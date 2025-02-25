 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes, ConstraintKinds
  #-} 

{- This module uses quickceck to generate tests for the BenOr protocol in BenOr.hs
   The testing here tries to be as agnostic as possible and makes use of different adversarial
   scheduling strategies inclduing censoring communication between pairs of parties, random delivery   of messages on a per-round or complete random basis.
-}

module CheckBenOr where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import BenOr
import TestTools

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Data (toConstr, Data)
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List ((\\), elemIndex, delete, tails)
import Test.QuickCheck
import Test.QuickCheck.Monadic 
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data BenOrCmd = CmdBenOrP2F PID Bool | CmdOne SID PID Int Bool MulticastTokens | CmdTwo SID PID Int MulticastTokens | CmdTwoD SID PID Int Bool MulticastTokens deriving (Show, Eq, Read)

type BenOrInput = (BenOrCmd, Tokens)
type BenOrConfig = (SID, [PID], CruptList, Int)

{-  set of party outputs from transcript (pid, decision) -}
getOutputs :: (MonadIO m) => BenOrTranscript -> m (Set (PID, Bool))
getOutputs tr = do
  s <- newIORef Set.empty
  forMseq_ tr $ \t -> do
    case t of
      Right (pid, BenOrF2P_Deliver m) -> modifyIORef s $ Set.insert (pid,m)
      _ -> return ()
  readIORef s

{- numebr of parties that output a decision -}
numOutputs :: (MonadIO m) => BenOrTranscript -> m Int
numOutputs tr = do
  s <- getOutputs tr
  return (Set.size s)

{- number of different values parties output -}
retValues :: (MonadIO m) => BenOrTranscript -> m Int
retValues tr = do
  s <- getOutputs tr
  n <- newIORef Set.empty
  forMseq_ (Set.toList s) $ \(p,o) -> modifyIORef n $ Set.insert o
  readIORef n >>= return . Set.size

-- generate messages of a specific type
benOrOneMsg :: (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen BenOrInput
benOrOneMsg ssid parties inputs round dts = do
  shuffle parties >>= \pl -> oneof inputs >>= \i -> (choose (0, 999999) :: Gen Int) >>= \sid -> return (CmdOne (ssid (show sid)) (pl !! 0) round i dts, 0)

benOrTwoMsg :: (String -> SID) -> [PID] -> Int -> Int -> Gen BenOrInput
benOrTwoMsg ssid parties round dts = do
  shuffle parties >>= \pl -> (choose (0, 999999) :: Gen Int) >>= \sid -> return (CmdTwo (ssid (show sid)) (pl !! 0) round dts, 0)

benOrTwoDMsg :: (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen BenOrInput
benOrTwoDMsg ssid parties inputs round dts =
  shuffle parties >>= \pl -> oneof inputs >>= \i -> (choose (0, 999999) :: Gen Int) >>= \sid -> return (CmdTwoD (ssid (show sid)) (pl !! 0) round i dts, 0)

-- When testing liveness in the optimistic case we're lookin for protocol design errors
-- and we want to ensure that all messages are delivered. Failures in liveness here indicate
-- problems even in the crash fault setting. The only difference in this generator is that it
-- creates no DELIVER messages for the runqueue.
benOrGeneratorOnlyMsgs :: Int -> Int -> (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [BenOrInput]
benOrGeneratorOnlyMsgs n numQueue ssid parties inputs round dts = frequency $
  [ (1, return []), 
    (5, if n==0 then return [] else (:) <$> (benOrOneMsg ssid parties inputs round dts) <*> (benOrGeneratorOnlyMsgs (n-1) numQueue ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> (benOrTwoMsg ssid parties round dts) <*> (benOrGeneratorOnlyMsgs (n-1) numQueue ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> (benOrTwoDMsg ssid parties inputs round dts) <*> (benOrGeneratorOnlyMsgs (n-1) numQueue ssid parties inputs round dts))
  ]

-- TODO: here the integer here is the round number. Therefore we need to parameterize this with a range or rounds. Maybe this way we an see if it reaches consensus or there's a better way to give round numbers and iteratively increase the possible round numbers. 

{- In BenOr the ssids only need to be difference because the round number isn't encoded in them.
  therefore we can jut generate random ssid numbers for each message without caring too much about it -}
benOrGenerator :: Int -> Int -> (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [Either BenOrInput AsyncInput]
benOrGenerator n numQueue ssid parties inputs round dts = frequency $
    [ (1, return []), 
      (10, if n==0 then return []
           else if numQueue==0 then (benOrGenerator n 0 ssid parties inputs round dts)
           else (:) <$> (choose (0,numQueue-1) >>= \i -> return (Right (CmdDeliver i, 0))) <*> (benOrGenerator (n-1) (numQueue-1) ssid parties inputs round dts)),
      (5, if n==0 then return [] else (:) <$> ((benOrOneMsg ssid parties inputs round dts) >>= return . Left) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)),
      (5, if n==0 then return [] else (:) <$> ((benOrTwoMsg ssid parties round dts) >>= return . Left) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)),
      (5, if n==0 then return [] else (:) <$> ((benOrTwoDMsg ssid parties inputs round dts) >>= return . Left) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts))
    ]


  
-- Takes in a BenOrCmd and executes it by writing the actual message on the channel
-- makes it easy to create an environment that takes in a tape of commands and executes
-- them all 
envExecBenOrCmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F BenOrP2F), CarryTokens Int))) ->
  (Chan ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) (Either _ (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int)) ->
  (Chan ()) -> BenOrInput -> m () 
envExecBenOrCmd z2p z2a pump cmd = do
  case cmd of
      ((CmdBenOrP2F pid' x'), st') -> do
          writeChan z2p $ (pid', ((ClockP2F_Through $ BenOrP2F_Input x'), SendTokens st'))
          readChan pump
      ((CmdOne ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (One r' x'), DeliverTokensWithMessage 0))), SendTokens st')
          readChan pump
      ((CmdTwo ssid' pid' r' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (Two r'), DeliverTokensWithMessage 0))), SendTokens st')
          readChan pump
      ((CmdTwoD ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (TwoD r' x'), DeliverTokensWithMessage 0))), SendTokens st')
          readChan pump

performBenOrEnv 
  :: (MonadEnvironment m) => 
  BenOrConfig -> [Either BenOrInput AsyncInput] ->
  (Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) BenOrTranscript m)
performBenOrEnv benOrConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int) = benOrConfig 
    writeChan z2exec $ SttCrupt_SidCrupt sid crupt

    (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
        
    () <- readChan pump 
  
    --writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
    --readChan clockChan
    let n = length parties

    forMseq_ cmdList $ \cmd -> do 
        envExecCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd
    writeChan outp =<< readIORef transcript


-- The purpose of this generator is to test whether asynchrnous conditions and byzantine adversaries
-- can cause parties to decide on different values. The environment:
-- * stays within the n/5 corruption bound
-- * gives each honest party a random one of [True, False]
-- * delivers only subsets of messages in the runqueue rather than all of them
-- * generates byzantine messages to send to everyone
-- 
-- The expectation of such a generator is that not every run will result in more than 1
-- party deciding on any value. As such properties that use this generator should use 
--     pre $ (Set.size o > 1)
-- to toss out uninteresting cases and subsequently assert
--     assert (Set.size o == 5)
benOrEnvRandomRounds
  :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript) m
benOrEnvRandomRounds parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  --let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  --let crupt = "Alice" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  
  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  
  
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  c <- envQueueSize z2a clockChan 1000
  
  let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  -- HONEST INPUT --
  forMseq_ (honest) $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdBenOrP2F h x, inputTokens)])
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    readChan pump

  -- generate a censor list 
  someHonest <- liftIO $ generate $ elements honest
  censorPairs <- liftIO $ generate $ shuffle [(x,y) | (x:ys) <- tails honest, y <- ys, x == someHonest || y == someHonest] 

  -- Make the protocol run --
  firstInp <- newIORef []
  forMseq_ [1..50] $ \r -> do
    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
    c <- envQueueSize z2a clockChan 0

    forMseq_ crupts $ \cpid -> do
      -- ADV INPUT with only some delivers (not all messages) --
      forMseq_ [1..10] $ \idx -> do
        rprime <- liftIO $ generate $ elements [r-2,r-1,r,r+1,r+2]
        inps <- liftIO $ generate $ benOrGeneratorOnlyMsgs 1 c (multicastSid sssid cpid parties) ["Dave"] inputs rprime inputTokens

        -- EXEC ADV INPUT --
        forMseq_ inps $ \i -> do
          modifyIORef cmdList $ (++ [Left i])
          envExecBenOrCmd z2p z2a pump i

    -- execute some subset of the current set of honest party messages 
    -- c was assigned before any crupt messages were delivered

    f <- liftIO $ generate $ arbitrary `suchThat` (> 1)
    inps <- liftIO $ generate $ frequency [ (3, rqDeliverChoice c f), (1, rqDeliverAll c) ]
    forMseq_ inps $ \inp -> do
      modifyIORef cmdList $ (++ [Right (inp,0)])
      deliverer censorPairs inp

    -- sometimes deliver all the messages between the censored parties
    b :: Int <- liftIO $ generate $ choose (1,5) 
    if b < 3 then do
      () <- deliverByPairs censorPairs
      return ()
    else return ()
    return ()
  
  tr <- readIORef transcript
  cl <- readIORef cmdList

  liftIO $ putStrLn $ "\n\t someHonest: " ++ show censorPairs
  liftIO $ putStrLn $ "\t pairs: " ++ show censorPairs
  
  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr)

-- A property that asserts safety holds
propBenOrSafety one two dec stat rnd = monadicIO $ do
    forAllM (readableParties 10 15) $ \ps -> do
      let t = (length ps `div` 5) - 1
      forAllM (cruptFrom ps t) $ \cc -> do
        let parties = ps
        let prot () = protBenOrBreak one two dec 0 stat rnd
        let crupt = cc
        (config', c', t', inps, tape, outputRounds) <- run $ runITMinIO 120 $ execUC 
          (benOrEnvByPartition parties crupt 1000)
          (runAsyncP $ prot ()) 
          (runAsyncF $ bangFAsync fMulticastToken) 
          dummyAdversaryToken
        --printYellow ("[Config]\n\n" ++ show config')
        --printYellow ("[Inputs]\n\n" ++ show c')
        n <- retValues t' 
        pre $ n > 0
        --printYellow (show tape)
        printYellow (show outputRounds)
        --assert False
        let maxRound = foldr1 (\x y -> if x >= y then x else y) $ map snd $ Map.toList outputRounds
        let minRound = foldr1 (\x y -> if x <= y then x else y) $ map snd $ Map.toList outputRounds
        assert $ (maxRound - minRound) <= 1
        --assert $ n < 2

benOrEnvTest
  :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript) m
benOrEnvTest parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  
  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  
  
  (deliverer, deliverByPairs, getByPairs, getBySenders, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  c <- envQueueSize z2a clockChan 1000
  
  let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  let pidsT = ["Alice", "Bob", "Charlie"]
  let pidsF = ["Dave", "Eve"]
  forMseq_ pidsT $ \p -> do
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens 1000))
    readChan pump

  forMseq_ pidsF $ \p -> do
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens 1000))
    readChan pump

  forMseq_ [1..10] $ \r -> do
     
    let sssid = multicastSid sssid "Frank" parties ("one" ++ show r)
    writeChan z2a $ asyncA2PMs "Frank" (
    

  -- generate a censor list 
  someHonest <- liftIO $ generate $ elements honest
  censorPairs <- liftIO $ generate $ shuffle [(x,y) | (x:ys) <- tails honest, y <- ys, x == someHonest || y == someHonest] 

  -- Make the protocol run --
  firstInp <- newIORef []
  forMseq_ [1..50] $ \r -> do
    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
    c <- envQueueSize z2a clockChan 0

    forMseq_ crupts $ \cpid -> do
      -- ADV INPUT with only some delivers (not all messages) --
      forMseq_ [1..10] $ \idx -> do
        rprime <- liftIO $ generate $ arbitrary
        inps <- liftIO $ generate $ benOrGeneratorOnlyMsgs 1 c (multicastSid sssid cpid parties) ["Dave"] inputs rprime inputTokens

        -- EXEC ADV INPUT --
        forMseq_ inps $ \i -> do
          modifyIORef cmdList $ (++ [Left i])
          envExecBenOrCmd z2p z2a pump i

    -- execute some subset of the current set of honest party messages 
    -- c was assigned before any crupt messages were delivered

    f <- liftIO $ generate $ arbitrary `suchThat` (> 1)
    inps <- liftIO $ generate $ frequency [ (3, rqDeliverChoice c f), (1, rqDeliverAll c) ]
    forMseq_ inps $ \inp -> do
      modifyIORef cmdList $ (++ [Right (inp,0)])
      deliverer censorPairs inp

    -- sometimes deliver all the messages between the censored parties
    b :: Int <- liftIO $ generate $ choose (1,5) 
    if b < 3 then do
      () <- deliverByPairs censorPairs
      return ()
    else return ()
    return ()
  
  tr <- readIORef transcript
  cl <- readIORef cmdList

  liftIO $ putStrLn $ "\n\t someHonest: " ++ show censorPairs
  liftIO $ putStrLn $ "\t pairs: " ++ show censorPairs
  
  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr)

benOrEnvTrackDecideRound :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool, [[Char]], Map PID Int) m
benOrEnvTrackDecideRound parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  let t = ((length parties) `div` 5) - 1
  let honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
  yprint ("Honest: " ++ show honest)
  yprint ("Crupt: " ++ show crupts)
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z

  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  

  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  let allOnes r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let allTwos r = getByFilter (2,r,False)
  let allTwoDs r = do getByFilter (3,r,True) >>= \x -> getByFilter (3,r,False) >>= \y -> return (x ++ y)
  let oneTrue r = do getByFilter (1,r,True)
  let oneFalse r = do getByFilter (1,r,False)
  let twoTrue r = do getByFilter (2,r,True)
  let twoFalse r = do getByFilter (2,r,False)
  let twoDTrue r = do getByFilter (3,r,True)
  let twoDFalse r = do getByFilter (3,r,False)
  let doDelivers ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd 
  let getOneByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let getTwoByArb r = do
            idxs <- getByFilter (2,r,False)
            return idxs
  let getTwoDByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (3,r,whichInp)
            return (whichInp, idxs)

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  c <- envQueueSize z2a clockChan 1000
  
  --let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  actionTape <- newIORef []
  let takeAction s = do modifyIORef actionTape (++ [s])

  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT
  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    takeAction (show p ++ " input " ++ show i)
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input i), SendTokens inputTokens))
    readChan pump

  checkChan <- newChan
  doneCheckChan <- newChan
  partyOutputRounds <- newIORef (Map.empty :: Map PID Int)
  -- track decision round
  fork $ forever $ do
    () <- readChan checkChan
    -- if there is a decide, the last out is always 
    lo <- readIORef lastOut
    case lo of
      Just (Right (pid, BenOrF2P_Deliver b)) -> do
        exists <- readIORef partyOutputRounds >>= return . (Map.member pid)
        if not exists then do
          -- get leaks
          leaks <- getLeaks
          lastRound <- newIORef 0
          -- search for last round number in messages sent by pid
          forMseq_ leaks $ \l -> do
            let (sid :: SID, ((bm :: BenOrMsg, DeliverTokensWithMessage st), SendTokens a)) = l
            let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "" $ snd sid
            let r' = if pidS == pid then
                       case bm of
                         One r b -> (r-1)
                         Two r -> (r-1)
                         TwoD r b -> (r-1)
                     else 0
            writeIORef lastRound r'
          readIORef lastRound >>= modifyIORef partyOutputRounds . Map.insert pid
        else return () 
      Just _ -> return ()
      Nothing -> return ()
    writeChan doneCheckChan ()
  
  let doDeliversWithCheck ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
              writeChan checkChan ()
              readChan doneCheckChan
 
  let rounds = 5 
  forMseq_ [1..rounds] $ \r -> do
    -- deliver all Ones in some random order
    ones <- shuffleM (allOnes r)
    doDelivers ones

    -- deliver all Two
    twos <- shuffleM $ concatM [(allTwos r), (allTwoDs r)]
    doDeliversWithCheck twos

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ac <- readIORef actionTape
  po <- readIORef partyOutputRounds

  writeChan outp ((sid, parties, (Map.empty), t), cl, tr, inputM, ac, po)
            


-- a theorem of the paper is that:
--    * if some part decides in round r all others decide in the next round
--    * if all parties propose the same value, they all decide in round 1
propBenOrFinishNextRound one two dec stat rnd = monadicIO $ do
  forAllM (readableParties 10 15) $ \parties -> do
    let t = (length parties `div` 5) - 1
    forAllM (cruptFrom parties t) $ \crupt -> do
      let prot () = protBenOrBreak one two dec 0 stat rnd
      (config', c', t', inps, tape, outputRounds) <- run $ runITMinIO 120 $ execUC
        (benOrEnvTrackDecideRound parties crupt 1000)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastToken)
        dummyAdversaryToken
      n <- retValues t' 
      pre $ n > 0
      --printYellow (show tape)
      printYellow (show outputRounds)
      assert False
      assert $ n < 2

propBenOrFinishNextRoundCCC = propBenOrFinishNextRound BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect CorrectState BenOrCheckRounds_Check
    

-- Here we create properties that run the BenOr protocol with different variants of
-- the threshold parameters the protocol uses. We expect CCC (all correct) never results
-- in safety violations where as certain combinations of small values can violate safety.
propBenOrSafetyCCC = propBenOrSafety BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect CorrectState BenOrCheckRounds_Check
propBenOrSafetyCCS = propBenOrSafety BenOrOneCorrect BenOrTwoDCorrect BenOrDecideSmall   CorrectState BenOrCheckRounds_Check
propBenOrSafetyCSC = propBenOrSafety BenOrOneCorrect BenOrTwoDSmall BenOrDecideCorrect   CorrectState BenOrCheckRounds_Check
propBenOrSafetyCSS = propBenOrSafety BenOrOneCorrect BenOrTwoDSmall BenOrDecideSmall     CorrectState BenOrCheckRounds_Check
propBenOrSafetySCC = propBenOrSafety BenOrOneSmall BenOrTwoDCorrect BenOrDecideCorrect   CorrectState BenOrCheckRounds_Check
propBenOrSafetySCS = propBenOrSafety BenOrOneSmall BenOrTwoDCorrect BenOrDecideSmall     CorrectState BenOrCheckRounds_Check
propBenOrSafetySSC = propBenOrSafety BenOrOneSmall BenOrTwoDSmall BenOrDecideCorrect     CorrectState BenOrCheckRounds_Check
propBenOrSafetySSS = propBenOrSafety BenOrOneSmall BenOrTwoDSmall BenOrDecideSmall       NoState BenOrCheckRounds_Check


-- This environment does cause a safety violation with ONLY threshold perturbations
-- It is more involved in that it separates messages out.
-- TODO: can we make this a smaller environment?
benOrEnvByPartition
  :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool, [[Char]], Map PID Int) m
benOrEnvByPartition parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  let t = ((length parties) `div` 5) - 1
  let honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
  yprint ("Honest: " ++ show honest)
  yprint ("Crupt: " ++ show crupts)
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z

  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  

  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  let allOnes r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let allTwos r = getByFilter (2,r,False)
  let allTwoDs r = do getByFilter (3,r,True) >>= \x -> getByFilter (3,r,False) >>= \y -> return (x ++ y)
  let oneTrue r = do getByFilter (1,r,True)
  let oneFalse r = do getByFilter (1,r,False)
  let twoTrue r = do getByFilter (2,r,True)
  let twoFalse r = do getByFilter (2,r,False)
  let twoDTrue r = do getByFilter (3,r,True)
  let twoDFalse r = do getByFilter (3,r,False)
  let doDelivers ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd 
  let getOneByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let getTwoByArb r = do
            idxs <- getByFilter (2,r,False)
            return idxs
  let getTwoDByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (3,r,whichInp)
            return (whichInp, idxs)

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  c <- envQueueSize z2a clockChan 1000
  
  --let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  actionTape <- newIORef []
  let takeAction s = do modifyIORef actionTape (++ [s])

  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT
  
  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    takeAction (show p ++ " input " ++ show i)
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input i), SendTokens inputTokens))
    readChan pump
  
  checkChan <- newChan
  doneCheckChan <- newChan
  partyOutputRounds <- newIORef (Map.empty :: Map PID Int)
  -- track decision round
  fork $ forever $ do
    () <- readChan checkChan
    -- if there is a decide, the last out is always 
    lo <- readIORef lastOut
    case lo of
      Just (Right (pid, BenOrF2P_Deliver b)) -> do
        exists <- readIORef partyOutputRounds >>= return . (Map.member pid)
        if not exists then do
          -- get leaks
          leaks <- getLeaks
          lastRound <- newIORef 0
          -- search for last round number in messages sent by pid
          forMseq_ leaks $ \l -> do
            let (sid :: SID, ((bm :: BenOrMsg, DeliverTokensWithMessage st), SendTokens a)) = l
            let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "" $ snd sid
            let r' = if pidS == pid then
                       case bm of
                         One r b -> (r-1)
                         Two r -> (r-1)
                         TwoD r b -> (r-1)
                     else 0
            writeIORef lastRound r'
          readIORef lastRound >>= modifyIORef partyOutputRounds . Map.insert pid
        else return () 
      Just _ -> return ()
      Nothing -> return ()
    writeChan doneCheckChan ()
  
  let doDeliversWithCheck ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
              writeChan checkChan ()
              readChan doneCheckChan

  let doCmdsWithCheck cmds = do
      forMseq_ cmds $ \cmd -> do
        envExecCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd 
        writeChan checkChan ()
        readChan doneCheckChan

  let rounds = 15
  forMseq_ [1..rounds] $ \r -> do
    yprint ("\t\t\t round: " ++ show r ++ " giving ones by partition")
    -- give ones by partition
    takeAction ("intersectM (oneTrue " ++ show r ++ ") (getByReceivers pidsT)")
    takeAction ("intersectM (oneFalse " ++ show r ++ ") (getByReceivers pidsF)")
    oneToT <- intersectM (oneTrue r) (getByReceivers pidsT)
    oneToF <- intersectM (oneFalse r) (getByReceivers pidsF)
    doDelivers $ oneToT ++ oneToF

    -- deliver more 1's for some partition with random values
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      (b', ones) <- getOneByArb r
      takeAction ("Party " ++ show p ++ ": (" ++ show b' ++ ", ones) <- getOneByArb " ++ show r)
      doDelivers (intersect ones forp)

    -- send adv 1's with random T/F
    cinps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      someInput <- generateM arbitrary
      cinp <- generateM $ vectorOf 5 $ benOrOneMsg (multicastSid sssid cpid parties) honest [return someInput] r inputTokens  
      forMseq_ cinp $ takeAction . show
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    doCmds cinpCmds

    yprint ("\tt give the rest of the 1s")
    -- deliver the rest of the 1 messages in this round
    finalSet <- allOnes r
    takeAction ("allOnes " ++ show r)
    doDelivers finalSet

    yprint ("\t\t deliver 2's by partition")

      -- deliver 2's by partition
    test <- twoTrue r
    if test /= [] then error "there should be no (2,r,True)"
    else return ()
    twoToT <- intersectM (twoTrue r) (getByReceivers pidsT)
    takeAction ("intersectM (twoTrue " ++ show r ++ ") (getByReceivers pidsT)")
    takeAction ("intersectM (twoDTrue " ++ show r ++ ") (getByReceivers pidsT)")
    takeAction ("intersectM (twoFalse " ++ show r ++ ") (getByReceivers pidsF)")
    takeAction ("intersectM (twoDFalse " ++ show r ++ ") (getByReceivers pidsF)")
    twoDToT <- intersectM (twoDTrue r) (getByReceivers pidsT)
    twoToF <- intersectM (twoFalse r) (getByReceivers pidsF)  
    twoDToF <- intersectM (twoDFalse r) (getByReceivers pidsF)
    doDeliversWithCheck $ twoToT ++ twoDToT ++ twoToF ++ twoDToF 

    -- adv 2 messages 
    cinps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- generateM $ vectorOf 5 $ benOrTwoMsg (multicastSid sssid cpid parties) honest r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
      forMseq_ cinp $ takeAction . show
    cinpCmds <- readIORef cinps
    doCmdsWithCheck cinpCmds

    -- adv 2D messages with arbitrary T/F
    cinps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      someInput <- generateM arbitrary
      cinp <- generateM $ vectorOf 5 $ benOrTwoDMsg (multicastSid sssid cpid parties) honest [return someInput] r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
      forMseq_ cinp $ takeAction . show
    cinpCmds <- readIORef cinps
    doCmdsWithCheck cinpCmds
 
    -- some subset gets all the 2's for them
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      twos <- getTwoByArb r
      (b', twoDs) <- getTwoDByArb r
      takeAction ("Party " ++ show p ++ "(" ++ show b' ++ ", twoDs) <- getTwoDByArb " ++ show r)
      doDeliversWithCheck (intersect (twos ++ twoDs) forp)

    yprint ("\t\t deliver rest of the pending")
    
    b <- ?getBit
    if b then do 
      -- deliver rest of 2's and 2D's
      finalSet <- concatM [allTwos r, allTwoDs r]
      takeAction ("concatM [allTwos " ++ show r ++ ", allTwoDs " ++ show r ++ "]")
      doDeliversWithCheck finalSet 
      -- all messages of this round should have been delivered by now
    else return ()
 
  tr <- readIORef transcript
  cl <- readIORef cmdList
  ac <- readIORef actionTape
  po <- readIORef partyOutputRounds

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ac, po)


benOrEnvAllHonestShuffle
  :: (MonadEnvironment m) => Int -> [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool, [[Char]], Int) m
benOrEnvAllHonestShuffle rounds parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  let t = ((length parties) `div` 5) - 1
  let honest = parties
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
  yprint ("Honest: " ++ show honest)
  yprint ("Crupt: " ++ show crupts)
 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.empty)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z

  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  

  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  let allOnes r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let allTwos r = getByFilter (2,r,False)
  let allTwoDs r = do getByFilter (3,r,True) >>= \x -> getByFilter (3,r,False) >>= \y -> return (x ++ y)
  let oneTrue r = do getByFilter (1,r,True)
  let oneFalse r = do getByFilter (1,r,False)
  let twoTrue r = do getByFilter (2,r,True)
  let twoFalse r = do getByFilter (2,r,False)
  let twoDTrue r = do getByFilter (3,r,True)
  let twoDFalse r = do getByFilter (3,r,False)
  let doDelivers ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd 
  let getOneByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let getTwoByArb r = do
            idxs <- getByFilter (2,r,False)
            return idxs
  let getTwoDByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (3,r,whichInp)
            return (whichInp, idxs)

  () <- readChan pump

  c <- envQueueSize z2a clockChan 1000
  modifyIORef cmdList $ (++ [Right (CmdGetCount, 1000)])
  
  --let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  actionTape <- newIORef []
  let takeAction s = do modifyIORef actionTape (++ [s])

  -- all honest just shuffle messages, but in order they are expected
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT
  let pidsT = take 5 honest
  let pidsF = honest \\ pidsT 

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)
  numDecided <- newIORef 0

  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    takeAction (show p ++ " input " ++ show i)
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input i), SendTokens inputTokens))
    readChan pump
    modifyIORef cmdList $ (++ [Left ((CmdBenOrP2F p i, inputTokens))])
  
  --let rounds = 5
  lastRound <- newIORef rounds
  forMseq_ [1..rounds] $ \r -> do
    --nd <- readIORef numDecided
    --if nd < (length honest) then do
    -- deliver all Ones in some random order
    ones <- shuffleM (allOnes r)
    doDelivers ones

    -- deliver all Two
    twos <- shuffleM $ concatM [(allTwos r), (allTwoDs r)]
    doDelivers twos

    --  -- check for outputs
    --  ls <- readIORef lastOut
    --  case ls of
    --    Just (Right (pid, BenOrF2P_Deliver m)) -> modifyIORef numDecided (+ 1)
    --    _ -> return ()
    --else do 
    --  writeIORef lastRound r 
    --  return ()
  tr <- readIORef transcript
  cl <- readIORef cmdList
  ac <- readIORef actionTape
  lr <- readIORef lastRound

  writeChan outp ((sid, parties, (Map.empty), t), cl, tr, inputM, ac, lr)

-- A property that asserts safety holds
{- 
  Tried with: 
    --  newRound being called early in isTimeToDecide but this only delays by one round so not a noticeable liveness problem becuase terminaton is still guaranteed
        got some differences but negligible.
-}
propBenOrSucceedRound one two decide' state' round' = monadicIO $ do
    forMseq_ [5,10,15,20] $ \r -> do
      parties <- generateM $ readableParties 10 10
      let t = (length parties `div` 5) - 1
      let crupt = []
      --let prot () = protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0 CorrectState BenOrCheckRounds_Check
      let prot () = protBenOrBreak one two decide' 0 state' round'
      (config', c', t', inps, tape, lastRound) <- run $ runITMinIO 120 $ execUC 
        (benOrEnvAllHonestShuffle r parties crupt 1000)
        (runAsyncP $ prot ()) 
        (runAsyncF $ bangFAsync fMulticastToken) 
        dummyAdversaryToken
      n <- numOutputs t'
      no <- retValues t'
      printYellow (show tape)
      assert $ no < 2
      monitor (collect (r, n))

propBenOrSafetyAllHonestCCC = propBenOrSucceedRound BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestCCS = propBenOrSucceedRound BenOrOneCorrect BenOrTwoDCorrect BenOrDecideSmall   CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestCSC = propBenOrSucceedRound BenOrOneCorrect BenOrTwoDSmall BenOrDecideCorrect   CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestCSS = propBenOrSucceedRound BenOrOneCorrect BenOrTwoDSmall BenOrDecideSmall     CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestSCC = propBenOrSucceedRound BenOrOneSmall BenOrTwoDCorrect BenOrDecideCorrect   CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestSCS = propBenOrSucceedRound BenOrOneSmall BenOrTwoDCorrect BenOrDecideSmall     CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestSSC = propBenOrSucceedRound BenOrOneSmall BenOrTwoDSmall BenOrDecideCorrect     CorrectState BenOrCheckRounds_Check
propBenOrSafetyAllHonestSSS = propBenOrSucceedRound BenOrOneSmall BenOrTwoDSmall BenOrDecideSmall       CorrectState BenOrCheckRounds_Check

{- Check when decisions are made -}
propBenOrAllHonestSuccess = propBenOrSafetyAllHonestCCC

propBenOrSucceedRoundWithCrupt one two decide' state' round' = monadicIO $ do
    forMseq_ [5,10,15,20] $ \r -> do
      parties <- generateM $ readableParties 10 10
      let t = (length parties `div` 5) - 1
      let crupt = []
      --let prot () = protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0 CorrectState BenOrCheckRounds_Check
      let prot () = protBenOrBreak one two decide' 0 state' round'
      (config', c', t', inps, tape, lastRound) <- run $ runITMinIO 120 $ execUC 
        (benOrEnvAllHonestShuffle r parties crupt 1000)
        (runAsyncP $ prot ()) 
        (runAsyncF $ bangFAsync fMulticastToken) 
        dummyAdversaryToken
      n <- numOutputs t'
      no <- retValues t'
      printYellow (show tape)
      assert $ no < 2
      monitor (collect (r, n))


propBenOrSucceedSim = monadicIO $ do
    forMseq_ [5] $ \r -> do
      parties <- generateM $ readableParties 10 10
      let t = (length parties `div` 5) - 1
      let crupt = []
      let prot () = protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0 CorrectState BenOrCheckRounds_Check
      --(config', c', t', inps, tape, lastRound) <- run $ runITMinIO 120 $ execUC 
      (deets, decision) <- run $ runITMinIO 120 $ do
        ((config', c', t', inps, tape, lastRound), bits) <- runRandRecord $ execUC 
          (benOrEnvAllHonestShuffle r parties crupt 1000)
          (runAsyncP $ prot ()) 
          (runAsyncF $ bangFAsync fMulticastToken) 
          dummyAdversaryToken
        tI <- runRandReplay bits $ execUC
          (performBenOrEnv config' c')
          idealProtocolToken
          (runAsyncF fABA)
          (runTokenA $ simBenOr)
        let idx = compareTranscript t' tI
        let (agreement,split) = splitAt idx t'
        --liftIO $ putStrLn $ "treal: " ++ show  (take (idx+1) t')
        --liftIO $ putStrLn $ "tideal: " ++ show  (take (idx+1) tI)
        --liftIO $ putStrLn $ "Agreement: " ++ show agreement
        --liftIO $ putStrLn $ "split: " ++ show (take 1 split)
        return ((config', c', t', inps, tape, lastRound), t' == tI)
      assert decision

{- This enviroment is to determine another lemma: how many parties have to propose a value before no other value can be decided? -}


{- This enviroment is to determine another lemma: how many parties have to propose a value before no other value can be decided? -}
benOrEnvAllHonestTestOutcome
  :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool, [[Char]], Int) m
benOrEnvAllHonestTestOutcome pidsT pidsF rounds parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  let t = ((length parties) `div` 5) - 1
  let honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
  yprint ("Honest: " ++ show honest)
  yprint ("Crupt: " ++ show crupts)
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z

  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  

  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  let allOnes r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let allTwos r = getByFilter (2,r,False)
  let allTwoDs r = do getByFilter (3,r,True) >>= \x -> getByFilter (3,r,False) >>= \y -> return (x ++ y)
  let oneTrue r = do getByFilter (1,r,True)
  let oneFalse r = do getByFilter (1,r,False)
  let twoTrue r = do getByFilter (2,r,True)
  let twoFalse r = do getByFilter (2,r,False)
  let twoDTrue r = do getByFilter (3,r,True)
  let twoDFalse r = do getByFilter (3,r,False)
  let doDelivers ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd 
  let getOneByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let getTwoByArb r = do
            idxs <- getByFilter (2,r,False)
            return idxs
  let getTwoDByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (3,r,whichInp)
            return (whichInp, idxs)

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  c <- envQueueSize z2a clockChan 1000
  
  --let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  actionTape <- newIORef []
  let takeAction s = do modifyIORef actionTape (++ [s])

  -- all honest just shuffle messages, but in order they are expected
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT
 
  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)
  numDecided <- newIORef 0

  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    takeAction (show p ++ " input " ++ show i)
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input i), SendTokens inputTokens))
    readChan pump
  
  --let rounds = 5
  lastRound <- newIORef rounds
  forMseq_ [1..rounds] $ \r -> do
    nd <- readIORef numDecided
    if nd < (length honest) then do
      -- deliver all Ones in some random order
      ones <- shuffleM (allOnes r)
      doDelivers ones

      -- deliver all Two
      twos <- shuffleM $ concatM [(allTwos r), (allTwoDs r)]
      doDelivers twos

      -- check for outputs
      ls <- readIORef lastOut
      case ls of
        Just (Right (pid, BenOrF2P_Deliver m)) -> modifyIORef numDecided (+ 1)
        _ -> return ()
    else do 
      writeIORef lastRound r 
      return ()

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ac <- readIORef actionTape
  lr <- readIORef lastRound

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ac, lr)

propBenOrFindThreshold = monadicIO $ do
  parties <- generateM $ readableParties 10 10
  let t = 1
  assert $ ((length parties `div` 5) - 1) == t
  forMseq_ [5,6,7,8] $ \numT -> do
    let pidsT = take numT parties
    let pidsF = parties \\ pidsT
    let crupt = []
    let prot () = protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0 CorrectState BenOrCheckRounds_Check
    (config', c', t', inps, tape, lastRound) <- run $ runITMinIO 120 $ execUC 
      (benOrEnvAllHonestTestOutcome pidsT pidsF 15 parties crupt 1000)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    
    outputs <- newIORef Set.empty
    numOuts <- newIORef 0
    forMseq_ [0..(length t')-1] $ \i -> do
        case (t' !! i) of 
            Right (pid, BenOrF2P_Deliver m) -> do
                liftIO $ putStrLn $ "\n\t ############### GOT SOME output " ++ show (t' !! i) ++ "\n"
                modifyIORef outputs $ Set.insert m
                modifyIORef numOuts (+ 1)
            _ -> return ()
    o <- readIORef outputs
    n <- readIORef numOuts
    pre $ (Set.size o) > 0
    --printYellow (show tape)
    assert $ (Set.size o) < 2
    let decision = (Set.toList o) !! 0
    monitor (collect (numT, length pidsF, decision))
 
{- the problem with such tests may not be solvable. If we move to more structured environments, we're losing some of the "fuzzing" part of testing. It's hard to say that a very structured environment is catching aberrant situatins where liveness fails. It's unclear how exactly to proceed. -}
--prop_benOrComplete liveCoin = monadicIO $ do
--  --let prot () = protBenOr
--  let prot () = (protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect liveCoin CorrectState BenOrCheckRounds_Check)
--  forMseq_ [5, 10, 20] $ \r -> do
--    (config', inputs, t') <- run $ runITMinIO 120 $ execUC 
--      --(benOrEnvDeliverLoop 1000000)
--      (propUEnvBenOrCompletion 1000000 r)
--      (runAsyncP $ prot ()) 
--      (runAsyncF $ bangFAsync fMulticastToken) 
--      dummyAdversaryToken
-- 
--    finalRound <- newIORef 0
--    commitRound <- newIORef 0 
--    numOutputs <- newIORef 0
--    outputs <- newIORef Set.empty
--    forMseq_ t' $ \out -> do
--        case out of
--          Left (SttCruptA2Z_P2A (pid, (s, (MulticastF2P_Deliver m, stk)))) ->
--            case m of
--              One r b -> readIORef finalRound >>= writeIORef finalRound . max r
--              Two r -> readIORef finalRound >>= writeIORef finalRound . max r
--              TwoD r b -> readIORef finalRound >>= writeIORef finalRound . max r
--          Right (pid, BenOrF2P_Deliver m) -> do
--            readIORef finalRound >>= writeIORef commitRound  
--            modifyIORef numOutputs $ (+) 1
--            modifyIORef outputs $ Set.insert m
--          _ -> return ()
--
--    n <- readIORef numOutputs
--    o <- readIORef outputs
--    --assert (n==5)
--    pre $ (n > 3)
--    --assert ( (Set.size o) <= 1 )
--    --assertWith (n == 5) "didn't get full agreement"
--    --pre $ (n == 5)
--    --cover 100 (n == 5) "non-trivial" $ (1 == 1)
--
--    liftIO $ putStrLn $ "\n\n done \n\n"
--
--    cr <- readIORef commitRound
--    --monitor (collect cr)
--    monitor (collect (r,n))

--prot_atLeast100 liveCoin = do
--  let args = stdArgs{maxSuccess = 100} 
--  argsM <- newIORef (stdArgs{maxSuccess = 100})
--  finished <- newIORef False
--  totalTests <- newIORef 0
--  totalFails <- newIORef 0 
--  whileM_ (readIORef finished >>= return . not) $ do
--    args <- readIORef argsM
--    res <- liftIO $ quickCheckWithResult args $ prop_benOrComplete liveCoin 
--    --writeIORef finished True 
--    case res of
--      Success numTests _ _ _ _ _ -> do
--        modifyIORef totalTests $ (+) numTests
--      Failure numTests nD nS _ _ _ _ _ _ _ _ _ _ -> do
--        modifyIORef totalTests $ (+) (numTests+1)
--        modifyIORef totalFails $ (+) 1
--      _ -> error "tf"
--    tT <- readIORef totalTests
--    if tT >= 100 then do
--      liftIO $ putStrLn $ "over 100 tests" 
--      writeIORef finished True
--    else writeIORef argsM (stdArgs{maxSuccess = (100 - tT)})
--  
--  tT <- readIORef totalTests
--  tF <- readIORef totalFails
--  liftIO $ putStrLn $ "totalTests: " ++ show tT
--  liftIO $ putStrLn $ "totalFails: " ++ show tF
--  liftIO $ putStrLn $ "percentFail: " ++ show (((fromIntegral tF) / (fromIntegral tT))*100)


benOrEnvDeliverLoop
  :: (MonadEnvironment m) => Tokens ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, BenOrTranscript) m
benOrEnvDeliverLoop inputTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
{- The goal here is to have a crupt party to just observe how any rounds
    it takes for the protocol to terminte. We just look at the latest round
    received before all honest parties terminate.
  - OPTION 1: we can condition only on test cases where everyone terminates
              to observe only how many rounds it takes. -}
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  
  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 

  finalRound <- newIORef 0
  let lastRound ctr party = do
              t <- readIORef transcript
              forMseq_ (deleteNth 0 (reverse t)) $ \msg -> do
                case msg of
                  Left (SttCruptA2Z_P2A (pid, (s, (MulticastF2P_Deliver m, stk)))) -> 
                    case m of
                      One r b -> readIORef finalRound >>= writeIORef finalRound . max r
                      Two r -> readIORef finalRound >>= writeIORef finalRound . max r
                      TwoD r b -> readIORef finalRound >>= writeIORef finalRound . max r
                  _ -> return () 
  
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    --x <- liftIO $ generate chooseAny
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens inputTokens))
    readChan pump
    
  whileM_ (envCheckQueue z2a clockChan 0) $ do
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan
    idx <- liftIO $ generate $ choose (0,c-1)
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx)), SendTokens 0)
    readChan pump
  
  tr <- readIORef transcript 
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), tr)

-- the property for the above ^^^^^^^^^^^^ environment
propBenOrObserve = monadicIO $ do
  let prot () = protBenOr
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let crupts = ["Alice"]
  (config', inputs, t') <- run $ runITMinIO 120 $ execUC 
    --(benOrEnvDeliverLoop 1000000)
    (benOrEnvRandomRounds parties crupts 1000000)
    (runAsyncP $ prot ()) 
    (runAsyncF $ bangFAsync fMulticastToken) 
    dummyAdversaryToken
 
  finalRound <- newIORef 0
  commitRound <- newIORef 0 
  numOutputs <- newIORef 0
  forMseq_ t' $ \out -> do
      case out of
        Left (SttCruptA2Z_P2A (pid, (s, (MulticastF2P_Deliver m, stk)))) ->
          case m of
            One r b -> readIORef finalRound >>= writeIORef finalRound . max r
            Two r -> readIORef finalRound >>= writeIORef finalRound . max r
            TwoD r b -> readIORef finalRound >>= writeIORef finalRound . max r
        Right (pid, BenOrF2P_Deliver m) -> do
          readIORef finalRound >>= writeIORef commitRound  
          modifyIORef numOutputs $ (+) 1
        _ -> return ()

  n <- readIORef numOutputs
  --assert (n < 5)
  --assertWith (n == 5) "didn't get full agreement"
  pre $ (n == 5)
  --cover 100 (n == 5) "non-trivial" $ (1 == 1)
  cr <- readIORef commitRound
  monitor (collect cr)


-- ==== (DEPRECATED) the environment below and it's property are no longer used ==== --
{- this environment generator is quite structured towards the BenOr protocol where
   where inputs are given, some messages are delivered thenmessages are sent by corrupt parties
   according to where they are expected by the protocl. 
   The next steps are:
    1. Create a generic environment that is agnostic to the protocol and takes in 
      some type of corrut party messages, some type of honest party messages,
      and randomly chooses from them. Run until interesting things happen. 
      First check how often something interesting happens.
    2. create a grammar for correlating state/output to the possible inputs, both
      corrupt and honest, that the environment can give.
-}
propEnvBenOrLiveness
  :: (MonadEnvironment m) => Tokens ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript) m
propEnvBenOrLiveness inputTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])

  -- compute ssids
  --let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  --let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  --let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))
  
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z

  counter <- newIORef 0
  let multicastSid c ps p = (show c, show (p, ps, ""))

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  --let inputTokens = 64

  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    () <- readChan pump
    modifyIORef cmdList $ (++) [Left $ (CmdBenOrP2F h x, inputTokens)]

  -- send out adversary One messages  
  -- send a message TO ALL HONEST PARTIES
  --let cruptssid = multicastSid sssid crupt parties "1"
  ctr <- readIORef counter
  modifyIORef counter $ (+) 1
  let cruptssid = multicastSid ctr "Alice" parties
  forMseq_ honest $ \hp -> do
    -- choose a bit
    x <- liftIO $ generate chooseAny
    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (cruptssid, (MulticastA2F_Deliver hp (One 1 x), DeliverTokensWithMessage 0))), SendTokens 0)
    () <- readChan pump 
    modifyIORef cmdList $ (++) [Left (CmdOne cruptssid hp 1 x 0, 0)]

  -- do some series of make progresses and delivers
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  -- send out adversary Two messages  
  --let cruptssid = multicastSid sssid crupt parties "2"
  forMseq_ honest $ \hp -> do
    -- choose a bit
    x :: Bool <- liftIO $ generate chooseAny
    b :: Bool <- liftIO $ generate chooseAny
    if b then do
      writeChan z2a $ ((SttCruptZ2A_A2F $ Right (cruptssid, (MulticastA2F_Deliver hp (Two 1), DeliverTokensWithMessage 0))), SendTokens 0)
      modifyIORef cmdList $ (++) [Left (CmdTwo cruptssid hp 1 0, 0)]
    else do
      writeChan z2a $ ((SttCruptZ2A_A2F $ Right (cruptssid, (MulticastA2F_Deliver hp (TwoD 1 x), DeliverTokensWithMessage 0))), SendTokens 0)
      modifyIORef cmdList $ (++) [Left (CmdTwoD cruptssid hp 1 x 0, 0)]
    () <- readChan pump 
    return ()

  -- do some series of make progresses and delivers
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList
 
  -- deliver the rest 
  getCmdChan <- newChan
  () <- envDeliverAll clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
  c <- readChan clockChan
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
 
  if (c /= 0) then error " stil not done wtf "
  else return ()

  tr <- readIORef transcript
  cl <- readIORef cmdList
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), reverse cl, tr)

-- ==== (DEPRECATED) the property below and it's environment above are no longer used ==== --
-- runs tests on the real world protocol only
-- no simulation checking
-- this test runs the Liveness environment with some x import tokens
-- and the test "fails" when import is exhausted and no value has been decided
-- by any party
prop_benOrLiveness = monadicIO $ do
    let prot () = protBenOr
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      (propEnvBenOrLiveness 64)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    outputs <- newIORef Set.empty
    forMseq_ t' $ \out -> do
        case out of 
            Right (pid, BenOrF2P_Deliver m) -> do
                modifyIORef outputs $ Set.insert m
            _ -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')

  -- asserting size is 0 check causes test to fail when some party
  -- has decided a value (the point being to check how common it is
  -- for all parties to decide something
  -- assert ( (Set.size o) == 0 )
    monitor (collect (Set.size o))

{- This property shows how `collect` is used to report, at the end of the test, reports statistics
    about the number of parties that decided some value over the 100 test cases. This property
    doesn't test anything. The point here is to use thie  -}
prop_benOrCollectDecisions ns = monadicIO $ do
  let prot () = protBenOr
  forMseq_ ns $ \imp -> do
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      (propEnvBenOrLiveness imp)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    
    numOutputs <- newIORef 0
    forMseq_ [0..(length t')-1] $ \i -> do
        case (t' !! i) of 
            Right (pid, BenOrF2P_Deliver m) -> do
                modifyIORef numOutputs $ (+) 1
            _ -> return ()

    n <- readIORef numOutputs
    monitor (collect (imp, n))

propEnvBenOrAllHonest
  :: (MonadEnvironment m) =>
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript) m
propEnvBenOrAllHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let honest = parties
  let sssid = "sidTestBenOr"
  let sid = (sssid, show (parties, t, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  let inputTokens = 64
  
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  liftIO $ putStrLn $ "Honest: " ++ show honest
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    () <- readChan pump
    modifyIORef cmdList $ (++) [Left $ (CmdBenOrP2F h x, inputTokens)]
  
  -- deliver all the ones scheduled form the above inputs
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  -- deliver all the twos
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
  c <- readChan clockChan
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
 
  if (c /= 0) then error " stil not done wtf "
  else return ()

  tr <- readIORef transcript
  cl <- readIORef cmdList

  writeChan outp ((sid, parties, Map.empty, t), reverse cl, tr)
  
-- runs tests on the real world protocol only
-- no simulation checking
prop_benOrAllHonest= monadicIO $ do
    let prot () = protBenOr
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      propEnvBenOrAllHonest
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t')-1] $ \i -> do
        case (t' !! i) of 
            Right (pid, BenOrF2P_Deliver m) -> do
                liftIO $ putStrLn $ "\n\t ############### GOT SOME output " ++ show (t' !! i) ++ "\n"
                modifyIORef outputs $ Set.insert m
            Right _ -> return ()
            Left m -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')
    assert ( (Set.size o) == 0 )


type MonadBenOrEnvironment m =
  (MonadEnvironment m,
    ?parties :: [PID],
    ?cruptMapList :: [(PID,())],
    ?crupts :: [PID],
    ?sssid :: String,
    ?t :: Int,
    ?sid :: SID,
    ?yprint :: [Char] -> m (),
    ?importAmt :: Int,
    ?cmdList :: IORef [Either BenOrInput AsyncInput],
    ?honest :: [PID],
    ?lastOut :: (IORef (Maybe (Either (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) (SID, (MulticastF2A BenOrMsg, TransferTokens Int)))) (PID, BenOrF2P)))),
    ?transcript :: IORef BenOrTranscript,
    ?clockChan :: Chan Int,
    ?deliverer :: [(PID,PID)] -> AsyncCmd -> m (),
    ?deliverByPairs :: [(PID,PID)] -> m (),
    ?getByPairs :: (PID,PID) -> m [Int],
    ?getBySender :: PID -> m [Int],
    ?getByReceivers :: [PID] -> m [Int],
    ?getByFilter :: (Int,Int,Bool) -> m [Int],
    ?getLeaks :: m [(SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))],
    ?allOnes :: Int -> m [Int],
    ?allTwos :: Int -> m [Int],
    ?allTwoDs :: Int -> m [Int],
    ?oneTrue :: Int -> m [Int],
    ?oneFalse :: Int -> m [Int],
    ?twoTrue :: Int -> m [Int],
    ?twoFalse :: Int -> m [Int],
    ?twoDTrue :: Int -> m [Int],
    ?twoDFalse :: Int -> m [Int],
    ?doDelivers :: [Int] -> m (),
    ?doCmds :: [(Either BenOrInput AsyncInput)] -> m (),
    ?getOneByArb :: Int -> m (Bool, [Int]),
    ?getTwoByArb :: Int -> m [Int],
    ?getTwoDByArb :: Int -> m (Bool, [Int]))


runBenOrEnvironment :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  (MonadBenOrEnvironment m => Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool) m) -> 
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool) m
runBenOrEnvironment parties crupts importAmt z z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  --let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let _t = 1 :: Int
  --let crupt = "Alice" :: PID
  let _honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, _t, ""))
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  cmdList <- newIORef []  
  (_lastOut, _transcript, _clockChan, _leakLimited) <- envReadOut p2z a2z

  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  

  (_deliverer, _deliverByPairs, _getByPairs, _getBySender, _getByReceivers, _getByFilter, _getLeaks) <- envMapQueue z2a a2z _clockChan _lastOut pump valueFilter cmdList


  let _allOnes r = do _getByFilter (1,r,True) >>= \x -> _getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let _allTwos r = _getByFilter (2,r,False)
  let _allTwoDs r = do _getByFilter (3,r,True) >>= \x -> _getByFilter (3,r,False) >>= \y -> return (x ++ y)
  let _oneTrue r = do _getByFilter (1,r,True)
  let _oneFalse r = do _getByFilter (1,r,False)
  let _twoTrue r = do _getByFilter (2,r,True)
  let _twoFalse r = do _getByFilter (2,r,False)
  let _twoDTrue r = do _getByFilter (3,r,True)
  let _twoDFalse r = do _getByFilter (3,r,False)
  let _doDelivers ds = do
            forMseq_ (deliverListAll ds) $ \i -> do
              _deliverer [] i
  let _doCmds cmds = do
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f _clockChan pump cmd envExecBenOrCmd 
  let _getOneByArb r = do
            whichInp <- generateM arbitrary
            idxs <- _getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let _getTwoByArb r = do
            idxs <- _getByFilter (2,r,False)
            return idxs
  let _getTwoDByArb r = do
            whichInp <- generateM arbitrary
            idxs <- _getByFilter (3,r,whichInp)
            return (whichInp, idxs)

  () <- readChan pump
 
  let ?parties = parties
      ?cruptMapList = cruptMapList
      ?crupts = crupts
      ?sssid = sssid
      ?t = _t
      ?sid = sid
      ?yprint = yprint
      ?importAmt = importAmt
      ?cmdList = cmdList
      ?honest = _honest
      ?lastOut = _lastOut
      ?transcript = _transcript
      ?clockChan = _clockChan
      ?deliverer = _deliverer
      ?deliverByPairs = _deliverByPairs
      ?getByPairs = _getByPairs
      ?getBySender = _getBySender
      ?getByReceivers = _getByReceivers
      ?getByFilter = _getByFilter
      ?getLeaks = _getLeaks
      ?allOnes = _allOnes
      ?allTwos = _allTwos
      ?allTwoDs = _allTwoDs
      ?oneTrue = _oneTrue
      ?oneFalse = _oneFalse
      ?twoTrue = _twoTrue
      ?twoFalse = _twoFalse
      ?twoDTrue = _twoDTrue
      ?twoDFalse = _twoDFalse
      ?doDelivers = _doDelivers
      ?doCmds = _doCmds
      ?getOneByArb = _getOneByArb
      ?getTwoByArb = _getTwoByArb
      ?getTwoDByArb = _getTwoDByArb in   
              z z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp

propTestAbstraction
  :: (MonadBenOrEnvironment m) => 
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], BenOrTranscript, Map PID Bool) m
propTestAbstraction z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  c <- envQueueSize z2a ?clockChan 1000
  
  --let inputs = do [return True, return False]
 
  let inputTokens = ?importAmt

  pidsT <- selectPIDs ?honest
  let pidsF = ?honest \\ pidsT
  --let pidsT = ["B", "C", "D", "E"]
  --let pidsF = ["F", "G", "H", "I", "J"]
 
  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input i), SendTokens inputTokens))
    readChan pump

  -- partition 1 messages by input
  c <- envQueueSize z2a ?clockChan 0
 
  let rounds = 5
  forMseq_ [1..rounds] $ \r -> do
    ?yprint ("\t\t\t round: " ++ show r ++ " giving ones by partition")
    -- give ones by partition
    oneToT <- intersectM (?oneTrue r) (?getByReceivers pidsT)
    oneToF <- intersectM (?oneFalse r) (?getByReceivers pidsF)
    ?doDelivers $ oneToT ++ oneToF

    -- deliver more 1's for some partition with random values
    partition <- selectPIDs ?honest
    forMseq_ partition $ \p -> do
      forp <- ?getByReceivers [p]
      (b', ones) <- ?getOneByArb r
      liftIO $ putStrLn $ "\t\t\t\t deliver " ++ show ones ++ " to " ++ show p
      ?doDelivers (intersect ones forp)

    -- send adv 1's
    cinps <- newIORef []
    forMseq_ ?crupts $ \cpid -> do
      someInput <- generateM arbitrary
      cinp <- generateM $ vectorOf 5 $ benOrOneMsg (multicastSid ?sssid cpid ?parties) ?honest [return someInput] r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    ?doCmds cinpCmds

    ?yprint ("\tt give the rest of the 1s")
    finalSet <- ?allOnes r
    ?doDelivers finalSet

    ?yprint ("\t\t deliver 2's by partition")

      -- deliver 2's by partition
    twoToT <- intersectM (?twoTrue r) (?getByReceivers pidsT)
    twoDToT <- intersectM (?twoDTrue r) (?getByReceivers pidsT)
    twoToF <- intersectM (?twoFalse r) (?getByReceivers pidsF)  
    twoDToF <- intersectM (?twoDFalse r) (?getByReceivers pidsF)
    liftIO $ putStrLn $ "\t\t\t\t delver 2's " ++ show (twoToT ++ twoDToT ++ twoToF ++ twoDToF)
    ?doDelivers $ twoToT ++ twoDToT ++ twoToF ++ twoDToF 

    -- adv 2's or 2D's   
    cinps <- newIORef []
    forMseq_ ?crupts $ \cpid -> do
      cinp <- generateM $ vectorOf 5 $ benOrTwoMsg (multicastSid ?sssid cpid ?parties) ?honest r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    ?doCmds cinpCmds

    -- adv 2's or 2D's   
    cinps <- newIORef []
    forMseq_ ?crupts $ \cpid -> do
      someInput <- generateM arbitrary
      cinp <- generateM $ vectorOf 5 $ benOrTwoDMsg (multicastSid ?sssid cpid ?parties) ?honest [return someInput] r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    ?doCmds cinpCmds
 
    -- select somesubset other twos 
    partition <- selectPIDs ?honest
    forMseq_ partition $ \p -> do
      forp <- ?getByReceivers [p]
      twos <- ?getTwoByArb r
      (b', twoDs) <- ?getTwoDByArb r
      ?doDelivers (intersect (twos ++ twoDs) forp)

    ?yprint ("\t\t deliver rest of the pending")

    -- deliver rest of 2's and 2D's and 1's
    --finalSet <- intersectM (allOnes r) (intersectM (allTwos r) (allTwoDs r))
    --finalSet <- shuffleAllM [allOnes r, allTwos r, allTwoDs r]
    --finalSet <- concatM [allOnes r, allTwos r, allTwoDs r]
    finalSet <- concatM [?allTwos r, ?allTwoDs r]
    ?doDelivers finalSet 
 
  tr <- readIORef ?transcript
  cl <- readIORef ?cmdList

  writeChan outp ((?sid, ?parties, (Map.fromList ?cruptMapList), ?t), cl, tr, inputM)

prop_uBenOrTestAbstract one two dec stat rnd = monadicIO $ do
    forAllM ( suchThat (partiesBetween 10 15) nonZeroParties) $ \ps -> do
      let t = length ps `div` 5
      forAllM (cruptFrom ps t) $ \cc -> do
        let parties = ps
        let prot () = protBenOrBreak one two dec 0 stat rnd
        let crupt = cc
        (config', c', t', inps) <- run $ runITMinIO 120 $ execUC 
          (runBenOrEnvironment parties crupt 1000 propTestAbstraction)
          (runAsyncP $ prot ()) 
          (runAsyncF $ bangFAsync fMulticastToken) 
          dummyAdversaryToken
        outputs <- newIORef Set.empty
        forMseq_ [0..(length t')-1] $ \i -> do
            case (t' !! i) of 
                Right (pid, BenOrF2P_Deliver m) -> do
                    liftIO $ putStrLn $ "\n\t ############### GOT SOME output " ++ show (t' !! i) ++ "\n"
                    modifyIORef outputs $ Set.insert m
                _ -> return ()
        o <- readIORef outputs
        --printYellow ("[Config]\n\n" ++ show config')
        --printYellow ("[Inputs]\n\n" ++ show c')
        pre $ (Set.size o) > 0
        assert $ (Set.size o) < 2

prop_partitionCCC = prop_uBenOrTestAbstract BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect CorrectState BenOrCheckRounds_Check
prop_partitionSSS = prop_uBenOrTestAbstract BenOrOneSmall BenOrTwoDSmall BenOrDecideSmall CorrectState BenOrCheckRounds_Check

