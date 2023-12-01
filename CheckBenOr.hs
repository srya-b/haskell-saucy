 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
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

-- TODO: here the integer here is the round number. Therefore we need to parameterize this with a range or rounds. Maybe this way we an see if it reaches consensus or there's a better way to give round numbers and iteratively increase the possible round numbers. 

{- In BenOr the ssids only need to be difference because the round number isn't encoded in them.
  therefore we can jut generate random ssid numbers for each message without caring too much about it -}
benOrGenerator :: Int -> Int -> (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [Either BenOrInput AsyncInput]
benOrGenerator n numQueue ssid parties inputs round dts = frequency $
    [ (1, return []), 
      (10, if n==0 then return []
           else if numQueue==0 then (benOrGenerator n 0 ssid parties inputs round dts)
           else (:) <$> (choose (0,numQueue-1) >>= \i -> return (Right (CmdDeliver i, 0))) <*> (benOrGenerator (n-1) (numQueue-1) ssid parties inputs round dts)),
      (5, if n==0 then return [] else (:) <$> 
          ((shuffle parties) >>= (\party -> oneof inputs >>= (\inp -> (choose (0, 999999) :: Gen Int) >>= (\sid -> 
            return (Left (CmdOne (ssid (show sid)) (party !! 0) round inp dts, 0)))))) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)),
      (5, if n==0 then return [] else (:) <$>
          ((shuffle parties) >>= (\party -> (choose (0, 999999) :: Gen Int) >>= (\sid -> 
            return (Left (CmdTwo (ssid (show sid)) (party !! 0) round 0, 0))))) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)),
      (5, if n==0 then return [] else (:) <$>
          ((shuffle parties) >>= (\party -> oneof inputs >>= (\inp -> (choose (0, 999999) :: Gen Int) >>= (\sid -> 
            return (Left (CmdTwoD (ssid (show sid)) (party !! 0) round inp 0, 0)))))) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)) 
    ]

benOrOneMsg :: (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen BenOrInput
benOrOneMsg ssid parties inputs round dts = do
  shuffle parties >>= \pl -> oneof inputs >>= \i -> (choose (0, 999999) :: Gen Int) >>= \sid -> return (CmdOne (ssid (show sid)) (pl !! 0) round i dts, 0)

benOrTwoMsg :: (String -> SID) -> [PID] -> Int -> Int -> Gen BenOrInput
benOrTwoMsg ssid parties round dts = do
  shuffle parties >>= \pl -> (choose (0, 999999) :: Gen Int) >>= \sid -> return (CmdTwo (ssid (show sid)) (pl !! 0) round dts, 0)

benOrTwoDMsg :: (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen BenOrInput
benOrTwoDMsg ssid parties inputs round dts =
  shuffle parties >>= \pl -> oneof inputs >>= \i -> (choose (0, 999999) :: Gen Int) >>= \sid -> return (CmdTwoD (ssid (show sid)) (pl !! 0) round i dts, 0)
  
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
          writeChan z2p $ (pid', ((ClockP2F_Through $ BenOrP2F_Input x'), SendTokens 32))
          readChan pump
      ((CmdOne ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (One r' x'), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      ((CmdTwo ssid' pid' r' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (Two r'), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      ((CmdTwoD ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (TwoD r' x'), DeliverTokensWithMessage 0))), SendTokens 0)
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
     (ClockZ2F) Transcript m)
performBenOrEnv benOrConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int) = benOrConfig 
    writeChan z2exec $ SttCrupt_SidCrupt sid crupt

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z
        
    () <- readChan pump 
  
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
    readChan clockChan
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
propUEnvBenOrSafety
  :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
propUEnvBenOrSafety parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  
  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  
  --(deliverer,deliverByPairs,getByPairs,getBySender,getByReceiver) <- envMapQueue z2a a2z clockChan lastOut pump 
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  c <- envQueueSize z2a clockChan 1000
  
  let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  
  -- HONEST INPUT --
  --subHonest <- liftIO $ generate $ sublistOf honest
  --forMseq_ (subHonest) $ \h -> do
  forMseq_ (honest) $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdBenOrP2F h x, inputTokens)])
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    readChan pump

  liftIO $ putStrLn $ "\n honest input done \n" 
  
  -- generate a censor list 
  --someHonest <- liftIO $ generate $ elements honest
  --censorPairs <- liftIO $ generate $ shuffle [(x,y) | (x:ys) <- tails honest, y <- ys, x == someHonest || y == someHonest] 
  let censorPairs = [("Bob","Bob"), ("Carol","Carol"), ("Dave","Dave"), ("Eve","Eve"), ("Frank","Frank")]
  --let censorPairs = take 1 pairsOfPIDs

  -- Make the protocol run --
  firstInp <- newIORef []
  forMseq_ [1..50] $ \r -> do
    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
    c <- envQueueSize z2a clockChan 0

    forMseq_ crupts $ \cpid -> do
      -- ADV INPUT with only some delivers (not all messages) --
      --inps <- liftIO $ generate $ benOrGeneratorOnlyMsgs 30 c (multicastSid sssid cpid parties) ["Bob"] inputs r inputTokens
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
    --inps <- liftIO $ generate $ rqDeliverAll c
    forMseq_ inps $ \inp -> do
      modifyIORef cmdList $ (++ [Right (inp,0)])
      --envExecAsyncCmd z2p z2a z2f clockChan pump (inp,0)
      deliverer censorPairs inp

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
prop_uBenOrSafety one two dec = monadicIO $ do
    forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
      let t = length ps `div` 5
      forAllM (cruptFrom ps t) $ \cc -> do
        --let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
        let parties = ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J"]
        let prot () = protBenOrBreak one two dec 0
        let crupt = ["A"]
    -- TODO: commented generation of parties to test a simple aspect of the protocol
    --parties <- liftIO $ (generate arbitrary :: IO [PID])
    --crupt <- liftIO $ (generate $ sublistOf parties) >>= return . take (length parties `div` 5)
        --let crupt = cc
        --let parties = ps
        --pre $ length parties > 5
        --pre $ length parties > (5 * length crupt)
        --crupt <- liftIO $ generate $ sublistOf parties
        (config', c', t', inps) <- run $ runITMinIO 120 $ execUC 
          (propUEnvBenOrPartition parties crupt 64)
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

-- Here we create properties that run the BenOr protocol with different variants of
-- the threshold parameters the protocol uses. We expect CCC (all correct) never results
-- in safety violations where as certain combinations of small values can violate safety.
prop_uBenOrSafetyCCC = prop_uBenOrSafety BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect
prop_uBenOrSafetyCCS = prop_uBenOrSafety BenOrOneCorrect BenOrTwoDCorrect BenOrDecideSmall
prop_uBenOrSafetyCSC = prop_uBenOrSafety BenOrOneCorrect BenOrTwoDSmall BenOrDecideCorrect
prop_uBenOrSafetyCSS = prop_uBenOrSafety BenOrOneCorrect BenOrTwoDSmall BenOrDecideSmall
prop_uBenOrSafetySCC = prop_uBenOrSafety BenOrOneSmall BenOrTwoDCorrect BenOrDecideCorrect
prop_uBenOrSafetySCS = prop_uBenOrSafety BenOrOneSmall BenOrTwoDCorrect BenOrDecideSmall
prop_uBenOrSafetySSC = prop_uBenOrSafety BenOrOneSmall BenOrTwoDSmall BenOrDecideCorrect
prop_uBenOrSafetySSS = prop_uBenOrSafety BenOrOneSmall BenOrTwoDSmall BenOrDecideSmall

propUEnvBenOrPartition
  :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript, Map PID Bool) m
propUEnvBenOrPartition parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  liftIO $ putStrLn $ "Parties: " ++ show parties 
  liftIO $ putStrLn $ "Crupt: " ++ show crupts
  --let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  --let crupt = "Alice" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
 
  let cruptMapList = map (\x -> (x,())) crupts
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList cruptMapList)
  
  cmdList <- newIORef []  
  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  let valueFilter msg = case msg of
                          One r b -> (1,r,b)
                          Two r -> (2,r,False)
                          TwoD r b -> (3,r,b)  

  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter

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

  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT
  let pidsT = ["B", "C", "D", "E"]
  let pidsF = ["F", "G", "H", "I", "J"]
 
  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through $ BenOrP2F_Input i), SendTokens inputTokens))
    readChan pump

  -- partition 1 messages by input
  c <- envQueueSize z2a clockChan 0
  --oneToT <- intersectM (oneTrue 1) (getByReceivers pidsT)
  --oneToF <- intersectM (oneFalse 1) (getByReceivers pidsF)
  --doDelivers $ oneToT ++ oneToF

  --yprint "\t\t\t\t T shoul have 4 and F should have 5"

  --forMseq_ pidsT $ \p -> do
  --  oneFtoP <- intersectM (oneFalse 1) (getByReceivers [p])
  --  doDelivers $ take 3 oneFtoP
  --  forMseq_ crupts $ \cpid -> do
  --    cinp <- generateM $ vectorOf 5 $ benOrOneMsg (multicastSid sssid cpid parties) [p] [return True] 1 inputTokens  
  --    doCmds (map Left cinp)

  ---- adv (1,1,T) to pidsT

  --forMseq_ pidsF $ \p -> do
  --  oneTtoP <- intersectM (oneTrue 1) (getByReceivers [p])
  --  doDelivers $ take 3 oneTtoP

  --yprint "they should all be expecting 2 messages"

  --twoDToT <- intersectM (twoDTrue 1) (getByReceivers pidsT)
  --twoDToF <- intersectM (twoDFalse 1) (getByReceivers pidsF)
  --doDelivers $ twoDToT ++ twoDToF

  --yprint "\t\t\t\t\t T shoud have 4 and F should have 5"  
 
  --forMseq_ pidsT $ \p -> do
  --  twoFtoP <- intersectM (twoDFalse 1) (getByReceivers [p])
  --  doDelivers $ take 3 twoFtoP
  --  forMseq_ crupts $ \cpid -> do
  --    cinp <- generateM $ vectorOf 5 $ benOrTwoDMsg (multicastSid sssid cpid parties) [p] [return True] 1 inputTokens  
  --    doCmds (map Left cinp)

  --forMseq_ pidsF $ \p -> do
  --  twoTtoP <- intersectM (twoDTrue 1) (getByReceivers [p])
  --  doDelivers $ take 3 twoTtoP
  
--------------
 
  let rounds = 5
  forMseq_ [1..rounds] $ \r -> do
    yprint ("\t\t\t round: " ++ show r ++ " giving ones by partition")
    -- give ones by partition
    oneToT <- intersectM (oneTrue r) (getByReceivers pidsT)
    oneToF <- intersectM (oneFalse r) (getByReceivers pidsF)
    doDelivers $ oneToT ++ oneToF

    -- deliver more 1's for some partition with random values
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      (b', ones) <- getOneByArb r
      liftIO $ putStrLn $ "\t\t\t\t deliver " ++ show ones ++ " to " ++ show p
      doDelivers (intersect ones forp)

    -- send adv 1's
    cinps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      someInput <- generateM arbitrary
      cinp <- generateM $ vectorOf 5 $ benOrOneMsg (multicastSid sssid cpid parties) honest [return someInput] r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    doCmds cinpCmds

    yprint ("\tt give the rest of the 1s")
    finalSet <- allOnes r
    doDelivers finalSet

    yprint ("\t\t deliver 2's by partition")

      -- deliver 2's by partition
    twoToT <- intersectM (twoTrue r) (getByReceivers pidsT)
    twoDToT <- intersectM (twoDTrue r) (getByReceivers pidsT)
    twoToF <- intersectM (twoFalse r) (getByReceivers pidsF)  
    twoDToF <- intersectM (twoDFalse r) (getByReceivers pidsF)
    liftIO $ putStrLn $ "\t\t\t\t delver 2's " ++ show (twoToT ++ twoDToT ++ twoToF ++ twoDToF)
    doDelivers $ twoToT ++ twoDToT ++ twoToF ++ twoDToF 

    -- adv 2's or 2D's   
    cinps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- generateM $ vectorOf 5 $ benOrTwoMsg (multicastSid sssid cpid parties) honest r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    doCmds cinpCmds

    -- adv 2's or 2D's   
    cinps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      someInput <- generateM arbitrary
      cinp <- generateM $ vectorOf 5 $ benOrTwoDMsg (multicastSid sssid cpid parties) honest [return someInput] r inputTokens  
      modifyIORef cinps $ (++ (map Left cinp))
    cinpCmds <- readIORef cinps
    doCmds cinpCmds
 
    -- select somesubset other twos 
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      twos <- getTwoByArb r
      (b', twoDs) <- getTwoDByArb r
      doDelivers (intersect (twos ++ twoDs) forp)

    yprint ("\t\t deliver rest of the pending")

    -- deliver rest of 2's and 2D's and 1's
    --finalSet <- intersectM (allOnes r) (intersectM (allTwos r) (allTwoDs r))
    --finalSet <- shuffleAllM [allOnes r, allTwos r, allTwoDs r]
    --finalSet <- concatM [allOnes r, allTwos r, allTwoDs r]
    finalSet <- concatM [allTwos r, allTwoDs r]
    doDelivers finalSet 
 
  tr <- readIORef transcript
  cl <- readIORef cmdList

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM)

-- When testing liveness in the optimistic case we're lookin for protocol design errors
-- and we want to ensure that all messages are delivered. Failures in liveness here indicate
-- problems even in the crash fault setting. The only difference in this generator is that it
-- creates no DELIVER messages for the runqueue.
benOrGeneratorOnlyMsgs :: Int -> Int -> (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [BenOrInput]
benOrGeneratorOnlyMsgs n numQueue ssid parties inputs round dts = frequency $
  [ (1, return []), 
    (5, if n==0 then return [] else (:) <$> 
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> (choose (0, 999999) :: Gen Int) >>=
              (\s -> return (CmdOne (ssid (show s)) (pl !! 0) round i dts, 0))))) <*> (benOrGeneratorOnlyMsgs (n-1) numQueue ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> (choose (0, 999999) :: Gen Int) >>=
              (\s -> return (CmdTwo (ssid (show s)) (pl !! 0) round 0, 0))))) <*> (benOrGeneratorOnlyMsgs (n-1) numQueue ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> (choose (0, 999999) :: Gen Int) >>=
              (\s -> return (CmdTwoD (ssid (show s)) (pl !! 0) round i 0, 0))))) <*> (benOrGeneratorOnlyMsgs (n-1) numQueue ssid parties inputs round dts)) 
  ]

-- We use the term Completion because we intend this environment to check optimistic liveness. 
-- Therefore this environment generator is created to ensure that a correct BenOr protocol always
-- results in all honest parties deciding some value (n==5). This environment:
-- * random inputs for honest parties
-- * delivers all messages from honest parties in a particular round
-- * doesn't inject byzantine messages
propUEnvBenOrCompletion
  :: (MonadEnvironment m) => Int -> Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
propUEnvBenOrCompletion importAmt rounds z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  --let crupt = "Alice" :: PID
  let honest = parties \\ ["Alice"]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Alice", ())])
  
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  
  let inputs = do [return True, return False]
 
  let inputTokens = importAmt
  -- Give somehonest parties some inputs
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdBenOrP2F h x, inputTokens)])
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    readChan pump

  -- go in some limited number of rounds    
  firstInp <- newIORef []
  forMseq_ [1..rounds] $ \r -> do
    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan 
    --inps <- liftIO $ generate $ benOrGenerator (max 20 c) c (multicastSid sssid crupt parties) parties inputs r 64
    
    inps <- liftIO $ generate $ benOrGeneratorOnlyMsgs 30 c (multicastSid sssid "Alice" parties) parties inputs r inputTokens

    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan 

    forMseq_ inps $ \i -> do
      modifyIORef cmdList $ (++ [Left i])
      envExecBenOrCmd z2p z2a pump (i)
    
    inps <- liftIO $ generate $ benOrGeneratorOnlyMsgs 30 c (multicastSid sssid "Bob" parties) parties inputs r inputTokens

    forMseq_ inps $ \i -> do
      --modifyIORef debugLog $ (++ [Left i])
      modifyIORef cmdList $ (++ [Left i])
      --envExecAsyncCmd z2p z2a z2f clockChan pump i envExecBenOrCmd
      envExecBenOrCmd z2p z2a pump i

    --inps <- liftIO $ generate $ rqDeliverAll c
    inps <- liftIO $ generate $ frequency [ (1, rqDeliverAll c), (20, rqDeliverChoice c 10) ]
    --inps <- liftIO $ generate $ frequency [ (1, return (map CmdDeliver [0..(c-1)])), (40, rqDeliverChoice c 1) ]
    forMseq_ inps $ \i -> do
      modifyIORef cmdList $ (++ [Right (i, 0)])
      envExecCmd z2p z2a z2f clockChan pump (Right (i,0)) envExecBenOrCmd 

  --c <- envQueueSize z2a clockChan 0
  --inps <- liftIO $ generate $ rqDeliverAll c
  --forMseq_ inps $ \i -> envExecCmd z2p z2a z2f clockChan pump (Right (i,0)) envExecBenOrCmd

  tr <- readIORef transcript
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, (Map.fromList [("Alice",()), ("Bob", ())]), t), cl, tr)

{- the problem with such tests may not be solvable. If we move to more structured environments, we're losing some of the "fuzzing" part of testing. It's hard to say that a very structured environment is catching aberrant situatins where liveness fails. It's unclear how exactly to proceed. -}
prop_benOrComplete liveCoin = monadicIO $ do
  --let prot () = protBenOr
  let prot () = (protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect liveCoin)
  forMseq_ [5, 10, 20] $ \r -> do
    (config', inputs, t') <- run $ runITMinIO 120 $ execUC 
      --(propEnvBenOrLivenessObserve 1000000)
      (propUEnvBenOrCompletion 1000000 r)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
 
    finalRound <- newIORef 0
    commitRound <- newIORef 0 
    numOutputs <- newIORef 0
    outputs <- newIORef Set.empty
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
            modifyIORef outputs $ Set.insert m
          _ -> return ()

    n <- readIORef numOutputs
    o <- readIORef outputs
    --assert (n==5)
    pre $ (n > 3)
    --assert ( (Set.size o) <= 1 )
    --assertWith (n == 5) "didn't get full agreement"
    --pre $ (n == 5)
    --cover 100 (n == 5) "non-trivial" $ (1 == 1)

    liftIO $ putStrLn $ "\n\n done \n\n"

    cr <- readIORef commitRound
    --monitor (collect cr)
    monitor (collect (r,n))

prot_atLeast100 liveCoin = do
  let args = stdArgs{maxSuccess = 100} 
  argsM <- newIORef (stdArgs{maxSuccess = 100})
  finished <- newIORef False
  totalTests <- newIORef 0
  totalFails <- newIORef 0 
  whileM_ (readIORef finished >>= return . not) $ do
    args <- readIORef argsM
    res <- liftIO $ quickCheckWithResult args $ prop_benOrComplete liveCoin 
    --writeIORef finished True 
    case res of
      Success numTests _ _ _ _ _ -> do
        modifyIORef totalTests $ (+) numTests
      Failure numTests nD nS _ _ _ _ _ _ _ _ _ _ -> do
        modifyIORef totalTests $ (+) (numTests+1)
        modifyIORef totalFails $ (+) 1
      _ -> error "tf"
    tT <- readIORef totalTests
    if tT >= 100 then do
      liftIO $ putStrLn $ "over 100 tests" 
      writeIORef finished True
    else writeIORef argsM (stdArgs{maxSuccess = (100 - tT)})
  
  tT <- readIORef totalTests
  tF <- readIORef totalFails
  liftIO $ putStrLn $ "totalTests: " ++ show tT
  liftIO $ putStrLn $ "totalFails: " ++ show tF
  liftIO $ putStrLn $ "percentFail: " ++ show (((fromIntegral tF) / (fromIntegral tT))*100)

{- 
  Propert compare structure agnostic of import 
-}
prop_uBenOrCompare = monadicIO $ do
  let prot () = protBenOr
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let crupts = ["Alice"]
  
  (config', c', t') <- run $ runITMinIO 120 $ execUC 
    (propUEnvBenOrSafety parties crupts 1000)
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
  monitor (collect n)

propEnvBenOrLivenessObserve
  :: (MonadEnvironment m) => Tokens ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, Transcript) m
propEnvBenOrLivenessObserve inputTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  
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
prop_benOrObserve = monadicIO $ do
  let prot () = protBenOr
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let crupts = ["Alice"]
  (config', inputs, t') <- run $ runITMinIO 120 $ execUC 
    --(propEnvBenOrLivenessObserve 1000000)
    (propUEnvBenOrSafety parties crupts 1000000)
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
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
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

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

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
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
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

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

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

--propUEnvParam
--  :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
--  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
--     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
--     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
--                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
--                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
--     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
--                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
--     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
--propUEnvParam parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
--  let extendRight conf = show ("", conf)
--  
--  --let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
--  let t = 1 :: Int
--  --let crupt = "Alice" :: PID
--  let honest = parties \\ crupts
--  let sssid = "sidTestACast"
--  let sid = (sssid, show (parties, t, ""))
--  
--  let cruptMap = Map.fromList $ map (\x -> (x,())) crupts 
--  --writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])
--  writeChan z2exec $ SttCrupt_SidCrupt sid cruptMap
--  
--  cmdList <- newIORef []  
--  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
--
--  () <- readChan pump
--  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
--  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
--  c <- readChan clockChan 
--  
--  let inputs = do [return True, return False]
-- 
--  let inputTokens = importAmt
--  
--  -- HONEST INPUT --
--  forMseq_ honest $ \h -> do
--    -- choose a boolean
--    x <- liftIO $ generate chooseAny
--    modifyIORef cmdList $ (++ [Left $ (CmdBenOrP2F h x, inputTokens)])
--    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
--    readChan pump
--
--  -- Make the protocol run --
--  firstInp <- newIORef []
--  forMseq_ [1..30] $ \r -> do
--    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
--    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
--    c <- readChan clockChan 
--
--    forMseq_ crupts $ \cpid -> do
--      -- ADV INPUT with only some delivers (not all messages) --
--      inps <- liftIO $ generate $ benOrGeneratorOnlyMsgs 30 c (multicastSid sssid cpid parties) parties inputs r inputTokens
--      -- EXEC ADV INPUT --
--      forMseq_ inps $ \i -> do
--        modifyIORef cmdList $ (++ [Left i])
--        envExecBenOrCmd z2p z2a pump (i)
--
--    inps <- liftIO $ generate $ rqDeliverAll c
--    forMseq_ inps $ \i -> do    
--      modifyIORef cmdList $ (++ [Right (i,0)])
--      envExecCmd z2p z2a z2f clockChan pump (Right (i,0)) envExecBenOrCmd
--
--  tr <- readIORef transcript
--  cl <- readIORef cmdList
--  
--  writeChan outp ((sid, parties, cruptMap, t), cl, tr)
--
---- A property that asserts safety holds
--prop_uParams one two dec = monadicIO $ do
--    let prot () = protBenOrBreak one two dec 0
--    let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
--    let crupts = ["Alice", "Bob", "Carol"]
--    (config', c', t') <- run $ runITMinIO 120 $ execUC 
--      (propUEnvParam parties crupts 64)
--      (runAsyncP $ prot ()) 
--      (runAsyncF $ bangFAsync fMulticastToken) 
--      dummyAdversaryToken
--    outputs <- newIORef Set.empty
--    forMseq_ [0..(length t')-1] $ \i -> do
--        case (t' !! i) of 
--            Right (pid, BenOrF2P_Deliver m) -> do
--                liftIO $ putStrLn $ "\n\t ############### GOT SOME output " ++ show (t' !! i) ++ "\n"
--                modifyIORef outputs $ Set.insert m
--            _ -> return ()
--    o <- readIORef outputs
--    --printYellow ("[Config]\n\n" ++ show config')
--    --printYellow ("[Inputs]\n\n" ++ show c')
--
--    --pre $ ((Set.size o) > 0)
--    --assert ( (Set.size o) <= 1 )
--    assert ( (Set.size o) == 0)
--
--prop_pp = prop_uParams BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect
