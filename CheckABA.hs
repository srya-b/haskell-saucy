 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

module CheckABA where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import SCCMulticast
import BrokenABA
import TestTools

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List ((\\), elemIndex, delete)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data ABACmd = CmdABAP2F PID Bool | CmdAux SID PID Int Bool MulticastTokens | CmdEst SID PID Int Bool MulticastTokens | CmdCoin SID Int deriving (Show, Eq, Read)

type ABAInput = (ABACmd, Tokens)
type ABAConfig = (SID, [PID], CruptList, Int)

makeSBCastSid :: [PID] -> PID -> Int -> Bool -> SID
makeSBCastSid ps p r b = (show ("sbcast", p, r, b), show (p, ps, ""))

makeMainSid :: [PID] -> PID -> Int -> Bool -> SID
makeMainSid ps p r w = (show ("maincast", p, r, w), show (p, ps, ""))

{- SIDs used in ABA
  -- the main thread has sidMain: relies on the sender pid, round r, candidate w
  -- the different sBCasts use their own ssid relies on: pid, round, bit  
        but this is only used for location the OK channel for sBCast, the
  the only info read in he reading loop is _round and _bit is used to route messages
  to sbcast, otherwise the main thread doesn't care what those values are as long as they can be parsed

  the loop only care about the pidS already a part of fMulticastTOken
-}
abaGenerator :: Int -> Int -> (Bool -> SID) -> (Bool -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [Either ABAInput AsyncInput]
abaGenerator n numQueue mainssid sbssid parties inputs round dts = frequency $
  [ (1, return []), 
    (10, if n==0 then return []
         else if numQueue==0 then (abaGenerator n 0 mainssid sbssid parties inputs round dts)
         else (:) <$> (choose (0,numQueue-1) >>= \i -> return (Right (CmdDeliver i, 0))) <*> (abaGenerator (n-1) (numQueue-1) mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>=
          (\pl -> oneof inputs >>=
            \i -> return (Left (CmdEst (sbssid i) (pl !! 0) round i dts, 0)))) <*> (abaGenerator (n-1) numQueue mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> 
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> return (Left (CmdAux (mainssid i) (pl !! 0) round i dts, 0))))) <*> (abaGenerator (n-1) numQueue mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> return (Left (CmdCoin (show ("sRO", round), show ("-1", parties,"")) round, 1)) <*> (abaGenerator (n-1) numQueue mainssid sbssid parties inputs round dts))
  ]

{- This generator only generates corrupt party messages, no Deliver or
MakeProgress messages like above. It generates at most `n` messages, with sid
`mainssid` for AUX messages and `sbssid` for EST messages. Every message
chooses a random PID out of `parties` and gives one of `inputs` for the
`round`. Finally it sends `dts` tokens. -}
abaGeneratorOnlyMsgs :: Int -> (Bool -> SID) -> (Bool -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [ABAInput]
abaGeneratorOnlyMsgs n mainssid sbssid parties inputs round dts = frequency $
  [ (1, return []), 
    (5, if n==0 then return [] else (:) <$> (abaEstMsg sbssid parties inputs round dts) <*> (abaGeneratorOnlyMsgs (n-1) mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> (abaAuxMsg mainssid parties inputs round dts) <*> (abaGeneratorOnlyMsgs (n-1) mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> return (CmdCoin (show ("sRO", round), show ("-1", parties,"")) round, 0) <*> (abaGeneratorOnlyMsgs (n-1) mainssid sbssid parties inputs round dts))
  ]

{- Generate a single EST message (see above for params) -}
abaEstMsg :: (Bool -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen ABAInput
abaEstMsg sbssid parties inputs round dts = do
  shuffle parties >>= \pl -> oneof inputs >>= \i -> return (CmdEst (sbssid i) (pl !! 0) round i dts, 0) 

{- Genrate a single AUX messages (previous comment for params -}
abaAuxMsg :: (Bool -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen ABAInput
abaAuxMsg mainssid parties inputs round dts = do
  shuffle parties >>= \pl -> oneof inputs >>= \i -> return (CmdAux (mainssid i) (pl !! 0) round i dts, 0)

-- TODO hard-coded 32 import
envExecABACmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F Bool), CarryTokens Int))) ->
  (Chan ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int))) (Either _ (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int)) ->
  (Chan ()) -> ABAInput -> m ()
envExecABACmd z2p z2a pump cmd = do
  case cmd of
      ((CmdABAP2F pid' x'), st') -> do
          writeChan z2p $ (pid', ((ClockP2F_Through $ x'), SendTokens st'))
          readChan pump
      ((CmdEst ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', ((CoinCastA2F_Deliver pid' (EST r' x', DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      ((CmdAux ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', ((CoinCastA2F_Deliver pid' (AUX r' x', DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      _ -> return ()
      --((CmdCoin ssid' r'), st') -> do
      --    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (CoinCastA2F_ro r', DeliverTokensWithMessage 1))), SendTokens 1)
      --    readChan pump

performABAEnv 
    :: (MonadEnvironment m) =>
    ABAConfig -> [Either ABAInput AsyncInput] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      --(Either ClockA2F (SID, (CoinCastA2F ABACast, CarryTokens Int)))), CarryTokens Int) Void
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) ABATranscript m
performABAEnv abaConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int) = abaConfig
  writeChan z2exec $ SttCrupt_SidCrupt sid crupt

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z  
  () <- readChan pump

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  readChan clockChan
  let n = length parties

  forMseq_ cmdList $ \cmd -> do
    envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  writeChan outp =<< readIORef transcript

data DeliveryTypeAll = AllRandom | ProtocolOrder | Sequential deriving (Show, Eq)

{- This environment is a simple check that the protocol works. It will always deliver all messages in a round and randomly choose honest party values -}
testEnvABADeliverAll
    :: (MonadEnvironment m) =>  Int -> [PID] -> [PID] -> Int -> DeliveryTypeAll ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript) m
testEnvABADeliverAll rounds parties crupts importAmt dtype z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  
  let t = 1 :: Int
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  

  let valueFilter msg = case msg of
                          EST r b -> (1,r,b)
                          AUX r b -> (2,r,b)
 
  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList

  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            --return (whichInp, idxs)
            return idxs
  let getAuxByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (r,r,whichInp)
            return (whichInp, idxs)
  

  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt
 
  let inputTokens = 10000
  -- Give somehonest parties random inputs
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdABAP2F h x, inputTokens)])
    writeChan z2p $ (h, ((ClockP2F_Through $ x), SendTokens inputTokens))
    readChan pump

  firstInp <- newIORef []
  forMseq_ [1..rounds] $ \r -> do 
    modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
    c <- envQueueSize z2a clockChan 0

    inps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinps <- liftIO $ generate $ abaGeneratorOnlyMsgs (max 10 c) (makeMainSid parties cpid r) (makeSBCastSid parties cpid r) parties inputs r 64
      modifyIORef inps (++ map Left cinps)
 
    dinps <- case dtype of
               -- randomize the queue and deliver 
               AllRandom -> generateM $ rqDeliverAll c
               Sequential -> rqDeliverAllSeq c
               ProtocolOrder -> do
                 ests :: [Int] <- allEsts r >>= generateM . shuffle
                 auxs :: [Int] <- allAuxs r >>= generateM . shuffle
                 return . deliverListAll $ (ests ++ auxs)
                 
    modifyIORef inps (++ map (\x -> Right (x,0)) dinps)
    execInps <- readIORef inps >>= (liftIO . generate . shuffle)
    forMseq_ execInps $ \i -> do
      envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

  tr <- readIORef transcript  
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, Map.fromList $ cruptMapList ++ [("-1",())], t), cl, tr)

prop_ABADeliverAllType dtype = monadicIO $ do
  let prot () = protABA
  let parties = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] :: [PID]
  let crupts = ["Bob"]
  (config', c', t') <- run $ runITMinIO 120 $ execUC
    (testEnvABADeliverAll 20 parties crupts 10000 dtype)
    (runAsyncP $ prot ())
    (runAsyncF $ bangFAsync fMulticastAndCoinToken)
    dummyAdversaryToken
  outputs <- newIORef Set.empty
  forMseq_ t' $ \outp -> do
    case outp of
      Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
        modifyIORef outputs $ Set.insert b
      Right _ -> return ()
      Left _ -> return ()
  o <- readIORef outputs

  pre $ (Set.size o) > 0
  assert $ (Set.size o) == 1

  printYellow ("[Config]\n\n" ++ show config')
  printYellow ("[Inputs]\n\n" ++ show c')

prop_ABADeliverAll = prop_ABADeliverAllType AllRandom 
prop_ABADeliverAllProtocol = prop_ABADeliverAllType ProtocolOrder
prop_ABADeliverAllSeq = prop_ABADeliverAllType Sequential

{- This environment paritions parties on input, starts the protocol by only giving each party EST of its
   own value, then in a loop gives some subset arbitrary EST values, and tries to force round progress by
   giving AUX messages to all.
  STEP: random honest input 
  STEP: give EST(v) by partition only
  STEP: give other EST to new PARTITION
  STEP: adv gives arbitrary EST messages to PARTITION of honest
  STEP: Give all aux to all + adv aux to HONEST
  STEP: deliver remaining EST of that round
-}
testUEnvABAPartition
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABAPartition parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let t = 1 :: Int
  --let crupt = "Bob" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  
  
  -- valueFilter :: ABACast -> (Int, Bool) 
  let valueFilter msg = case msg of
                          AUX r b -> (2,r,b)
                          EST r b -> (1,r,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            --return (whichInp, idxs)
            return idxs
  let getAuxByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (r,r,whichInp)
            return (whichInp, idxs)
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
   
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  -- STEP 1: choose honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  -- INIT: deliver ESTs + crupt by partition
  c <- envQueueSize z2a clockChan 0
  estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  estToF <- intersectM (estFalse 1) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  -- similar structure for all rounds
  let rounds = 4
  forMseq_ [1..rounds] $ \r -> do
    -- STEP: give some PARTITION more EST from other bools
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      --(b',ests) <- getEstByArb r
      ests <- getEstByArb r
      --arbEst <- intersectM (getByReceivers [p]) (getEstByArb r)
      --doDelivers arbEst
      doDelivers (intersect ests forp)
   
    -- STEP give only PARTITION crupt input of arbitrary input 
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid r) partition inputs r 64
      modifyIORef cinpsEsts $ (++  (map Left cinp))

    cinpCmds <- readIORef cinpsEsts 
    -- TODO: doesn't interleave adv input with delivery of EST
    ---- interleave then execute
    ----finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ estCmds)
    finalSet <- liftIO $ generate $ shuffle cinpCmds
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

    -- STEP give all to all AUX to make parties make progress
    yprint ("Giving all AUX to all AUX")
    auxs <- allAuxs r
    --doDelivers auxs 
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    -- STEP: deliver adv AUX and delivery shuffled
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll $ auxs)) -- ++ ests))
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd
    -- STEP: deliver remaining ESTs
    ests <- allEsts r
    doDelivers ests
    
    ---- deliver rest of round r messages
    yprint ("Giving rest of EST to all")
    yprint ("Looping environment")

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

-- This property runs the "correct" protocol and asserts that safety is achieved
-- and that the protocol should terminate with agreement
--prop_uABACompletion abaVariant bcastVariant svalVariant = monadicIO $ do
--  let prot () = protABABreak abaVariant bcastVariant svalVariant 
--  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
--    let t = length ps `div` 3
--    let crupts = []
--    (config', c', t') <- run $ runITMinIO 120 $ execUC
--      (testUEnvABACompletion ps crupts 100 10000)
--      (runAsyncP $ prot ())
--      (runAsyncF $ bangFAsync fMulticastAndCoinToken)
--      dummyAdversaryToken
--    outputs <- newIORef Set.empty
--    forMseq_ [0..(length t')-1] $ \i -> do
--      case (t' !! i) of
--        Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
--          modifyIORef outputs $ Set.insert b
--        Right _ -> return ()
--        Left _ -> return ()
--    o <- readIORef outputs
--
--    pre $ (Set.size o) > 0
--    assert $ (Set.size o) == 1
--
--    printYellow ("[Config]\n\n" ++ show config')
--    printYellow ("[Inputs]\n\n" ++ show c')

{- This environment paritions parties on input, starts the protocol by only giving each party EST of its
   own value, then in a loop gives some subset arbitrary EST values, and tries to force round progress by
   giving AUX messages to all. -}
-- TODO: Identical to the above environment, what's the point??????
testUEnvABAAdvEstAndAux
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABAAdvEstAndAux parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let t = 1 :: Int
  --let crupt = "Bob" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  
  
  -- valueFilter :: ABACast -> (Int, Bool) 
  let valueFilter msg = case msg of
                          AUX r b -> (2,r,b)
                          EST r b -> (1,r,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let getAuxByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (r,r,whichInp)
            return (whichInp, idxs)
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
   
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  -- STEP 1: choose honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  -- INIT: deliver ESTs + crupt by partition
  c <- envQueueSize z2a clockChan 0
  estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  estToF <- intersectM (estFalse 1) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  -- similar structure for all rounds
  let rounds = 4
  forMseq_ [1..rounds] $ \r -> do
    -- STEP: give some parties more EST messages to get different views
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      (b',ests) <- getEstByArb r
      --arbEst <- intersectM (getByReceivers [p]) (getEstByArb r)
      --doDelivers arbEst
      doDelivers (intersect ests forp)
   
    -- STEP give crupt input of arbitrary input 
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid r) partition inputs r 64
      modifyIORef cinpsEsts $ (++  (map Left cinp))

    cinpCmds <- readIORef cinpsEsts 
    ---- interleave then execute
    ----finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ estCmds)
    finalSet <- liftIO $ generate $ shuffle cinpCmds
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

    -- give AUX to make all parties progress to the next round
    yprint ("Giving all AUX to all AUX")
    auxs <- allAuxs r
    --doDelivers auxs 
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    ests <- allEsts r
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll $ auxs)) -- ++ ests))
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd
    doDelivers ests
    
    ---- deliver rest of round r messages
    yprint ("Giving rest of EST to all")
    yprint ("Looping environment")

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)


{- A Safety checker that accepts thresholds to change in the protocol. -}
prop_uABASafety abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug) 
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        --(testUEnvABAPartition ps cc 100 10000)
        (testUEnvABAAdvEstAndAux ps cc 100 1000)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastAndCoinToken)
        dummyAdversaryToken
      printYellow("Checking safety...")
      pre $ (numDecided t') > 1
      printYellow ("[Config]\n\n" ++ show config')
      --printYellow ("[Inputs]\n\n" ++ show c')
      printYellow ("[Intputs]\n" ++ show inps)
      assert $ (numDecisions t') == 1

{- different threshold setting (only 2 or 3^3=27 -}
prop_uABASafetyCCC = quickCheck $ prop_uABASafety ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct

{- FAIL: These all fail safety check -}
prop_uABASafetySSS = quickCheckWithResult stdArgs{maxSuccess = 1000}  $ prop_uABASafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any
prop_uABASafetySSC = quickCheck $ prop_uABASafety ABASmall SBcastSmall SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct
prop_uABASafetyCSS = quickCheck $ prop_uABASafety ABACorrect SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct
prop_uABASafetySCC = quickCheck $ prop_uABASafety ABASmall SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct


testUEnvABALemma17
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABALemma17 parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let t = 1 :: Int
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  
  
  -- valueFilter :: ABACast -> (Int, Bool) 
  let valueFilter msg = case msg of
                          AUX r b -> (2,r,b)
                          EST r b -> (1,r,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            return (whichInp, idxs)
  let getAuxByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (r,r,whichInp)
            return (whichInp, idxs)
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
   
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  -- STEP 1: choose honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  -- INIT: deliver ESTs + crupt by partition
  c <- envQueueSize z2a clockChan 0
  estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  estToF <- intersectM (estFalse 1) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  -- similar structure for all rounds
  forMseq_ [1..rounds] $ \r -> do
    -- STEP: give some parties more EST messages to get different views
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      (b',ests) <- getEstByArb r
      --arbEst <- intersectM (getByReceivers [p]) (getEstByArb r)
      --doDelivers arbEst
      doDelivers (intersect ests forp)
   
    -- STEP give crupt input of arbitrary input 
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid r) partition inputs r 64
      modifyIORef cinpsEsts $ (++  (map Left cinp))

    cinpCmds <- readIORef cinpsEsts 
    ---- interleave then execute
    ----finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ estCmds)
    finalSet <- liftIO $ generate $ shuffle cinpCmds
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

    -- give AUX to make all parties progress to the next round
    yprint ("Giving all AUX to all AUX")
    auxs <- allAuxs r
    --doDelivers auxs 
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    ests <- allEsts r
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll $ auxs)) -- ++ ests))
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd
    doDelivers ests
    
    ---- deliver rest of round r messages
    yprint ("Giving rest of EST to all")
    yprint ("Looping environment")

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

prop_ABALemma17 abaVariant bcastVariant svalVariant roundBug binPtr auxBug = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtr, auxBug) 
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        --(testUEnvABAPartition ps cc 100 10000)
        (testUEnvABALemma17 ps cc 4 1000)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastAndCoinToken)
        dummyAdversaryToken
      printYellow("Checking safety...")
      printYellow ("[Config]\n\n" ++ show config')
      --printYellow ("[Inputs]\n\n" ++ show c')
      printYellow ("[Intputs]\n" ++ show inps)

      supportCoinsTrueInRound <- newIORef (Map.empty :: Map Int Int)
      auxInR <- newIORef (Map.empty :: Map PID [Int])
      estInR <- newIORef (Map.empty :: Map PID [Int])
      lastAux <- newIORef (Map.empty :: Map PID Int)
      lastEst <- newIORef (Map.empty :: Map PID Int)
      whenDecide <- newIORef (Map.empty :: Map PID Int)
      lastRound <- newIORef 0
      let roundCoins = [False, True, True, False, False, True, False]
      let parties = ps
      let crupts = cc
      --forMseq_ (parties \\ crupts) $ \p -> do
      --  let ests = estP p . map parseLeak . justLeaks $ ll
      --  liftIO $ putStrLn $ "ests for " ++ show p ++ " " ++ show ests
      --  let auxs = auxP p . map parseLeak . justLeaks $ ll
      --  liftIO $ putStrLn $ "auxs for " ++ show p ++ " " ++ show auxs
      --  let dec = decideRound p 0 (betterLeaks ll)
      --  modifyIORef estInR $ Map.insert p ests
      --  modifyIORef auxInR $ Map.insert p auxs
      --  modifyIORef whenDecide $ Map.insert p dec

      --forMseq_ [2..4] $ \r -> do
      --  forMseq_ (parties \\ crupts) $ \p -> do
      --    ests <- (readIORef estInR >>= (return . filter (< r) . Map.findWithDefault [] p))
      --    auxs <- (readIORef auxInR >>= (return . filter (< r) . Map.findWithDefault [] p))
      --    if (elem (r-1) auxs) && not (elem r ests) then do
      --      modifyIORef supportCoinsTrueInRound (Map.insertWith (+) r 1)
      --    else return ()

      --scInR <- (readIORef supportCoinsTrueInRound >>= return . Map.assocs)
      --liftIO $ putStrLn $ "scInR " ++ show scInR
      --decisionRounds <- (readIORef whenDecide >>= return . Map.elems)
      failure <- newIORef False
      --forMseq_ scInR $ \(round, numsc) -> do
      --  if numsc == (length (parties \\ crupts)) then do
      --    let (sameRound :: Bool) = (foldr (&&) True (map (== round) decisionRounds)) && ((length decisionRounds) > 0)
      --    let sameCoin = ((roundCoins !! round) == (roundCoins !! (round-1)))
      --    if (not sameRound) && sameCoin then do
      --      liftIO $ putStrLn $ "-------------------------------------- failure ----------------------------------"
      --      writeIORef failure True
      --      --error "success"
      --    else return ()
      --  else return ()
      forMseq_ ll $ \l -> do
        case l of
          Left leaks -> do
            forMseq_ leaks $ \leak -> do
              case leak of
                (sid, ((EST r b, DeliverTokensWithMessage tk), SendTokens st)) -> do
                  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "SCCMulticast" $ snd sid
                  modifyIORef estInR $ Map.insertWith (++) pidS [r]
                  modifyIORef lastEst $ Map.insert pidS r
                  --r' <- readIORef lastRound
                  --if r < r' then error $ "getting an earlier round later. r=" ++ show r ++ ", r'=" ++ show r'
                  --else writeIORef lastRound r
                (sid, ((AUX r b, DeliverTokensWithMessage tk), SendTokens st)) -> do
                  -- skip round 1 messages, they don't count
                  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "SCCMulticast" $ snd sid
                  if r > 1 then do
                    --liftIO $ putStrLn $ "r>1" 
                    Just pidSest <- (readIORef estInR) >>= (return . Map.lookup pidS)
                    liftIO $ putStrLn $ show pidSest
                    let estInR = elem r pidSest 
                    Just pidSaux <- (readIORef auxInR) >>= (return . Map.lookup pidS)  
                    let auxInRminus = elem (r-1) pidSaux
                    if (auxInRminus && (not estInR)) then do -- this means supportCoin = True
                      liftIO $ putStrLn $ ("sc=T for " ++ show pidS ++ " in round " ++ show r)
                      modifyIORef supportCoinsTrueInRound (Map.insertWith (+) r 1)
                    else return ()
                  else return ()
                  liftIO $ putStrLn $ "aux " ++ show pidS
                  modifyIORef auxInR $ Map.insertWith (++) pidS [r]
                  modifyIORef lastAux $ Map.insert pidS r
                  --r' <- readIORef lastRound
                  --if r < r' then error $ "getting an earlier round later. r=" ++ show r ++ ", r'=" ++ show r'
                  --else writeIORef lastRound r
            --scInR <- (readIORef supportCoinsTrueInRound >>= return. Map.assocs)
            --forMseq_ scInR $ \(round, numsc) -> do
            --  if numsc == (length (parties \\ crupts)) then
            --    liftIO $ putStrLn $ "all sc"
            --  else return ()
          Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
            -- round of last message (if EST then it's round r else if AUX then r-1)
            liftIO $ putStrLn $ "output " ++ show pid
            readIORef lastAux >>= liftIO . liftIO . putStrLn . ("lastaux " ++) . show
            Just estr <- (readIORef lastEst >>= return . (Map.lookup pid))
            Just auxr <- (readIORef lastAux >>= return . (Map.lookup pid))
            let r = max estr auxr
            modifyIORef whenDecide $ Map.insert pid r
          Right (pid, (ABAF2P_Ok, SendTokens st)) ->
            return ()
      
      readIORef estInR >>= liftIO . putStrLn . ("estInR " ++) . show
      readIORef auxInR >>= liftIO . putStrLn . ("auxInR " ++) . show

      --er <- readIORef estInR
      --ar <- readIORef auxInR
      --forMseq_ (parties \\ crupts) $ \p -> do
      --  let pest = Map.lookup p er
      --  let paux = Map.lookup p ar    
      --  liftIO $ putStrLn $ "pd=" ++ show p ++ " pest=" ++ show pest
      --  liftIO $ putStrLn $ "paux=" ++ show paux

      -- find the intersection of the rounds 
      prounds <- newIORef []
      scInR <- (readIORef supportCoinsTrueInRound >>= return . Map.assocs)
      liftIO $ putStrLn $ "supportCoin map " ++ show scInR
      decisionRounds <- (readIORef whenDecide >>= return . Map.elems)
      --liftIO $ putStrLn $ "decision rounds: " ++ show decisionRounds
      forMseq_ scInR $ \(round, numsc) -> do
        if numsc == (length (parties \\ crupts)) then do
          --liftIO $ putStrLn $ "Checking round " ++ show round ++ " with numsc: " ++ show numsc
          -- all supportCoins are True
          -- did all parties decide this round?
          let (sameRound :: Bool) = (foldr (&&) True (map (== round) decisionRounds)) && ((length decisionRounds) > 0)
          liftIO $ putStrLn $ "sameRound=" ++ show sameRound
          let sameCoin = ((roundCoins !! round) == (roundCoins !! (round-1)))
          liftIO $ putStrLn $ "sameCoin=" ++ show sameCoin
          liftIO $ putStrLn $ "Round " ++ show round ++ ": " ++ show (roundCoins !! round)
          liftIO $ putStrLn $ "Round " ++ show (round-1) ++ ": " ++ show (roundCoins !! (round-1))
          if (not sameRound) && sameCoin then do
            liftIO $ putStrLn $ "\t\t*************Violation of Lemma 17********************"
            writeIORef failure True
          else return ()
        else return ()
      
      f <- readIORef failure
      return (not f)

prop_ABALemma17Rounds = prop_ABALemma17 ABACorrect SBcastCorrect SBSCorrect ABARounds_Buggy ABABinPtr_Persist ABAAnyAux_Correct
  

{- Compared to previous environments, in this environment honest deliver and adv input is interleaved always -}
testUEnvABABetterAdv
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool) m
testUEnvABABetterAdv parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let t = 1 :: Int
  --let crupt = "Bob" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  
  
  -- valueFilter :: ABACast -> (Int, Bool) 
  let valueFilter msg = case msg of
                          AUX r b -> (2,r,b)
                          EST r b -> (1,r,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  
  let getEstByArb r = do
            whichInp <- liftIO $ generate arbitrary
            getByFilter (1,r,whichInp)
  let getAuxByArb r = do
            whichInp <- liftIO $ generate arbitrary
            getByFilter (r,r,whichInp)
 
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  forMseq_ pidsT $ \h -> do
    writeChan z2p $ (h, ((ClockP2F_Through True), SendTokens inputTokens))
    readChan pump
  
  forMseq_ pidsF $ \h -> do
    writeChan z2p $ (h, ((ClockP2F_Through False), SendTokens inputTokens))
    readChan pump

  -- INIT: deliver ESTs + crupt by partition
  c <- envQueueSize z2a clockChan 0
  estT <- estTrue 1
  estF <- estFalse 1
  recvT <- getByReceivers pidsT
  recvF <- getByReceivers pidsF
  doDelivers $ (intersect estT recvT) ++ (intersect estF recvF)

  -- similar structure for all rounds
  let rounds = 10
  forMseq_ [1..rounds] $ \r -> do
    -- give some parties more EST messages to get different views
    partition <- selectPIDs honest
    estsIdxs <- newIORef []    -- a list of CmdDelivers
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      ests <- getEstByArb r
      modifyIORef estsIdxs $ (++ ests)
      --doDelivers (intersect ests forp)
    estCmds <- readIORef estsIdxs >>= return . map Right . map (\x -> (x, 0)) . deliverListAll
  
    -- give crupt input of arbitrary input 
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaEstMsg (makeSBCastSid parties cpid r) partition inputs r 64
      modifyIORef cinpsEsts $ (++  (map Left cinp))
      --envExecABACmd z2p z2a pump (cinp !! 0)

    cinpCmds <- readIORef cinpsEsts 
    --deliverCmds <- readIORef estCmds 
    -- interleave then execute
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ estCmds)
    forMseq_ finalSet $ \i -> do
      envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

    -- give AUX to make all parties progress to the next round
    auxs <- allAuxs r
    --doDelivers auxs
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll auxs))
    forMseq_ finalSet $ \i -> do
      envExecCmd z2p z2a z2f clockChan pump i envExecABACmd
    
    ---- deliver rest of round r messages
    --ests <- allEsts r
    --doDelivers ests



  tr <- readIORef transcript
  cl <- readIORef cmdList

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM)

prop_uABAAdvSafety abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug) 
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      (config', c', t', inps) <- run $ runITMinIO 120 $ execUC
        (testUEnvABABetterAdv ps cc 100 10000)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastAndCoinToken)
        dummyAdversaryToken
      printYellow("Checking safety...")
      pre $ (numDecided t') > 1
      printYellow ("[Config]\n\n" ++ show config')
      --printYellow ("[Inputs]\n\n" ++ show c')
      printYellow ("[Intputs]\n" ++ show inps)
      assert $ (numDecisions t') == 1

{- different threshold setting (only 2 or 3^3=27 -}
prop_uABAAdvSafetyCCC = prop_uABAAdvSafety ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct

{- These all fail safety check -}
prop_uABAAdvSafetySSS = quickCheckWithResult stdArgs{maxSuccess = 200}  $ prop_uABAAdvSafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any
prop_uABAAdvSafetySSC = prop_uABAAdvSafety ABASmall SBcastSmall SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct
prop_uABAAdvSafetyCSS = prop_uABAAdvSafety ABACorrect SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct
prop_uABAAdvSafetySCC = prop_uABAAdvSafety ABASmall SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Correct


testUEnvABASim
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABASim parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let t = 1 :: Int
  --let crupt = "Bob" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  
  
  -- valueFilter :: ABACast -> (Int, Bool) 
  let valueFilter msg = case msg of
                          AUX r b -> (2,r,b)
                          EST r b -> (1,r,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            --return (whichInp, idxs)
            return idxs
  let getAuxByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (r,r,whichInp)
            return (whichInp, idxs)
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
   
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  ---- give random input
  --forMseq_ honest $ \p -> do
  --  b <- generateM arbitrary
  --  writeChan z2p $ (p, ((ClockP2F_Through b), SendTokens inputTokens))
  --  readChan pump
  --  modifyIORef cmdList $ (++ [Left ((CmdABAP2F p b, inputTokens))])

  -- STEP 1: choose honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump
    modifyIORef cmdList $ (++ [Left ((CmdABAP2F p i, inputTokens))])

  -- INIT: deliver ESTs + crupt by partition
  c <- envQueueSize z2a clockChan 0
  modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
  estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  estToF <- intersectM (estFalse 1) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  -- similar structure for all rounds
  let rounds = 1
  forMseq_ [1..rounds] $ \r -> do
    -- STEP: give some PARTITION more EST from other bools
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      --(b',ests) <- getEstByArb r
      ests <- getEstByArb r
      --arbEst <- intersectM (getByReceivers [p]) (getEstByArb r)
      --doDelivers arbEst
      doDelivers (intersect ests forp)
   
    -- STEP give only PARTITION crupt input of arbitrary input 
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid r) partition inputs r 64
      modifyIORef cinpsEsts $ (++  (map Left cinp))

    cinpCmds <- readIORef cinpsEsts 
    -- TODO: doesn't interleave adv input with delivery of EST
    ---- interleave then execute
    ----finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ estCmds)
    finalSet <- liftIO $ generate $ shuffle cinpCmds
    doCmds finalSet
    modifyIORef cmdList $ (++ finalSet)
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

    -- STEP give all to all AUX to make parties make progress
    yprint ("Giving all AUX to all AUX")
    auxs <- allAuxs r
    --doDelivers auxs 
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    -- STEP: deliver adv AUX and delivery shuffled
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll $ auxs)) -- ++ ests))
    doCmds finalSet
    modifyIORef cmdList $ (++ finalSet)
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

    -- STEP: deliver remaining ESTs
    ests <- allEsts r
    doDelivers ests
    
    ---- deliver rest of round r messages
    yprint ("Giving rest of EST to all")
    yprint ("Looping environment")

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

testABASimShuffle
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testABASimShuffle parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let t = 1 :: Int
  --let crupt = "Bob" :: PID
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
  () <- readChan pump
 
  cmdList <- newIORef []  
  
  -- valueFilter :: ABACast -> (Int, Bool) 
  let valueFilter msg = case msg of
                          AUX r b -> (2,r,b)
                          EST r b -> (1,r,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,r,whichInp)
            --return (whichInp, idxs)
            return idxs
  let getAuxByArb r = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (r,r,whichInp)
            return (whichInp, idxs)
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
   
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  pidsT <- selectPIDs honest
  let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  ---- give random input
  --forMseq_ honest $ \p -> do
  --  b <- generateM arbitrary
  --  writeChan z2p $ (p, ((ClockP2F_Through b), SendTokens inputTokens))
  --  readChan pump
  --  modifyIORef cmdList $ (++ [Left ((CmdABAP2F p b, inputTokens))])

  -- STEP 1: choose honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump
    modifyIORef cmdList $ (++ [Left ((CmdABAP2F p i, inputTokens))])

  -- similar structure for all rounds
  let rounds = 4
  forMseq_ [1..rounds] $ \r -> do
    -- STEP: deliver some shuffled subset of all EST
    ests <- (allEsts r) >>= generateM . sublistOf
    doDelivers ests

    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaEstMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpsEsts $ (++  (map Left cinp))
    cinpCmds <- readIORef cinpsEsts 
    finalSet <- generateM $ shuffle cinpCmds
    doCmds finalSet
    modifyIORef cmdList $ (++ finalSet)

    -- STEP: deliver some shuffled subset of all AUX
    auxs <- (allAuxs r) >>= generateM . sublistOf
    doDelivers auxs

    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    finalSet <- generateM $ shuffle cinpCmds
    doCmds finalSet
    modifyIORef cmdList $ (++ finalSet)

    -- STEP: deliver the rest of the EST
    ests <- allEsts r
    doDelivers ests
    
    -- STEP: deliver rest of the AUX
    auxs <- allAuxs r
    doDelivers auxs

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)


propSimBias = monadicIO $ do
  let prot () = protABABreak (ABACorrect, SBcastCorrect, SBSCorrect, ABARounds_Correct, ABABinPtr_Persist, ABAAnyAux_Correct)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      liftIO $ putStrLn $ "Crupt parties: " ++ show cc
      ((config', c', t', inps, ll), bits) <- run $ runITMinIO 120 $ runRandRecord $ execUC
        (testABASimShuffle ps cc 100 1000)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastAndCoinToken)
        dummyAdversaryToken
      tIdeal <- run $ runITMinIO 120 $ runRandReplay bits $ execUC      
        (performABAEnv config' c')
        idealProtocolToken
        (runAsyncF $ fABA)
        (runTokenA simABA)
      let idx = compareTranscript t' tIdeal
      let (agreement, split) = splitAt idx t'
      --liftIO $ putStrLn $ "Agreement: " ++ show agreement
      --liftIO $ putStrLn $ "split: " ++ show split
      --liftIO $ putStrLn $ "Real: " ++ show (take (idx+1) t')
      --liftIO $ putStrLn $ "\n\nIdeal: " ++ show (take (idx+3) tIdeal)
      liftIO $ putStrLn $ "idx: " ++ show idx
      --liftIO $ putStrLn $ "real: " ++ show t'
      --liftIO $ putStrLn $ "ideal: " ++ show tIdeal
      assert $ t' == tIdeal
      liftIO $ putStrLn $ "real = ideal"
      let decidedReal = numDecided t'
      let decidedIdeal = numDecided tIdeal
      let decisionsReal = numDecisions t'
      let decisionsIdeal = numDecisions tIdeal
      pre $ decidedReal > 1
      liftIO $ putStrLn $ "decideIdeal >= decideReal"
      assert (decidedIdeal >= decidedReal)
      liftIO $ putStrLn $ "decideReal == " ++ show decisionsReal
      assert (decisionsReal == 1)
      liftIO $ putStrLn $ "decideIDeal == " ++ show decisionsIdeal
      assert (decisionsIdeal == 1)
      
      let realDecision = firstDecision t'
      let idealDecision = firstDecision tIdeal
      monitor  (collect ("real", realDecision))
      monitor (collect ("ideal", idealDecision))

      --(config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
      --  --(testUEnvABAPartition ps cc 100 10000)
      --  (testUEnvABAAdvEstAndAux ps cc 100 1000)
      --  (runAsyncP $ prot ())
      --  (runAsyncF $ bangFAsync fMulticastAndCoinToken)
      --  dummyAdversaryToken
      --printYellow("Checking safety...")
      --pre $ (numDecided t') > 1
      --printYellow ("[Config]\n\n" ++ show config')
      ----printYellow ("[Inputs]\n\n" ++ show c')
      --printYellow ("[Intputs]\n" ++ show inps)
      --assert $ (numDecisions t') == 1
