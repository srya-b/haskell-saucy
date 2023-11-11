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
import ABA
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
          writeChan z2p $ (pid', ((ClockP2F_Through $ x'), SendTokens 32))
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

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z  
  () <- readChan pump

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  readChan clockChan
  let n = length parties

  forMseq_ cmdList $ \cmd -> do
    envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd
  writeChan outp =<< readIORef transcript

{- This environment is a simple check that the protocol works. It will always deliver all messages in a round and randomly choose honest party values -}
testEnvABADeliverAll
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript) m
testEnvABADeliverAll parties crupts importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  
  let t = 1 :: Int
  let honest = parties \\ crupts
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
 
  let cruptMapList = map (\x -> (x,())) crupts 
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ cruptMapList)
 
  cmdList <- newIORef []  

  let valueFilter msg = case msg of
                          EST r b -> (1,r,b)
                          AUX r b -> (2,r,b)
 
  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt
 
  let inputTokens = 10000
  -- Give somehonest parties some inputs
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdABAP2F h x, inputTokens)])
    writeChan z2p $ (h, ((ClockP2F_Through $ x), SendTokens inputTokens))
    readChan pump

  firstInp <- newIORef []
  forMseq_ [1..20] $ \r -> do 
    modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
    c <- envQueueSize z2a clockChan 0

    inps <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinps <- liftIO $ generate $ abaGeneratorOnlyMsgs (max 10 c) (makeMainSid parties cpid r) (makeSBCastSid parties cpid r) parties inputs r 64
      modifyIORef inps (++ map Left cinps)
  
    dinps <- liftIO $ generate $ rqDeliverAll c
    modifyIORef inps (++ map (\x -> Right (x,0)) dinps)
    execInps <- readIORef inps >>= (liftIO . generate . shuffle)
    forMseq_ execInps $ \i -> do
      envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

  tr <- readIORef transcript  
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, Map.fromList $ cruptMapList ++ [("-1",())], t), cl, tr)

prop_ABADeliverAll = monadicIO $ do
  let prot () = protABA
  let parties = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] :: [PID]
  let crupts = ["Bob"]
  (config', c', t') <- run $ runITMinIO 120 $ execUC
    (testEnvABADeliverAll parties crupts 10000)
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

testUEnvABACompletion
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript) m
testUEnvABACompletion parties crupts rounds importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter
 
  let allAuxs r = do getByFilter (2,r,True) >>= \x -> getByFilter (2,r,False) >>= \y -> return (x ++ y)
  let allEsts r = do getByFilter (1,r,True) >>= \x -> getByFilter (1,r,False) >>= \y -> return (x ++ y)
  let auxTrue r = do getByFilter (2,r,True)
  let auxFalse r = do getByFilter (2,r,False)
  let estFalse r = do getByFilter (1,r,False)
  let estTrue r = do getByFilter (1,r,True)
  let doDelivers ds = do forMseq_ (deliverListAll ds) $ deliverer []
  
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
  let rounds = 2
  forMseq_ [1..rounds] $ \r -> do
    -- give some parties more EST messages to get different views
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      ests <- getEstByArb r
      doDelivers (intersect ests forp)
   
    -- give crupt input of arbitrary input 
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 1 $ abaEstMsg (makeSBCastSid parties cpid r) partition inputs r 64
      envExecABACmd z2p z2a pump (cinp !! 0)

    -- give AUX to make all parties progress to the next round
    auxs <- allAuxs r
    doDelivers auxs

  tr <- readIORef transcript
  cl <- readIORef cmdList

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr)

-- This property runs the "correct" protocol and asserts that safety is achieved
-- and that the protocol should terminate with agreement
prop_uABACompletion abaVariant bcastVariant svalVariant = monadicIO $ do
  let prot () = protABABreak abaVariant bcastVariant svalVariant 
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let t = length ps `div` 3
    let crupts = []
    (config', c', t') <- run $ runITMinIO 120 $ execUC
      (testUEnvABACompletion ps crupts 100 10000)
      (runAsyncP $ prot ())
      (runAsyncF $ bangFAsync fMulticastAndCoinToken)
      dummyAdversaryToken
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t')-1] $ \i -> do
      case (t' !! i) of
        Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
          modifyIORef outputs $ Set.insert b
        Right _ -> return ()
        Left _ -> return ()
    o <- readIORef outputs

    pre $ (Set.size o) > 0
    assert $ (Set.size o) == 1

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')

{- A Safety checker that accepts thresholds to change in the protocol. -}
prop_uABASafety abaVariant bcastVariant svalVariant = monadicIO $ do
  liftIO $ putStrLn $ "\n==========================================================\n"
  let prot () = protABABreak abaVariant bcastVariant svalVariant 
  --forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
  --let t = length ps `div` 3
  let t = 1 
  let parties = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"]
  let crupts = ["Frank"]
  --crupts <- liftIO $ generate $ cruptFrom ps 1
  (config', c', t') <- run $ runITMinIO 120 $ execUC
    (testUEnvABACompletion parties crupts 100 10000)
    (runAsyncP $ prot ())
    (runAsyncF $ bangFAsync fMulticastAndCoinToken)
    dummyAdversaryToken
  outputs <- newIORef Set.empty
  numOutputs <- newIORef 0
  forMseq_ [0..(length t')-1] $ \i -> do
    case (t' !! i) of
      Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
        modifyIORef outputs $ Set.insert b
        modifyIORef numOutputs $ (+) 1
      Right _ -> return ()
      Left _ -> return ()
  o <- readIORef outputs
  no <- readIORef numOutputs

  pre $ (Set.size o) > 0
  pre $ no > 1
  printYellow("Checking safety...")
  assert $ (Set.size o) == 1
  printYellow ("[Config]\n\n" ++ show config')
  printYellow ("[Inputs]\n\n" ++ show c')

{- different threshold setting (only 2 or 3^3=27 -}
prop_uABASafetyCCC = prop_uABASafety ABACorrect SBcastCorrect SBSCorrect
prop_uABASafetySSS = do
  let args = stdArgs{maxSuccess = 500}
  quickCheckWithResult args $ prop_uABASafety ABASmall SBcastSmall SBSSmall
