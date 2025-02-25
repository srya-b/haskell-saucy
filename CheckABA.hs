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

makeRoSid :: [PID] -> Int -> SID
makeRoSid parties r = (show ("sRO", r), show("-1", parties, ""))

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
    :: (MonadEnvironment m) =>  Int -> [PID] -> [PID] -> Int -> [PID] -> [PID] -> DeliveryTypeAll ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript) m
testEnvABADeliverAll rounds parties crupts importAmt pidsT pidsF dtype z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  
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
              liftIO $ putStrLn $ "doDeliver: " ++ show i
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

  --let inputs = do [return True, return False]
  let inputTokens = importAmt
 
  let inputTokens = 10000
  -- Give somehonest parties random inputs
  --forMseq_ honest $ \h -> do
  --  -- choose a boolean
  --  x <- liftIO $ generate chooseAny
  --  modifyIORef cmdList $ (++ [Left $ (CmdABAP2F h x, inputTokens)])
  --  writeChan z2p $ (h, ((ClockP2F_Through $ x), SendTokens inputTokens))
  --  readChan pump

  forMseq_ pidsT $ \p -> do
    modifyIORef cmdList $ (++ [Left $ (CmdABAP2F p True, inputTokens)])
    writeChan z2p $ (p, ((ClockP2F_Through $ True), SendTokens inputTokens))
    readChan pump

  liftIO $ putStrLn $ "true: " ++ show pidsT
  liftIO $ putStrLn $ "false: " ++ show pidsF
    
  forMseq_ pidsF $ \p -> do
    modifyIORef cmdList $ (++ [Left $ (CmdABAP2F p False, inputTokens)])
    writeChan z2p $ (p, ((ClockP2F_Through $ False), SendTokens inputTokens))
    readChan pump

  firstInp <- newIORef []
  let rounds = 3
  forMseq_ [1..rounds] $ \r -> do 
    modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
    c <- envQueueSize z2a clockChan 0
    liftIO $ putStrLn $ "Queue size: " ++ show c

    inps <- newIORef []
    --forMseq_ crupts $ \cpid -> do
    --  cinps <- liftIO $ generate $ abaGeneratorOnlyMsgs (max 10 c) (makeMainSid parties cpid r) (makeSBCastSid parties cpid r) parties inputs r 64
    --  modifyIORef inps (++ map Left cinps)
 
    dinps <- case dtype of
               -- randomize the queue and deliver 
               AllRandom -> generateM $ rqDeliverAll c
               Sequential -> rqDeliverAllSeq c
               ProtocolOrder -> do
                 ests :: [Int] <- allEsts r -- >>= generateM . shuffle
                 liftIO $ putStrLn $ "ests: " ++ show ests
                 doDelivers ests
                 auxs :: [Int] <- allAuxs r -- >>= generateM . shuffle
                 --return (ests ++ auxs)
                 liftIO $ putStrLn $ "auxs: " ++ show auxs
                 doDelivers auxs
                 return . deliverListAll $ (ests ++ auxs)
                 
    liftIO $ putStrLn $ "\n*****Delivering shuffle of crupt and delivers: " ++ show dinps
    --forMseq_ dinps $ \d -> do
    --  envExecCmd z2p z2a z2f clockChan pump (Right (d, 0)) envExecABACmd

    --modifyIORef inps (++ map (\x -> Right (x,0)) dinps)
    --execInps <- readIORef inps >>= (liftIO . generate . shuffle)
    --forMseq_ (deliverListAllMixed execInps) $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd

  tr <- readIORef transcript  
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, Map.fromList $ cruptMapList ++ [("-1",())], t), cl, tr)

prop_ABADeliverAllType dtype = monadicIO $ do
  let prot () = protABABreak (ABACorrect, SBcastCorrect, SBSCorrect, ABARounds_Correct, ABABinPtr_Persist, ABAAnyAux_Any, ABASupport_Correct)

  let parties = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] :: [PID]
  let crupts = ["Bob"]
  let honest = parties \\ crupts
  
  pidsT <- newIORef []
  pidsF <- newIORef ([] :: [PID])
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    if x then modifyIORef pidsT (++ [h]) else modifyIORef pidsF (++ [h])
  --pidsT <- newIORef (honest)
  --pidsF <- newIORef []

  pt <- readIORef pidsT
  pf <- readIORef pidsF
  --let pt = honest
  --let pf = honest \\ pt
  (config', c', t') <- run $ runITMinIO 120 $ execUC
    (testEnvABADeliverAll 20 parties crupts 10000 pt pf dtype)
    (runAsyncP $ prot ())
    (runAsyncF $ bangFAsync fMulticastAndCoinToken)
    dummyAdversaryToken
  outputs <- newIORef Set.empty
  numDecide <- newIORef 0
  forMseq_ t' $ \outp -> do
    case outp of
      Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
        modifyIORef outputs $ Set.insert b
        modifyIORef numDecide $ (+) 1
      Right _ -> return ()
      Left _ -> return ()
  o <- readIORef outputs
  n <- readIORef numDecide

  --assert False
  if (length pt) > (length pf) then
    monitor (collect ((length pt, length pf), n))
  else
    monitor (collect ((length pf, length pt), n))
  --pre $ (Set.size o) > 0
  --assert $ (Set.size o) == 1

  printYellow ("[Config]\n\n" ++ show config')
  printYellow ("[Inputs]\n\n" ++ show c')

prop_ABADeliverAll = prop_ABADeliverAllType AllRandom 
prop_ABADeliverAllProtocol = prop_ABADeliverAllType ProtocolOrder
prop_ABADeliverAllSeq = prop_ABADeliverAllType Sequential


cruptEstMsg :: (MonadITM m) => [PID] -> [PID] -> [Gen Bool] -> Int -> Int -> m [Either ABAInput AsyncInput]
cruptEstMsg crupts receivers inputs round n = do
  cinps <- newIORef []
  forMseq_ crupts $ \cpid -> do
    cinp <- liftIO $ generate $ vectorOf n $ abaEstMsg (makeSBCastSid receivers cpid round) receivers inputs round 64
    modifyIORef cinps $ (++ (map Left cinp)) 
  readIORef cinps >>= return

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
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABAPartition parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
  let rounds = 6
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
    --cinpCmds <- cruptEstMsg crupts partition inputs r 5

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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
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
    yprint ("Looping environment " ++ show r)

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
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABAAdvEstAndAux parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
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
prop_uABASafety abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        (testUEnvABAPartition ps cc 100 10000 pidsT pidsF)
        --(testUEnvABAAdvEstAndAux ps cc 100 1000 pidsT pidsF)
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
prop_uABASafetyCCC = quickCheckWithResult stdArgs{maxSuccess = 1000} $ prop_uABASafety ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

{- FAIL: These all fail safety check -}
prop_uABASafetySSS = quickCheckWithResult stdArgs{maxSuccess = 1000}  $ prop_uABASafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
--prop_uABASafetySSS = quickCheck $ prop_uABASafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_uABASafetySSC = quickCheck $ prop_uABASafety ABASmall SBcastSmall SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_uABASafetyCSS = quickCheck $ prop_uABASafety ABACorrect SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_uABASafetySCC = quickCheck $ prop_uABASafety ABASmall SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

testUEnvABAProgress
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABAProgress parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
    --cinpCmds <- cruptEstMsg crupts partition inputs r 5

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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    -- STEP: deliver adv AUX and delivery shuffled
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll $ auxs)) -- ++ ests))
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd
    -- STEP: deliver remaining ESTs
    ---- deliver rest of round r messages
    yprint ("Giving rest of EST to all")
    ests <- allEsts r
    doDelivers ests

    -- deliver all AUXs now
    auxs <- allAuxs r
    doDelivers auxs

    -- get coin flip value
    --if (length crupts) > 0 then do
    --  let cpid = crupts !! 0
    --  writeChan z2a $ asyncA2PMsg cpid (ro_sid r, (CoinCastP2F_ro r, SendTokens 1)) 1
    --  () <- readChan pump
    --  c <- readIORef lastOut >>= return . advCoinP2A
    --  writeIORef coinResult c
    --else ?getBit >>= writeIORef coinresult

    -- do the next round's partitioned delivery
    -- we want to try to deliver    

    
    yprint ("Looping environment " ++ show r)

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

prop_Termination abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      let cc = []
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      forMseq_ [81] $ \im -> do
        (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
          (testUEnvABAProgress ps cc im im pidsT pidsF)
          --(testUEnvABAAdvEstAndAux ps cc 100 1000 pidsT pidsF)
          (runAsyncP $ prot ())
          (runAsyncF $ bangFAsync fMulticastAndCoinToken)
          dummyAdversaryToken
        printYellow("Checking safety...")
        --pre $ (numDecided t') > 1
        let majorityInput = if (length pidsT) > (length pidsF) then length pidsT else length pidsF
        monitor (collect (im, majorityInput, numDecided t'))
        assert $ if (majorityInput > 4 && (numDecided t') == 0) then False else True

prop_TerminationCCC = quickCheckWithResult stdArgs{maxSuccess = 100} $ prop_Termination ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct



testUEnvABALemma17
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABALemma17 parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
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

prop_ABALemma17 abaVariant bcastVariant svalVariant roundBug binPtr auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtr, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        --(testUEnvABAPartition ps cc 100 10000)
        (testUEnvABALemma17 ps cc 4 1000 pidsT pidsF)
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

prop_ABALemma17Rounds = prop_ABALemma17 ABACorrect SBcastCorrect SBSCorrect ABARounds_Buggy ABABinPtr_Persist ABAAnyAux_Correct ABASupport_Correct

  

{- Compared to previous environments, in this environment honest deliver and adv input is interleaved always -}
testUEnvABABetterAdv
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABABetterAdv parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
      -- TODO
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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
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
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

prop_uABAAdvSafety abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        (testUEnvABABetterAdv ps cc 100 10000 pidsT pidsF)
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
prop_uABAAdvSafetyCCC = prop_uABAAdvSafety ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

{- These all fail safety check -}
prop_uABAAdvSafetySSS = quickCheckWithResult stdArgs{maxSuccess = 200}  $ prop_uABAAdvSafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_uABAAdvSafetySSC = prop_uABAAdvSafety ABASmall SBcastSmall SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_uABAAdvSafetyCSS = prop_uABAAdvSafety ABACorrect SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_uABAAdvSafetySCC = prop_uABAAdvSafety ABASmall SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

prop_BinPtr = monadicIO $ do
  let prot () = protABABreak (ABACorrect, SBcastCorrect, SBSCorrect, ABARounds_Correct, ABABinPtr_Reset, ABAAnyAux_Any, ABASupport_Correct)
  --let allEnvs = [return testUEnvABAPartition, return testUEnvABAAdvEstAndAux, return testUEnvABALemma17, return testUEnvABABetterAdv, return testUEnvABASim, return testABASimShuffle]
  --let env = testUEnvABAPartition
  let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"]
  --let cc = ["Alice"]
  let cc = []
  let honest = ps \\ cc
  pidsT <- selectPIDs honest
  let pidsT = honest
  let pidsF = honest \\ pidsT
  (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
    (testUEnvABAPartition ps cc 100 10000 pidsT pidsF)
    (runAsyncP $ prot ())
    (runAsyncF $ bangFAsync fMulticastAndCoinToken)
    dummyAdversaryToken
  printYellow("Checking safety...")
  printYellow ("[Config]\n\n" ++ show config')
  --printYellow ("[Inputs]\n\n" ++ show c')
  printYellow ("[Intputs]\n" ++ show inps)
  let nd = numDecided t'
  let majoritySize = if (length pidsT) > (length pidsF) then length pidsT else length pidsF
  monitor $ collect (majoritySize, nd)
  assert False
  


testUEnvABASim
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABASim parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
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
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testABASimShuffle parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

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
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
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
  let prot () = protABABreak (ABACorrect, SBcastCorrect, SBSCorrect, ABARounds_Correct, ABABinPtr_Persist, ABAAnyAux_Any, ABASupport_Correct)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      liftIO $ putStrLn $ "Crupt parties: " ++ show cc
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      ((config', c', t', inps, ll), bits) <- run $ runITMinIO 120 $ runRandRecord $ execUC
        (testABASimShuffle ps cc 100 1000 pidsT pidsF)
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

testABALiveness
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> (Map PID Bool) ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testABALiveness parties crupts rounds importAmt inputMap z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  let getBySenders ps = do
          ret <- newIORef []
          forMseq_ ps $ \p -> getBySender p >>= modifyIORef ret . (++)
          readIORef ret

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

  --let inputs = do [return True, return False]
  let inputTokens = importAmt 

  -- STEP 1: choose honest inputs
  forMseq_ (Map.keys inputMap) $ \p -> do
    let i = (Map.!) inputMap p
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  -- whichever group has more, isolate one of them
  -- p1 = 0, p2 = 1, p3 = 1  --> select either p2 or p3
  --im <- readIORef inputMap
  let pf = Map.filter (== False) inputMap
  let pt = Map.filter (== True) inputMap
  let nf = Map.size pf
  let nt = Map.size pt 
  
  let isolated = if nf >= nt then ((Map.keys pf) !! 0) else ((Map.keys pt) !! 0)
  --let isolated = "P2"
  liftIO $ putStrLn $ "Isolated: " ++ show isolated
  let commonChoice = if nf >= nt then False else True
  let commonEst = if commonChoice then estTrue else estFalse
  let notCommonEst = if commonChoice then estFalse else estTrue
  let commonAux = if commonChoice then auxTrue else auxFalse
  let notCommonAux = if commonChoice then auxFalse else auxTrue

  -- deliver between the non isolated 
  -- let p1 and p3 deliver 1
  -- give the p1 EST(1) caue them to echo EST(1) 
  -- then give all EST(1) to non isolated
  c <- envQueueSize z2a clockChan 0
  --estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  --estTtoF <- intersectM (estTrue 1) (getByReceivers $ (Map.keys pf) \\ [isolated])
  estTtoF <- intersectM3  (getByReceivers $ (Map.keys pf) \\ [isolated]) (getBySenders (honest \\ [isolated]))  (commonEst 1)
  doDelivers estTtoF

  -- crupt send EST(1) to p1
  cinpsEsts <- newIORef []
  forMseq_ crupts $ \cpid -> do
    cinp <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid 1) (honest \\ [isolated]) [return commonChoice] 1 64
    modifyIORef cinpsEsts $ (++  (map Left cinp))
  cinpCmds <- readIORef cinpsEsts 
  finalSet <- liftIO $ generate $ shuffle cinpCmds
  doCmds finalSet

  -- give EST(1) to all except 
  estTs <- intersectM (commonEst 1) (getByReceivers $ (honest \\ [isolated]))
  doDelivers estTs

  -- get EST(0) delivered too
  estTtoF <- intersectM3  (getByReceivers $ (Map.keys pt) \\ [isolated]) (getBySenders (honest \\ [isolated]))  (notCommonEst 1)
  doDelivers estTtoF

  -- crupt send EST(1) to p1
  cinpsEsts <- newIORef []
  forMseq_ crupts $ \cpid -> do
    cinp <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid 1) (honest \\ [isolated]) [return (not commonChoice)] 1 64
    modifyIORef cinpsEsts $ (++  (map Left cinp))
  cinpCmds <- readIORef cinpsEsts 
  finalSet <- liftIO $ generate $ shuffle cinpCmds
  doCmds finalSet

  -- give EST(1) to all except 
  estTs <- intersectM (notCommonEst 1) (getByReceivers $ (honest \\ [isolated]))
  doDelivers estTs

  -- get p1 and p3 to the coin flip stage
  auxs <- intersectM (allAuxs 1) (getByReceivers $ honest \\ [isolated])
  doDelivers auxs

  liftIO $ putStrLn $ "%%%%%%%%%%%%%%%%%%%%"

  forMseq_ crupts $ \cpid -> do
    cinp <- liftIO $ generate $ vectorOf 5 $ abaAuxMsg (makeMainSid parties cpid 1) (honest \\ [isolated]) [return (not commonChoice)] 1 64
    doCmds (map Left cinp)


  -- check out the coin value
  forMseq_ crupts $ \cpid -> do
    writeChan z2a $ ((SttCruptZ2A_A2P $ (cpid, ClockP2F_Through (makeRoSid parties 1, (CoinCastP2F_ro (1 :: Int), SendTokens 1)))), SendTokens 0)
    readChan pump

  coinRes <- readIORef lastOut
  let Just (Left (SttCruptA2Z_P2A (_pid, (_sid, (CoinCastF2P_ro result, SendTokens _))))) = coinRes
  liftIO $ putStrLn $ "Coin: " ++ show result

  case result of
    _ | result == commonChoice -> do
      -- crupt try to force isolated party to deliver (not commonChoice) i.e. not the input it received
      ests <- intersectM (notCommonEst 1) (getByReceivers [isolated])
      doDelivers ests
      forMseq_ crupts $ \cpid -> do
        cinps <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid 1) [isolated] [return (not commonChoice)] 1 64
        doCmds (map Left cinps)
    _ | result == (not commonChoice) -> do -- let the isolated party deliver the not commonChoice
      ests <- intersectM (commonEst 1) (getByReceivers [isolated])
      doDelivers ests
      forMseq_ crupts $ \cpid -> do
        cinps <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid 1) [isolated] [return (not commonChoice)] 1 64
        doCmds (map Left cinps)

  -- now give isolated party all Auxes
  auxs <- intersectM (notCommonAux 1) (getByReceivers [isolated])
  auxs <- intersectM (allAuxs 1) (getByReceivers [isolated])
  na <- notCommonAux 1
  liftIO $ putStrLn $ "not common aux: " ++ show na
  liftIO $ putStrLn $ "isolated: " ++ show isolated
  liftIO $ putStrLn $ "auxs: " ++ show auxs
  doDelivers auxs
  forMseq_ crupts $ \cpid -> do
    cinp <- liftIO $ generate $ vectorOf 5 $ abaAuxMsg (makeMainSid parties cpid 1) [isolated] [return (not commonChoice)] 1 64
    doCmds (map Left cinp)

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputMap, ll)
 
prop_MMRLiveness abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    --let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let ps = ["P1", "P2", "P3", "P4"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      -- determine an input distribution
      let cc = ["P4"]
      let honest = ps \\ cc
      ---- Randomly choose parition of True and False
      --pidsT <- selectPIDs honest
      --let pidsF = honest \\ pidsT
      let pidsT = ["P2", "P3"]
      let pidsF = ["P1"]

      let ptm = map (\x -> (x,True)) pidsT
      let pfm = map (\x -> (x,False)) pidsF
      let inputM = Map.fromList (ptm ++ pfm)

      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        --(testUEnvABAPartition ps cc 100 10000)
        (testABALiveness ps cc 100 1000 inputM)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastAndCoinToken)
        dummyAdversaryToken
      assert False

prop_MMRLivenessCCC = quickCheck $ prop_MMRLiveness ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct



---------------------------------------------------------------
-- Safety Violation with CCC and AuxAny
testABA
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testABA parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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

  --let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

  -- store coin from each round, at r=1 set it to be the smaller of the two groups 
  -- (try to make them decide first)
  coinResult <- newIORef $ if (length pidsF) < (length pidsT) then True else False

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  -- STEP 1: deliver honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  -- INIT: deliver ESTs by input partition
  c <- envQueueSize z2a clockChan 0
  estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  estToF <- intersectM (estFalse 1) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  let ro_sid r = (show ("sRO", r), show("-1", parties, ""))

  -- The strategy tried to violate safety and that can only happen in
  -- subsequent rounds, and after the coin flip result. A party that decided in
  -- round `r` necessarily decides the value of the coin toss, so if we are trying
  -- to violate safety we should be targetting users with the opposite proposed
  -- value of the coin flip from last round. We hope they confirm the opposite value
  -- in this round.
  let rounds = 2
  forMseq_ [1..rounds] $ \r -> do
    c <- readIORef coinResult
    qsize <- envQueueSize z2a clockChan 0
    if qsize == 0 then error "quee is empty"
    else return ()
    -- we target the values indicated by the opposite of the coin flip 
    -- as the ones we want to force to decide
    let targetAux = if not c then auxTrue else auxFalse
    let notTargetAux = if not c then auxFalse else auxTrue
    let targetEst = if not c then estTrue else estFalse
    let notTargetEst = if not c then estFalse else estTrue
    let targetSet = if not c then pidsT else pidsF
    let notTargetSet = if not c then pidsF else pidsT
    let targetInput = if not c then True else False

    -- give byzantine EST message to target set to force delivery of (not c)
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinpF <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid r) honest [return targetInput] r 64
      modifyIORef cinpsEsts $ (++  (map Left cinpF))
    cinpCmds <- readIORef cinpsEsts   
    doCmds cinpCmds
    modifyIORef cmdList $ (++ cinpCmds)

    -- give the target set each other's EST that the above might have forced to echo
    ests <- intersectM (targetEst r) (getByReceivers targetSet)
    doDelivers ests
    ests <- intersectM (allEsts r) (getByReceivers notTargetSet)
    doDelivers ests
    -- by this point we hope all parties have broadcast AUX messages

    -- give the target set their AUX messages (they only see AUX for (not c))
    auxs <- intersectM (targetAux r) (getByReceivers targetSet)
    doDelivers auxs 
    -- byzantine AUX messages of the same for the target set
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) targetSet [return targetInput] r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    doCmds cinpCmds
    modifyIORef cmdList $ (++ cinpCmds)

    -- give the non target set so they make progress too and reach the coin flip
    auxs <- intersectM (allAuxs r) (getByReceivers notTargetSet)
    doDelivers auxs
    -- at this point we assume everyone has reached the coin flip

    -- get coin flip value
    let cpid = crupts !! 0
    writeChan z2a $ asyncA2PMsg cpid (ro_sid r, (CoinCastP2F_ro r, SendTokens 1)) 1
    () <- readChan pump
    c <- readIORef lastOut >>= return . advCoinP2A
    writeIORef coinResult c

    -- force progress for all in case we don't succeed
    -- and we try again next round
    auxs <- allAuxs r
    doDelivers auxs
    
  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

{- A Safety checker that accepts thresholds to change in the protocol. -}
prop_test abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      let cc = ["Dave"]
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      let pidsT = ["Bob", "Charlie"]
      let pidsF = ["Alice"]
      (config', inputTrace', transcript', inps, leaks) <- run $ runITMinIO 120 $ execUC
        (testCSSAnyAux ps cc 100 10000 pidsT pidsF)
        (runAsyncP $ prot ())
        (runAsyncF $ bangFAsync fMulticastAndCoinToken)
        dummyAdversaryToken
      printYellow("Checking safety...")
      pre $ (numDecided transcript') > 1
      printYellow ("[Config]\n\n" ++ show config')
      printYellow ("[Inputs]\n\n" ++ show inputTrace')
      printYellow ("[Intputs]\n" ++ show inps)
      assert $ (numDecisions transcript') == 1

{- different threshold setting (only 2 or 3^3=27 -}
prop_testCCC = quickCheck $ prop_test ABACorrect  SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

{- FAIL: These all fail safety check -}
prop_testSSS = quickCheckWithResult stdArgs{maxSuccess = 1000}  $ prop_test ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
--prop_testSSS = quickCheck $ prop_test ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_testSSC = quickCheck $ prop_test ABASmall SBcastSmall SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_testCSS = quickCheck $ prop_test ABACorrect SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_testSCC = quickCheck $ prop_test ABASmall SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

testCSSAnyAux
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testCSSAnyAux parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT
  --let pidsT = ["Bob", "Charlie"]
  --let pidsF = ["Alice"]

  -- store coin from each round, at r=1 set it to be the smaller of the two groups 
  -- (try to make them decide first)
  coinResult <- newIORef $ if (length pidsF) < (length pidsT) then True else False

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  -- STEP 1: deliver honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  c <- envQueueSize z2a clockChan 0
  -- INIT: deliver ESTs by input partition
  estToT <- intersectM (estTrue 1) (getByReceivers pidsT)
  estToF <- intersectM (estFalse 1) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  let ro_sid r = (show ("sRO", r), show("-1", parties, ""))

  -- The strategy tried to violate safety and that can only happen in
  -- subsequent rounds, and after the coin flip result. A party that decided in
  -- round `r` necessarily decides the value of the coin toss, so if we are trying
  -- to violate safety we should be targetting users with the opposite proposed
  -- value of the coin flip from last round. We hope they confirm the opposite value
  -- in this round.
  let rounds = 2
  forMseq_ [1..rounds] $ \r -> do
    c <- readIORef coinResult
    -- we target the values indicated by the opposite of the coin flip 
    -- as the ones we want to force to decide
    let targetAux = if not c then auxTrue else auxFalse
    let notTargetAux = if not c then auxFalse else auxTrue
    let targetEst = if not c then estTrue else estFalse
    let notTargetEst = if not c then estFalse else estTrue
    let targetSet = if not c then pidsT else pidsF
    let notTargetSet = if not c then pidsF else pidsT
    let targetInput = if not c then True else False

    -- give byzantine EST message to target set to force delivery of (not c)
    cinpsEsts <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinpF <- liftIO $ generate $ vectorOf 5 $ abaEstMsg (makeSBCastSid parties cpid r) honest [return targetInput] r 64
      modifyIORef cinpsEsts $ (++  (map Left cinpF))
    cinpCmds <- readIORef cinpsEsts   
    doCmds cinpCmds
    modifyIORef cmdList $ (++ cinpCmds)

    -- give the target set each other's EST that the above might have forced to echo
    ests <- intersectM (targetEst r) (getByReceivers targetSet)
    doDelivers ests
    ests <- intersectM (allEsts r) (getByReceivers notTargetSet)
    doDelivers ests
    -- by this point we hope all parties have broadcast AUX messages

    -- give the target set their AUX messages (they only see AUX for (not c))
    --auxs <- intersectM (targetAux r) (getByReceivers targetSet)
    auxs <- intersectM (allAuxs r) (getByReceivers targetSet)
    doDelivers auxs 
    -- byzantine AUX messages of the same for the target set
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    doCmds cinpCmds
    modifyIORef cmdList $ (++ cinpCmds)

    -- give the non target set so they make progress too and reach the coin flip
    auxs <- intersectM (allAuxs r) (getByReceivers notTargetSet)
    doDelivers auxs
    -- at this point we assume everyone has reached the coin flip

    -- get coin flip value
    let cpid = crupts !! 0
    writeChan z2a $ asyncA2PMsg cpid (ro_sid r, (CoinCastP2F_ro r, SendTokens 1)) 1
    () <- readChan pump
    c <- readIORef lastOut >>= return . advCoinP2A
    writeIORef coinResult c

    -- force progress for all in case we don't succeed
    -- and we try again next round
    auxs <- allAuxs r
    doDelivers auxs
    
  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)


testUEnvABANoRounds
    :: (MonadEnvironment m) => [PID] -> [PID] -> Int -> Int -> [PID] -> [PID] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript, Map PID Bool, [Either [(SID, ((ABACast, TransferTokens Int), CarryTokens Int))] (PID, (ABAF2P, CarryTokens Int))]) m
testUEnvABANoRounds parties crupts rounds importAmt pidsT pidsF z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
                          AUX _ b -> (2,b)
                          EST _ b -> (1,b)

  (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
  (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter,getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter cmdList
 
  let allAuxs () = do getByFilter (2,True) >>= \x -> getByFilter (2,False) >>= \y -> return (x ++ y)
  let allEsts () = do getByFilter (1,True) >>= \x -> getByFilter (1,False) >>= \y -> return (x ++ y)
  let auxTrue () = do getByFilter (2,True)
  let auxFalse () = do getByFilter (2,False)
  let estFalse () = do getByFilter (1,False)
  let estTrue () = do getByFilter (1,True)

  let doDelivers ds = do 
            forMseq_ (deliverListAll ds) $ \i -> do
              deliverer [] i
  let doCmds cmds = do  
      forMseq_ cmds $ \cmd -> envExecCmd z2p z2a z2f clockChan pump cmd envExecABACmd

  let getEstByArb () = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (1,whichInp)
            --return (whichInp, idxs)
            return idxs
  let getAuxByArb () = do
            whichInp <- generateM arbitrary
            idxs <- getByFilter (2,whichInp)
            return (whichInp, idxs)
  
  let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
   
  c <- envQueueSize z2a clockChan 1000

  let inputs = do [return True, return False]
  let inputTokens = importAmt 
 
  ---- Randomly choose parition of True and False
  --pidsT <- selectPIDs honest
  --let pidsF = honest \\ pidsT

  let ptm = map (\x -> (x,True)) pidsT
  let pfm = map (\x -> (x,False)) pidsF
  let inputM = Map.fromList (ptm ++ pfm)

  -- STEP 1: choose honest inputs
  forMseq_ (ptm ++ pfm) $ \(p,i) -> do
    writeChan z2p $ (p, ((ClockP2F_Through i), SendTokens inputTokens))
    readChan pump

  -- INIT: deliver ESTs + crupt by partition
  c <- envQueueSize z2a clockChan 0
  estToT <- intersectM (estTrue ()) (getByReceivers pidsT)
  estToF <- intersectM (estFalse ()) (getByReceivers pidsF)
  doDelivers $ estToT ++ estToF

  -- similar structure for all rounds
  let rounds = 6
  forMseq_ [1..rounds] $ \r -> do
    -- STEP: give some PARTITION more EST from other bools
    partition <- selectPIDs honest
    forMseq_ partition $ \p -> do
      forp <- getByReceivers [p]
      --(b',ests) <- getEstByArb r
      ests <- getEstByArb ()
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
    auxs <- allAuxs () >>= generateM . shuffle
    --doDelivers auxs 
    cinpAuxs <- newIORef []
    forMseq_ crupts $ \cpid -> do
      --cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeSBCastSid parties cpid r) honest inputs r 64
      cinp <- liftIO $ generate $ vectorOf 10 $ abaAuxMsg (makeMainSid parties cpid r) honest inputs r 64
      modifyIORef cinpAuxs $ (++ (map Left cinp))
    cinpCmds <- readIORef cinpAuxs
    
    -- STEP: deliver adv AUX and delivery shuffled
    finalSet <- liftIO $ generate $ shuffle (cinpCmds ++ (map Right . map (\x -> (x,0)) $ deliverListAll $ auxs)) -- ++ ests))
    doCmds finalSet
    --forMseq_ finalSet $ \i -> do
    --  envExecCmd z2p z2a z2f clockChan pump i envExecABACmd
    -- STEP: deliver remaining ESTs
    ests <- allEsts () >>= generateM . shuffle
    doDelivers ests
    
    ---- deliver rest of round r messages
    yprint ("Giving rest of EST to all")
    yprint ("Looping environment " ++ show r)

  tr <- readIORef transcript
  cl <- readIORef cmdList
  ll <- readIORef leakLimited

  writeChan outp ((sid, parties, (Map.fromList cruptMapList), t), cl, tr, inputM, ll)

prop_RoundSafety abaVariant bcastVariant svalVariant roundBug binPtrBug auxBug supportInvert = monadicIO $ do
  let prot () = protABABreak (abaVariant, bcastVariant, svalVariant, roundBug, binPtrBug, auxBug, supportInvert)
  forAllM ( suchThat (partiesBetween 6 10) nonZeroParties) $ \ps -> do
    let ps = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"] --, "Gina", "Harry"]
    let t = length ps `div` 3
    forAllM (cruptFrom ps t) $ \cc -> do
      let honest = ps \\ cc
      pidsT <- selectPIDs honest
      let pidsF = honest \\ pidsT
      (config', c', t', inps, ll) <- run $ runITMinIO 120 $ execUC
        (testUEnvABANoRounds ps cc 100 10000 pidsT pidsF)
        --(testUEnvABAAdvEstAndAux ps cc 100 1000 pidsT pidsF)
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
prop_RoundSafetyCCC = quickCheckWithResult stdArgs{maxSuccess = 500} $ prop_RoundSafety ABACorrect  SBcastCorrect SBSCorrect ABARounds_Buggy ABABinPtr_Persist ABAAnyAux_Correct ABASupport_Correct

{- FAIL: These all fail safety check -}
prop_RoundSafetySSS = quickCheckWithResult stdArgs{maxSuccess = 1000}  $ prop_RoundSafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
--proRoundBASafetySSS = quickCheck $ prop_uABASafety ABASmall SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_RoundSafetySSC = quickCheck $ prop_RoundSafety ABASmall SBcastSmall SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_RoundSafetyCSS = quickCheck $ prop_RoundSafety ABACorrect SBcastSmall SBSSmall ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct
prop_RoundSafetySCC = quickCheck $ prop_RoundSafety ABASmall SBcastCorrect SBSCorrect ABARounds_Correct ABABinPtr_Persist ABAAnyAux_Any ABASupport_Correct

