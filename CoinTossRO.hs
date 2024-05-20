 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
 PartialTypeSignatures
  #-} 

module CoinTossRO where

import ProcessIO
import StaticCorruptions
import Async
import Multicast (forMseq_)
import Multisession
import TokenWrapper

import Safe
import Data.List (findIndex)
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM, liftM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map, (!))
import Test.QuickCheck.Monadic
import qualified Data.Map.Strict as Map

import TestTools (envReadOut, envMapQueue, intersect, deliverListAll, envQueueSize)

--data CoinFlipP2F m = FlipP2F_start | FlipP2F_m m deriving (Show, Eq)
--data CoinFlipF2P m = FlipF2P_coin Bool | FlipF2P_ok | FlipF2P_m m deriving (Show, Eq)
data CoinFlipP2F = FlipP2F_start deriving (Show, Eq)
data CoinFlipF2P = FlipF2P_coin Bool | FlipF2P_ok deriving (Show, Eq)

data ChanP2F a = ChanP2F_m a deriving (Show, Eq)
data ChanF2P a = ChanF2P_m a | ChanF2P_ok deriving (Show, Eq)

-- TODO: should F2P output that the other party started?
type CoinFlipTranscript a = [Either
                          (SttCruptA2Z (RoF2P (Either a ProtFlip_Msg))
                                       (Either (ClockF2A (PID, Either a ProtFlip_Msg)) Void))
                          (PID, Either CoinFlipF2P (ChanF2P a))]

data CoinFlipA2F a = FlipA2F_DeliverA | FlipA2F_DeliverB | FlipA2F_Deliver PID a deriving (Show, Eq)
data CoinFlipF2A = FlipF2A_Flip Bool deriving (Show, Eq)

fCoinFlipUnfair :: (Eq a, Show a, MonadFunctionalityAsync m (PID, Either CoinFlipP2F (ChanP2F a))) =>
  Functionality (Either CoinFlipP2F (ChanP2F a)) (Either CoinFlipF2P (ChanF2P a))
                (CoinFlipA2F a) CoinFlipF2A Void Void m
fCoinFlipUnfair (p2f, f2p) (a2f, f2a) _ = do
  let sid = ?sid :: SID
  let (pidA :: PID, pidB :: PID, sssid :: String) = readNote "fMulticast" $ snd sid
  startA <- newIORef False
  startB <- newIORef False
  ready <- newIORef False
  bit <- newIORef False

  msgChan :: Chan (PID, ChanP2F a) <- newChan
  funcChan :: Chan (PID, CoinFlipP2F) <- newChan
  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of
      Left m -> writeChan funcChan (pid, m)
      Right m -> writeChan msgChan (pid, m)

  fork $ forever $ do
    (pid, FlipP2F_start) <- readChan funcChan
    a <- readIORef startA 
    b <- readIORef startB
    if not a && (pid == pidA) then writeIORef startA True
    else if not b && (pid == pidB) then writeIORef startB True
    else error "Not A or B start msg"
    ?leak (pid, Left FlipP2F_start)
    
    a <- readIORef startA
    b <- readIORef startB
    if a && b then do
      b <- ?getBit
      writeIORef bit b
      writeIORef ready True
    else return ()
    writeChan f2p (pid, Left FlipF2P_ok)

  fork $ forever $ do
    (pid, ChanP2F_m m) <- readChan msgChan 
    ?leak (pid, Right $ ChanP2F_m m)
    case () of
      _ | pid == pidA -> eventually $ writeChan f2p (pidB, Right $ ChanF2P_m m)
      _ | pid == pidB -> eventually $ writeChan f2p (pidA, Right $ ChanF2P_m m)
    writeChan f2p (pid, Right ChanF2P_ok)

  fork $ forever $ do
    m <- readChan a2f
    case m of
        FlipA2F_Deliver pidR m | pidR == pidA -> 
                                   if (member pidB ?crupt) then writeChan f2p (pidR, Right $ ChanF2P_m m) else error "pidB not crupt"
                               | pidR == pidB ->
                                   if (member pidA ?crupt) then writeChan f2p (pidR, Right $ ChanF2P_m m) else error "pidA ot crupt"
        _ -> do
          r <- readIORef ready
          b <- readIORef bit
          if r then do
            case m of
              -- we don't do eventually here because we don't want to deliver both eventually
              -- adv has complte control who gets any output
              FlipA2F_DeliverA -> writeChan f2p (pidA, Left $ FlipF2P_coin b)
              FlipA2F_DeliverB -> writeChan f2p (pidB, Left $ FlipF2P_coin b)
          else ?pass
  return ()

--
makeSyncLog handler req = do
  ctr <- newIORef 0
  let syncLog = do
        log <- req
        t <- readIORef ctr
        let tail = drop t log
        modifyIORef ctr (+ length tail)
        forM tail handler
        return ()
  return syncLog
--

simFlip :: (Show a, Eq a, MonadAdversary m) => Adversary 
  (SttCruptZ2A (ClockP2F (RoP2F (Int, Bool) (Either a ProtFlip_Msg)))   -- z2a
               (Either ClockA2F Void))
  (SttCruptA2Z (RoF2P (Either a ProtFlip_Msg))
               (Either (ClockF2A (PID, Either a ProtFlip_Msg)) Void))   -- a2z
  (Either CoinFlipF2P (ChanF2P a)) (ClockP2F (Either CoinFlipP2F (ChanP2F a)))   -- p2a, a2p
  (Either (ClockF2A (PID, Either CoinFlipP2F (ChanP2F a))) CoinFlipF2A)   -- f2a
  (Either ClockA2F (CoinFlipA2F a)) m   -- a2f
simFlip (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  let sid = ?sid :: SID
  let (pidA :: PID, pidB :: PID, sssid :: String) = readNote "fMulticast" $ snd sid

  a2s <- newChan
  a2r <- newChan
  
  table <- newIORef (Map.empty :: (Map (Int, Bool) Int))
  backtable <- newIORef (Map.empty :: (Map Int (Int, Bool)))
  comh <- newIORef Nothing

  z2a' <- newChan
  --fork $ forever $ do
  --  mh <- readChan z2a
  --  liftIO $ putStrLn $ "sim: readChhan on z2a"
  --  case mh of 
  --    SttCruptZ2A_A2P (pid, m) | pid == pidA -> do
  --                                liftIO $ putStrLn $ "sim: z2a a2p A : " ++ show m
  --                                writeChan a2s m
  --                             | pid == pidB -> do
  --                                liftIO $ putStrLn $ "sim: z2a a2p B : " ++ show m
  --                                writeChan a2r m
  --    _ -> writeChan z2a' mh
  --    -- the Right of the case is Void so we don't care about it
        
  let functionality (p2f', f2p') (a2f', f2a') (z2f', f2z') = do
            fork $ forever $ do
              (pid, mf) <- readChan p2f'
              liftIO $ putStrLn $ "sim_F: message " ++ show mf
              case mf of
                RoP2F_Ro (nonce, b) -> do
                  liftIO $ putStrLn $ "sim: RO request " ++ show (pid, mf)
                  tbl <- readIORef table
                  if not $ member (nonce, b) tbl then do
                    h :: Int <- getNbits 120
                    modifyIORef table     (Map.insert (nonce,b) h)
                    modifyIORef backtable (Map.insert h (nonce,b)) 
                  else return ()
                  tbl <- readIORef table
                  writeChan f2p' (pid, RoF2P_Ro (tbl ! (nonce, b)))
                  --writeChan a2 (SttCruptA2Z_P2A (pidA, RoF2P_Ro (tbl ! (nonce, b))))
                RoP2F_m m -> do
                  if pid == pidA then do 
                    ?leak (pid, m) 
                    eventually $ writeChan f2p' (pidB, RoF2P_m m)
                    writeChan f2p' (pid, RoF2P_Ok)
                  else if pid == pidB then do
                    ?leak (pid, m)
                    eventually $ writeChan f2p' (pidA, RoF2P_m m)
                    writeChan f2p' (pid, RoF2P_Ok)
                  else ?pass
            return ()

  sbxp2z <- newChan
  sbxz2p <- newChan
  sbxz2f <- newChan
  sbxpump <- newChan
  sbxa2z <- newChan
  chanOk <- newChan
  deliverList <- newIORef ([] :: [(PID, a)])
  

  let sbxEnv z2exec (p2z', z2p') (a2z', z2a') (f2z', z2f') pump' outp' = do
          liftIO $ putStrLn $ "Going to write crup to sim execuc"
          writeChan z2exec $ SttCrupt_SidCrupt ?sid ?crupt
          -- if sender is crupt: simulator outputs random bit received by the receiver and that's it
          -- also wait wait for the simulation to output and then make the crupt sender also init

          forward p2z' sbxp2z
          forward sbxz2p z2p'

          forward z2a z2a'
          --forward a2z' a2z
          forward a2z' sbxa2z
  
          forward sbxz2f z2f'
          
          forward pump' sbxpump
    
          return ()

  fork $ forever $ do
    mf <- readChan sbxa2z
    liftIO $ putStrLn $ "sbza2z " ++ show mf
    case mf of
      SttCruptA2Z_P2A (_pid, RoF2P_m (Left m)) -> do
        res <- readIORef deliverList >>= return . findIndex (==(if _pid==pidA then pidB else pidA, m))
        let (Just idx) = res 
        modifyIORef deliverList (deleteNth idx)
        writeChan a2f (Left $ ClockA2F_Deliver idx)
        (pid', mp) <- readChan p2a
        let Right (ChanF2P_m m) = mp
        writeChan a2z mf
      _ -> writeChan a2z mf

  let handleLeak (pid, m) = do
            if member pid ?crupt then return ()
            else do
              case m of
                Left FlipP2F_start -> do
                  -- give start to the internal pid as well
                  liftIO $ putStrLn $ "sim: start leak for " ++ show pid
                  writeChan sbxz2p (pid, ClockP2F_Through $ Left FlipP2F_start)
                  readChan chanOk
                  -- this always results in a ?pass
                Right (ChanP2F_m m') -> do
                  -- add this message to the list
                  modifyIORef deliverList (++ [(pid, m')])
                  -- send the message in the simulation as well
                  liftIO $ putStrLn $ "******sim: send msg"
                  writeChan sbxz2p (pid, ClockP2F_Through $ Right (ChanP2F_m m'))
                  readChan chanOk
                _ -> error "shouldn't ever be leaked"
            return ()

  syncLeaks <- makeSyncLog handleLeak $ do
      writeChan a2f $ (Left ClockA2F_GetLeaks)
      mf <- readChan f2a

      let Left (ClockF2A_Leaks leaks) = mf
      return leaks

  let sbxAdv (z2a', a2z') (p2a', a2p') (f2a', a2f') = do
          fork $ forever $ do
            mf <- readChan z2a'
            printAdv $ "Intercepted z2a' " ++ show mf
            syncLeaks
            printAdv $ "forwarding into the sandbox" 
            case mf of
              SttCruptZ2A_A2F f -> do
                liftIO $ putStrLn $ "z2a_a2f " ++ show f
                writeChan a2f' f
              SttCruptZ2A_A2P pm -> do
                liftIO $ putStrLn $ "z2a_a2p " ++ show pm
                writeChan a2p' pm
          fork $ forever $ do
            m <- readChan f2a'
            liftIO $ putStrLn $ "f2a' " ++ show m
            writeChan a2z' $ SttCruptA2Z_F2A m
          fork $ forever $ do
            (pid, m) <- readChan p2a'
            liftIO $ putStrLn $ "p2a' " ++ show m
            writeChan a2z' $ SttCruptA2Z_P2A (pid, m)
          return ()

  if member pidA ?crupt then do
    -- if the sender is crupt only simulate the bit that was received from honest receiver
    fork $ forever $ do
      (_pidB, mf) <- readChan sbxp2z
      case mf of 
        Left (FlipF2P_coin b) -> do
          -- implies honest party has already started
          writeChan a2p (pidA, ClockP2F_Through $ Left FlipP2F_start)
          -- this write results in f2a write from functionality
          ma <- readChan p2a
          --let (pidB, FlipF2P_ok) = ma
          let (pidB, Left FlipF2P_ok) = ma
          -- not we deliver pidB
          writeChan a2f (Right FlipA2F_DeliverB)
        Left (FlipF2P_ok) -> writeChan chanOk ()
        Right ChanF2P_ok -> writeChan chanOk ()
        Right (ChanF2P_m m) -> do
          liftIO $ putStrLn $ "receives message from pidB " ++ show m
          writeChan a2f $ Right $ FlipA2F_Deliver pidB m
      return ()
    return ()
  else if member pidB ?crupt then do
    fork $ forever $ do
      (_pidA, mf) <- readChan sbxp2z
      case mf of 
        Left (FlipF2P_coin b) -> do
          writeChan a2p (pidB, ClockP2F_Through $ Left FlipP2F_start)
          ma <- readChan p2a
          let (pidA, Left FlipF2P_ok) = ma
          writeChan a2f (Right FlipA2F_DeliverA)
        Left FlipF2P_ok -> writeChan chanOk ()
        Right ChanF2P_ok -> writeChan chanOk ()
        Right (ChanF2P_m m) -> do
          liftIO $ putStrLn $ "receives message from pidA " ++ show m
          writeChan a2f $ Right $ FlipA2F_Deliver pidA m
    return ()
  else do
    -- at this point, the simulator has been activated for delivery of all the messages
    -- handleLeak ensures that the simulation has been started and that the parties have been started
    -- all you have to do now is wait to see which returns and deliver the message
    fork $ forever $ do
      (_pid, mf) <- readChan sbxp2z
      liftIO $ putStrLn $ "sim: readChan sbxp2z"
      case mf of 
        Left (FlipF2P_coin b) -> do
          -- deliver to _pid
          case () of  
            _ | _pid == pidA -> writeChan a2f (Right FlipA2F_DeliverA) 
            _ | _pid == pidB -> writeChan a2f (Right FlipA2F_DeliverB) 
        Left FlipF2P_ok -> writeChan chanOk ()
        Right ChanF2P_ok -> writeChan chanOk ()
        Right (ChanF2P_m m) -> do
          res <- readIORef deliverList >>= return . findIndex (==(if _pid==pidA then pidB else pidA, m))
          let (Just idx) = res
          modifyIORef deliverList (deleteNth idx)
          writeChan a2f (Left $ ClockA2F_Deliver idx)
      return ()
    return ()
        
  -- we need to wait write token to finish init
  mf <- selectRead z2a f2a
  liftIO $ putStrLn $ "sim: got activation to init"
  
  let sbxProt () = protCoinFlipROUnfair
  let sbxF () = fTwoWayAndRO

  fork $ execUC_ sbxEnv (runAsyncP $ sbxProt ()) (runAsyncF $ sbxF ()) sbxAdv
  () <- readChan sbxpump
  liftIO $ putStrLn $ "init'd simulation"

  case mf of
    Left m -> writeChan z2a m
    Right m -> writeChan f2a m

  fork $ forever $ do
    () <- readChan sbxpump
    liftIO $ putStrLn $ "Reading pump in sim"
    writeChan a2z (SttCruptA2Z_F2A $ Left ClockF2A_Pass)
    return ()

  return ()
--
testFlipSimHonest :: IO ()
testFlipSimHonest = runITMinIO 120 $ do
  treal <- execUC
        testEnvFlipRealHonest
        (runAsyncP $ protCoinFlipROUnfair)
        (runAsyncF $ fTwoWayAndRO)
        dummyAdversary
  tideal <- execUC
        testEnvFlipRealHonest
        idealProtocol
        (runAsyncF $ fCoinFlipUnfair)
        simFlip
  liftIO $ putStrLn $ "\nReal transcript: \n" ++ show treal
  liftIO $ putStrLn $ "\nIdeal Transcript: \n" ++ show tideal
--
testFlipSimCruptSender :: IO ()
testFlipSimCruptSender = runITMinIO 120 $ do
  treal <- execUC
        testEnvFlipRealCruptSender
        (runAsyncP $ protCoinFlipROUnfair)
        (runAsyncF $ fTwoWayAndRO)
        dummyAdversary
  tideal <- execUC
        testEnvFlipRealCruptSender
        idealProtocol 
        (runAsyncF $ fCoinFlipUnfair)
        simFlip
  liftIO $ putStrLn $ "\nReal transcript: \n" ++ show treal
  liftIO $ putStrLn $ "\nIdeal transcript: \n" ++ show tideal

testFlipSimCruptReceiver :: IO ()
testFlipSimCruptReceiver = runITMinIO 120 $ do
  treal <- execUC
        testEnvFlipRealCruptReceiver
        (runAsyncP $ protCoinFlipROUnfair)
        (runAsyncF $ fTwoWayAndRO)
        dummyAdversary
  tideal <- execUC
        testEnvFlipRealCruptReceiver
        idealProtocol 
        (runAsyncF $ fCoinFlipUnfair)
        simFlip
  liftIO $ putStrLn $ "\nReal transcript: \n" ++ show treal
  liftIO $ putStrLn $ "\nIdeal transcript: \n" ++ show tideal


testEnvFlipIdeal :: MonadEnvironment m =>
  Environment (Either CoinFlipF2P (ChanF2P String)) (ClockP2F (Either CoinFlipP2F (ChanP2F String)))
              (SttCruptA2Z (Either CoinFlipF2P (ChanF2P String))
                           (Either (ClockF2A (PID, Either CoinFlipP2F (ChanP2F String))) CoinFlipF2A))
              (SttCruptZ2A (ClockP2F (Either CoinFlipP2F (ChanP2F String)))
                           (Either ClockA2F (CoinFlipA2F a)))
              Void ClockZ2F () m
--  Environment (CoinFlipF2P ProtFlip_Msg) (ClockP2F (CoinFlipP2F ProtFlip_Msg))
--               (SttCruptA2Z (CoinFlipF2P ProtFlip_Msg)
--                            (Either (ClockF2A (PID, (CoinFlipP2F ProtFlip_Msg))) CoinFlipF2A))
--               (SttCruptZ2A (ClockP2F (CoinFlipP2F ProtFlip_Msg))
--                            (Either ClockA2F CoinFlipA2F))
--               Void ClockZ2F () m
testEnvFlipIdeal z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestIdealFlip", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Alice",())])

  (lastOut, transcript, clockChan, _) <- envReadOut p2z a2z
  () <- readChan pump

  liftIO $ putStrLn $ "\nCrupt Alice Start"
  writeChan z2a $ (SttCruptZ2A_A2P ("Alice", (ClockP2F_Through $ Left FlipP2F_start)))
  () <- readChan pump

  writeChan z2p $ ("Bob", ClockP2F_Through $ Right $ ChanP2F_m "hello")
  () <- readChan pump

  writeChan z2a $ (SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks)
  () <- readChan pump

  l <- readIORef lastOut
  liftIO $ putStrLn $ "Last out: " ++ show l

  -- try early deliver
  liftIO $ putStrLn $ "\nTrying to deliver early, last out should be unchanged"
  writeChan z2a $ (SttCruptZ2A_A2F $ Right FlipA2F_DeliverA)
  () <- readChan pump
  l' <- readIORef lastOut
  -- they should be the same
  liftIO $ putStrLn $ "Last out: " ++ show l'

  -- Bob honest input
  liftIO $ putStrLn $ "\nBob start"
  writeChan z2p $ ("Bob", ClockP2F_Through $ Left FlipP2F_start)
  () <- readChan pump
  writeChan z2a $ (SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks)
  () <- readChan pump

  l <- readIORef lastOut
  liftIO $ putStrLn $ "Last out: " ++ show l

  -- actually deliver now
  liftIO $ putStrLn $ "\nDelivering to A"
  writeChan z2a $ (SttCruptZ2A_A2F $ Right FlipA2F_DeliverA)
  () <- readChan pump

  l <- readIORef lastOut
  liftIO $ putStrLn $ "Last out: " ++ show l

  liftIO $ putStrLn $ "\nDelivering to B"
  writeChan z2a $ (SttCruptZ2A_A2F $ Right FlipA2F_DeliverB)
  () <- readChan pump

  l <- readIORef lastOut
  liftIO $ putStrLn $ "Last out: " ++ show l

  writeChan outp ()

testFlipIdeal :: IO ()
testFlipIdeal = runITMinIO 120 $ execUC
  testEnvFlipIdeal
  idealProtocol
  (runAsyncF $ fCoinFlipUnfair)
  dummyAdversary


{----------------}
{-  Real World  -}
{----------------}

data RoP2F a b = RoP2F_Ro a | RoP2F_m b deriving (Show, Eq)
data RoF2P b = RoF2P_Ro Int | RoF2P_m b | RoF2P_Ok deriving (Show, Eq)

fTwoWayAndRO :: (Show a, Show b, MonadFunctionalityAsync m (PID, b)) => 
  Functionality (RoP2F a b) (RoF2P b) Void Void Void Void m
fTwoWayAndRO (p2f, f2p) _ _ = do
  let (pidS :: PID, pidR :: PID, ssid :: String) = readNote "fTwoWayAndRO" $ snd ?sid
  table <- newIORef Map.empty
  forever $ do
    (pid, mf) <- readChan p2f
    case mf of
      RoP2F_m m -> do
        liftIO $ putStrLn $ "msg send " ++ show (pid, mf) 
        if pid == pidS then do 
          liftIO $ putStrLn $ "pidS"
          ?leak (pid, m) 
          eventually $ writeChan f2p (pidR, RoF2P_m m)
          writeChan f2p (pid, RoF2P_Ok)
        else if pid == pidR then do
          liftIO $ putStrLn $ "pidR"
          ?leak (pid, m)
          eventually $ writeChan f2p (pidS, RoF2P_m m)
          writeChan f2p (pid, RoF2P_Ok)
        else ?pass
      RoP2F_Ro m -> do
        tbl <- readIORef table
        if member (show m) tbl then writeChan f2p (pid, RoF2P_Ro (tbl ! show m))
        else do
          h <- getNbits 120
          modifyIORef table (Map.insert (show m) h)
          writeChan f2p (pid, RoF2P_Ro h)
          

-- pidA clips a coin to pidB
data ProtFlip_Msg = ProtFlip_commit Int | ProtFlip_bit Bool | ProtFlip_open Int Bool | ProtFlip_abort deriving (Show, Eq)

protCoinFlipROUnfair :: (Show a, MonadAsyncP m) =>
  Protocol (ClockP2F (Either CoinFlipP2F (ChanP2F a))) (Either CoinFlipF2P (ChanF2P a))
           (RoF2P (Either a ProtFlip_Msg)) (RoP2F (Int, Bool) (Either a ProtFlip_Msg)) m
  --Protocol (ClockP2F (CoinFlipP2F ProtFlip_Msg)) (CoinFlipF2P ProtFlip_Msg) (RoF2P ProtFlip_Msg) (RoP2F (Int, Bool) ProtFlip_Msg) m
protCoinFlipROUnfair (z2p, p2z) (f2p, p2f) = do
  let (pidA :: PID, pidB :: PID, sssid :: String) = readNote "fMulticast" $ snd ?sid

  msgChan :: Chan (ChanP2F a) <- newChan
  protChan :: Chan CoinFlipP2F <- newChan
  fork $ forever $ do
    mf <- readChan z2p
    case mf of
      ClockP2F_Pass -> ?pass
      ClockP2F_Through (Left m) -> writeChan protChan m
      ClockP2F_Through (Right m) -> writeChan msgChan m

  --toProt :: Chan (RoF2P (Either Void ProtFlip_Msg)) <- newChan
  toProt :: Chan (RoF2P ProtFlip_Msg) <- newChan
  okChan <- newChan
  fork $ forever $ do
    mf <- readChan f2p
    liftIO $ putStrLn $ "party [" ++ show ?pid ++ "] m: " ++ show mf
    case mf of
      RoF2P_Ok -> writeChan okChan ()
      RoF2P_m (Left m) -> writeChan p2z $ Right (ChanF2P_m m)
      RoF2P_m (Right m) -> writeChan toProt $ RoF2P_m m
      RoF2P_Ro h -> writeChan toProt $ RoF2P_Ro h

  fork $ forever $ do
    (ChanP2F_m m) <- readChan msgChan
    liftIO $ putStrLn $ "msgChan read: " ++ show m 
    writeChan p2f (RoP2F_m $ Left m)
    readChan okChan
    writeChan p2z $ Right ChanF2P_ok
    -- ?pass

  case () of
    _ | ?pid == pidA -> do
      FlipP2F_start <- readChan protChan
      liftIO $ putStrLn $ "Started pidA"
      -- choose a bit and commit to it in the random oracle
      b <- ?getBit
      nonce :: Int <- getNbits 120
      liftIO $ putStrLn $ "Alice: querying Ro"
      writeChan p2f $ RoP2F_Ro (nonce, b)
      m' <- readChan toProt
      let (RoF2P_Ro h) = m'
      liftIO $ putStrLn $ "Alice: sending commit"
      writeChan p2f $ RoP2F_m (Right $ ProtFlip_commit h)
      readChan okChan
      writeChan p2z $ Left FlipF2P_ok
      m' <- readChan toProt
      let RoF2P_m (ProtFlip_bit b') = m'
      liftIO $ putStrLn $ "Alice: sending open"
      writeChan p2f $ RoP2F_m (Right $ ProtFlip_open nonce b)
      readChan okChan
      writeChan p2z (Left $ FlipF2P_coin $ (b' && not b) || (not b' && b)) 
    _ | ?pid == pidB -> do
      m' <- readChan protChan
      let FlipP2F_start = m'
      liftIO $ putStrLn $ "Started pidB"
      writeChan p2z $ Left FlipF2P_ok
      -- recieve the commit
      m' <- readChan toProt
      let RoF2P_m (ProtFlip_commit h) = m'
      liftIO $ putStrLn $ "Bob: received commitment: " ++ show h  
      -- send a bit
      b <- ?getBit
      liftIO $ putStrLn $ "Bob: sending bit: " ++ show b
      writeChan p2f (RoP2F_m (Right $ ProtFlip_bit b))
      readChan okChan
      ?pass
      -- wait for opening
      mf <- readChan toProt
      case mf of
        RoF2P_m (ProtFlip_open nonce' b') -> do
          liftIO $ putStrLn $ "Received open: " ++ show nonce' ++ " " ++ show b'
          -- check in RO
          writeChan p2f (RoP2F_Ro (nonce', b'))
          m' <- readChan toProt
          let RoF2P_Ro h' = m'
          if h == h' then do
            liftIO $ putStrLn $ "Bob: verified the bit correctly"
            writeChan p2z (Left $ FlipF2P_coin $ (b' && not b) || (not b' && b))
          else error "bad commitment"
        RoF2P_m (ProtFlip_abort) -> do
          -- make the flip myself
          b' <- ?getBit
          writeChan p2z (Left $ FlipF2P_coin b')

  return ()


testEnvFlipRealHonest :: MonadEnvironment m =>
  Environment (Either CoinFlipF2P (ChanF2P String)) (ClockP2F (Either CoinFlipP2F (ChanP2F String)))
              (SttCruptA2Z (RoF2P (Either String ProtFlip_Msg))
                           (Either (ClockF2A (PID, Either String ProtFlip_Msg)) Void))
              (SttCruptZ2A (ClockP2F (RoP2F (Int, Bool) (Either String ProtFlip_Msg)))
                           (Either ClockA2F Void))
              Void ClockZ2F (CoinFlipTranscript String) m
testEnvFlipRealHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestIdealFlip", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

  (lastOut, transcript, clockChan, _) <- envReadOut p2z a2z
  cmdList <- newIORef []
  () <- readChan pump

  writeChan z2p ("Alice", ClockP2F_Through $ Left FlipP2F_start)
  () <- readChan pump

  writeChan z2p ("Bob", ClockP2F_Through $ Left FlipP2F_start)
  () <- readChan pump

  -- deliver Alice's commitment
  liftIO $ putStrLn $ "\nZ: deliver Alice's commitment"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  writeChan z2p ("Alice", ClockP2F_Through $ Right (ChanP2F_m "hello"))
  () <- readChan pump

  liftIO $ putStrLn $ "\nZ: deliver hello msg"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  liftIO $ putStrLn $ "\nZ: deliver Bob's bit" 
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  liftIO $ putStrLn $ "\nZ: deliver Alice's opening"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks
  () <- readChan pump

  readIORef transcript >>= writeChan outp 

testFlipRealHonest :: IO (CoinFlipTranscript String)
testFlipRealHonest = runITMinIO 120 $ execUC
  testEnvFlipRealHonest
  (runAsyncP $ protCoinFlipROUnfair)
  (runAsyncF $ fTwoWayAndRO)
  dummyAdversary

testEnvFlipRealCruptReceiver :: MonadEnvironment m =>
  Environment (Either CoinFlipF2P (ChanF2P String)) (ClockP2F (Either CoinFlipP2F (ChanP2F String)))
              (SttCruptA2Z (RoF2P (Either String ProtFlip_Msg))
                           (Either (ClockF2A (PID, Either String ProtFlip_Msg)) Void))
              (SttCruptZ2A (ClockP2F (RoP2F (Int, Bool) (Either String ProtFlip_Msg)))
                           (Either ClockA2F Void))
              Void ClockZ2F (CoinFlipTranscript String) m
testEnvFlipRealCruptReceiver z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestIdealFlip", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Bob",())])

  (lastOut, transcript, clockChan, _) <- envReadOut p2z a2z
  cmdList <- newIORef []
  () <- readChan pump

  writeChan z2p ("Alice", ClockP2F_Through $ Left FlipP2F_start)
  () <- readChan pump

  -- deliver Alice's commitment
  liftIO $ putStrLn $ "\nZ: deliver Alice's commitment"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  writeChan z2a $ (SttCruptZ2A_A2P ("Bob", ClockP2F_Through $ RoP2F_m (Left "Hello")))
  --writeChan z2p ("Alice", ClockP2F_Through $ Right (ChanP2F_m "Hello"))
  () <- readChan pump
  
  -- send Alice the same bit all the time
  liftIO $ putStrLn $ "\nZ: give Alice a bit"
  writeChan z2a $ SttCruptZ2A_A2P ("Bob", ClockP2F_Through $ RoP2F_m $ Right $ ProtFlip_bit True)
  () <- readChan pump

  liftIO $ putStrLn $ "\nZ: deliver Bob's bit"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  -- deliver Bob's bit
  liftIO $ putStrLn $ "\nZ: deliver Bob's bit"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump
 
  readIORef transcript >>= writeChan outp 

testFlipRealCruptReceiver :: IO (CoinFlipTranscript String)
testFlipRealCruptReceiver = runITMinIO 120 $ execUC
  testEnvFlipRealCruptReceiver
  (runAsyncP $ protCoinFlipROUnfair)
  (runAsyncF $ fTwoWayAndRO)
  dummyAdversary


testEnvFlipRealCruptSender :: MonadEnvironment m =>
  Environment (Either CoinFlipF2P (ChanF2P String)) (ClockP2F (Either CoinFlipP2F (ChanP2F String)))
              (SttCruptA2Z (RoF2P (Either String ProtFlip_Msg))
                           (Either (ClockF2A (PID, Either String ProtFlip_Msg)) Void))
              (SttCruptZ2A (ClockP2F (RoP2F (Int, Bool) (Either String ProtFlip_Msg)))
                           (Either ClockA2F Void))
              Void ClockZ2F (CoinFlipTranscript String) m
testEnvFlipRealCruptSender z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestIdealFlip", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Alice",())])

  (lastOut, transcript, clockChan, _) <- envReadOut p2z a2z
  cmdList <- newIORef []
  () <- readChan pump

  writeChan z2p ("Bob", ClockP2F_Through $ Left FlipP2F_start)
  () <- readChan pump

  -- generate a commitment
  b <- ?getBit
  nonce :: Int <- getNbits 120
  writeChan z2a $ (SttCruptZ2A_A2P ("Alice", ClockP2F_Through $ RoP2F_Ro (nonce, b)))
  () <- readChan pump

  mh <- readIORef lastOut
  let Just (Left (SttCruptA2Z_P2A ("Alice", RoF2P_Ro h))) = mh

  --writeChan z2a $ (SttCruptZ2A_A2P ("Alice", ClockP2F_Through $ RoP2F_m (Left "Hello")))
  writeChan z2p ("Bob", ClockP2F_Through $ Right (ChanP2F_m "Hello"))
  () <- readChan pump

  liftIO $ putStrLn $ "\nZ: commitment: " ++ show h
  writeChan z2a $ (SttCruptZ2A_A2P ("Alice", ClockP2F_Through $ RoP2F_m (Right $ ProtFlip_commit h)))
  () <- readChan pump

  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  ---- deliver Alice's commitment
  liftIO $ putStrLn $ "\nZ: deliver Alice's commitment"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  liftIO $ putStrLn $ "\nZ: deliver Bob's bit" 
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  mh <- readIORef lastOut
  liftIO $ putStrLn $ show mh
  let Just (Left (SttCruptA2Z_P2A ("Alice", RoF2P_m (Right (ProtFlip_bit b'))))) = mh

  let resultFlip = (b && not b') || (not b && b')
  liftIO $ putStrLn $ "\nZ: resultflip: " ++ show resultFlip
  if resultFlip == False then
    writeChan z2a $ SttCruptZ2A_A2P ("Alice", ClockP2F_Through $ RoP2F_m (Right $ ProtFlip_abort))
  else writeChan z2a $ SttCruptZ2A_A2P ("Alice", ClockP2F_Through $ RoP2F_m (Right $ ProtFlip_open nonce b))
  () <- readChan pump

  -- deliver this message
  liftIO $ putStrLn $ "\nZ: deliver the final message"
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  () <- readChan pump

  --l <- readIORef lastOut
  --let Just (Right ("Bob", Left (FlipF2P_coin flip))) = l

  --liftIO $ putStrLn $ "\nZ: deliver Alice's opening"
  --writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  --() <- readChan pump

  --writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks
  --() <- readChan pump
  
  readIORef transcript >>= writeChan outp

testFlipRealCruptSender :: IO (CoinFlipTranscript String)
testFlipRealCruptSender = runITMinIO 120 $ execUC
  testEnvFlipRealCruptSender
  (runAsyncP $ protCoinFlipROUnfair)
  (runAsyncF $ fTwoWayAndRO)
  dummyAdversary
