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


data CoinFlipP2F m = FlipP2F_start | FlipP2F_m m deriving (Show, Eq)
data CoinFlipF2P m = FlipF2P_coin Bool | FlipF2P_m m deriving (Show, Eq)
--data CoinFlipA2F = FlipA2F_input deriving (Show, Eq)
--data CoinFlipF2A = FlipF2A_start PID deriving (Show, Eq)

-- TODO: should F2P output that the other party started?

fCoinFlipFair :: MonadFunctionalityAsync m (CoinFlipF2A) =>
  Functionality (CoinFlipP2F a) (CoinFlipF2P a) Void Void Void Void m --CoinFlipA2F CoinflipF2A Void Void m
fCoinFlipFair (p2f, f2p) _ _ = do
  let sid = ?sid :: SID
  let (pidA :: PID, pidB :: PID, sssid :: String) = readNote "fMulticast" $ snd sid
  startA <- newIORef False
  startB <- newIORef False
  forever $ do
    (pid, mf) <- readChan p2f
    case mf of
      FlipP2F_m m | pid == pidA -> eventually $ writeChan f2p (pidB, FlipF2P_m m)
                  | pid == pidB -> eventually $ writeChan f2p (pidA, FlipF2P_m m)
      FlipP2F_start -> do
        a <- readIORef startA 
        b <- readIORef startB
        if a && (pid == pidA) then writeIORef startA True
        else if b && (pid == pidB) then writeIORef startB True
        else error "Not A or B start msg"
        
        a <- readIORef startA
        b <- readIORef startB
        if a && b then do
          b <- ?getBit
          eventually $ writeChan f2p (pidA, FlipF2P_coin b)
          eventually $ writeChan f2p (pidB, FlipF2P_coin b)
        else return ()

data CoinFlipA2F = FlipA2F_DeliverA | FlipA2F_DeliverB deriving (Show, Eq)
data CoinFlipF2A = FlipF2A_Flip Bool deriving (Show, Eq)

fCoinFlipUnfair :: MonadFunctionalityAsync m (PID, CoinFlipP2F a) =>
  Functionality (CoinFlipP2F a) (CoinFlipF2P a) CoinFlipA2F CoinFlipF2A Void Void m
fCoinFlipUnfair (p2f, f2p) (a2f, f2a) _ = do
  let sid = ?sid :: SID
  let (pidA :: PID, pidB :: PID, sssid :: String) = readNote "fMulticast" $ snd sid
  startA <- newIORef False
  startB <- newIORef False
  ready <- newIORef False
  bit <- newIORef False
  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of
      FlipP2F_m m | pid == pidA -> writeChan f2p (pidB, FlipF2P_m m)
                  | pid == pidB -> writeChan f2p (pidA, FlipF2P_m m)
      FlipP2F_start -> do
        a <- readIORef startA 
        b <- readIORef startB
        if (not a) && (pid == pidA) then writeIORef startA True
        else if (not b) && (pid == pidB) then writeIORef startB True
        else error "Not A or B start msg"
        ?leak (pid, mf)
        
        a <- readIORef startA
        b <- readIORef startB
        if a && b then do
          b <- ?getBit
          writeIORef bit b
          writeIORef ready True
          writeChan f2a (FlipF2A_Flip b)
        else ?pass

  fork $ forever $ do
    m <- readChan a2f
    r <- readIORef ready
    b <- readIORef bit
    if r then do
      case m of
        -- we don't do eventually here because we don't want to deliver both eventually
        -- adv has complte control who gets any output
        FlipA2F_DeliverA -> writeChan f2p (pidA, FlipF2P_coin b)
        FlipA2F_DeliverB -> writeChan f2p (pidB, FlipF2P_coin b)
    else ?pass
  return ()

data RoP2F a b = RoP2F_Ro a | RoP2F_m b deriving (Show, Eq)
data RoF2P b = RoF2P_Ro Int | RoF2P_m b | RoF2P_Ok deriving (Show, Eq)

fTwoWayAndRO :: (Show a, MonadFunctionalityAsync m (PID, b)) => 
  Functionality (RoP2F a b) (RoF2P b) Void Void Void Void m
fTwoWayAndRO (p2f, f2p) _ _ = do
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read $ snd ?sid
  table <- newIORef Map.empty
  forever $ do
    (pid, mf) <- readChan p2f
    case mf of
      RoP2F_m m -> do
        if pid == pidS then do 
          ?leak (pid, m) 
          eventually $ writeChan f2p (pidR, RoF2P_m m)
          writeChan f2p (pid, RoF2P_Ok)
        else if pid == pidR then do
          ?leak (pid, m)
          eventually $ writeChan f2p (pidR, RoF2P_m m)
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
data ProtFlip_Msg = ProtFlip_commit Int | ProtFlip_bit Bool | ProtFlip_open Int Bool | ProtFlip_abort Int Bool deriving (Show, Eq)

protCoinFlipROUnfair :: MonadAsyncP m =>
  Protocol (ClockP2F (CoinFlipP2F ProtFlip_Msg)) (CoinFlipF2P ProtFlip_Msg) (RoF2P ProtFlip_Msg) (RoP2F (Int, Bool) ProtFlip_Msg) m
protCoinFlipROUnfair (z2p, p2z) (f2p, p2f) = do
  let (pidA :: PID, pidB :: PID, sssid :: String) = readNote "fMulticast" $ snd ?sid
  case () of
    _ | ?pid == pidA -> do
      readChan z2p -- Start
      -- choose a bit and commit to it in the random oracle
      b <- ?getBit
      nonce :: Int <- getNbits 120
      writeChan p2f $ RoP2F_Ro (nonce, b)
      mh <- readChan f2p
      let RoF2P_Ro h = mh
      -- send the hash to the other party and wait for its hash
      writeChan p2f $ RoP2F_m (ProtFlip_commit h)
      readChan p2f -- OK
      ?pass
      -- wait to receive the other party's bit
      mf <- readChan f2p
      let RoF2P_m (ProtFlip_bit b') = mf
      -- i can compute the coin flip now, send the opening to the other party so they can too
      writeChan p2f $ RoP2F_m (ProtFlip_open nonce b)
      readChan f2p -- OK
      -- compute and output the coin flip
      writeChan p2z (FlipF2P_coin $ (b' && not b) || (not b' && b))
    _ | ?pid == pidB -> do
      -- recieve the commit
      mf <- readChan f2p
      let RoF2P_m (ProtFlip_commit h) = mf
      -- send a bit
      b <- ?getBit
      writeChan p2f (RoP2F_m (ProtFlip_bit b))
      readChan f2p -- OK
      ?pass
      -- wait for opening
      mf <- readChan f2p
      let RoF2P_m (ProtFlip_open nonce' b') = mf
      -- check in RO
      writeChan p2f (RoP2F_Ro (nonce', b'))
      mh <- readChan f2p
      let RoF2P_Ro h' = mh
      if h == h' then writeChan p2z (FlipF2P_coin $ (b' && not b) || (not b' && b))
      else error "bad commitment"
  return ()

testEnvFlipIdeal :: MonadEnvironment m =>
  Environment (CoinFlipF2P ProtFlip_Msg) (ClockP2F (CoinFlipP2F ProtFlip_Msg))
               (SttCruptA2Z (CoinFlipF2P ProtFlip_Msg)
                           (Either (ClockF2A (PID, (CoinFlipP2F ProtFlip_Msg))) CoinFlipF2A))
               (SttCruptZ2A (ClockP2F (CoinFlipP2F ProtFlip_Msg))
                            (Either ClockA2F CoinFlipA2F))
               Void ClockZ2F () m
testEnvFlipIdeal z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestIdealFlip", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Alice",())])

  (lastOut, transcript, clockChan, _) <- envReadOut p2z a2z
  () <- readChan pump

  liftIO $ putStrLn $ "\nCrupt Alice Start"
  writeChan z2a $ (SttCruptZ2A_A2P ("Alice", (ClockP2F_Through $ FlipP2F_start)))
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
  writeChan z2p $ ("Bob", ClockP2F_Through $ FlipP2F_start)
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

--testEnvFlipIdeal :: MonadEnvironment m =>
--  Environment (CoinFlipF2P ProtFlip_Msg) (ClockP2F (CoinFlipP2F ProtFlip_Msg))
--              (SttCruptA2Z (RoF2P ProtFlip_Msg) 
--                           (Either (ClockF2A (PID, CoinFlipP2F a)) Void))
--              (SttCruptZ2A (ClockP2F (RoP2F (Int, Bool) ProtFlip_Msg))
--                           (Either ClockA2F Void))
--              Void ClockZ2F Void m
  


                                   

--
--  z2p' <- newChan
--  p2f' <- newChan
--  okChan <- newChan
--
--  -- pidA starts the flip and pidB responds
--  if ?pid == pidA then do
--    fork $ do
--      readChan z2p' -- Start
--      -- choose a bit and commit to it in the random oracle
--      b <- ?getBit
--      nonce :: Int <- getNBits 120
--      writeChan p2f $ RoP2F_Ro (nonce, b)
--      mh <- readChan f2p'
--      let RoF2P_Ro h = mh
--      -- send the hash to the other party and wait for its hash
--      writeChan p2f $ RoP2F_m (ProtFlip_commit h)
--      readChan okChan
--      -- wait to receive the other party's bit
--      ?pass
--      mf <- readChan f2p'
--      let ProtFlip_bit b' = mf
--      -- i can compute the coin flip now, send the opening to the other party so they can too
--      writeChan p2f $ RoP2F_m (ProtFlip_open nonce b)
--      readChan okChan
--      -- compute and output the coin flip
--      writeChan p2z (FlipF2P_coin (b' `xor` b))
--
--    fork $ forever $ do
--      (pid, m) <- readChan f2p 
--      case m of
--        RoF2P_OK -> writeChan okChan ()
--        RoF2P_m (ProtFlip_commit h) ->
--        RoF2P_m (ProtFlip_bit b) ->
--        RoF2P_
--        _ -> writeChan f2p'
--
--    fork $ forever $ do
--      m <- readChan z2p
--      case m of
--        FlipP2F_m m -> do
--          writeChan p2f m
--          readChan okChan
--        _ -> writeChan z2p' m
--          
--          
--  else if ?pid == pidB then do
--  else return ()
--  
--  fork $ forever $ do
--    m <- readChan z2p
--    case m of
--      FlipP2F_m m -> do
--        writeChan p2f m
--        readChan p2f -- Ok
--      FlipP2F_Start -> do
         


