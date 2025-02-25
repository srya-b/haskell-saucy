{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-} 
{-# LANGUAGE PartialTypeSignatures #-}

module Multicast where

import ProcessIO
import StaticCorruptions
import Multisession
import Async
import TokenWrapper

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

{- fMulticast: a multicast functionality -}

forMseq_ xs f = sequence_ $ map f xs

data MulticastF2P a = MulticastF2P_OK | MulticastF2P_Deliver a deriving (Show, Eq)
data MulticastF2A a = MulticastF2A a deriving (Show, Eq)
data MulticastA2F a = MulticastA2F_Deliver PID a deriving Show

fMulticast :: MonadFunctionalityAsync m t =>
  Functionality t (MulticastF2P t) (MulticastA2F t) (MulticastF2A t) Void Void m
fMulticast (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender and set of parties is encoded in SID
  let sid = ?sid :: SID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticast" $ snd sid

  if not $ member pidS ?crupt then
      -- Only activated by the designated sender
      fork $ forever $ do
        (pid, m) <- readChan p2f
        liftIO $ putStrLn $ "\n\nreceived a message to be multicast\n\n"
        if pid == pidS then do
          ?leak m
          forMseq_ parties $ \pidR -> do
             eventually $ do 
               liftIO $ putStrLn $ "sending a deliver message to " ++ show pidR
               writeChan f2p (pidR, MulticastF2P_Deliver m)
          writeChan f2p (pidS, MulticastF2P_OK)
        else error "multicast activated not by sender"
  else do
      -- If sender is corrupted, arbitrary messages can be delivered (once) to parties in any order
      delivered <- newIORef (empty :: Map PID ())
      fork $ forever $ do
         MulticastA2F_Deliver pidR m <- readChan a2f
         del <- readIORef delivered
         if member pidR del then return () 
         else do
           writeIORef delivered (insert pidR () del)
           writeChan f2p (pidR, MulticastF2P_Deliver m)
  return ()

fMulticastToken :: MonadFunctionalityAsync m ((t, TransferTokens Int), CarryTokens Int) =>
  Functionality ((t, TransferTokens Int), CarryTokens Int) (MulticastF2P t, TransferTokens Int)
                (MulticastA2F t, TransferTokens Int) (MulticastF2A t, TransferTokens Int) Void Void m
fMulticastToken (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender and set of parties is encoded in SID
  let sid = ?sid :: SID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticast" $ snd sid
  let n = length parties 

  tokens <- newIORef 0
  totalTokens <- newIORef 0
  totalMessages <- newIORef 0
  
  let require cond msg = 
        if not cond then do
          liftIO $ putStrLn $ msg
          ?pass
          readChan =<< newChan
        else return ()


  if not $ member pidS ?crupt then
      -- Only activated by the designated sender
      fork $ forever $ do
        (pid, ((m, DeliverTokensWithMessage st), SendTokens a)) <- readChan p2f
        modifyIORef totalMessages $ (+) n
        if a>=0 then do
          tk <- readIORef tokens
          writeIORef tokens (tk+a)
          modifyIORef totalTokens $ (+) a 
        else
          error "sending negative tokens"
        --liftIO $ putStrLn $ "received " ++ (show a) ++ " tokens from " ++ (show pid)
        if pid == pidS then do
          ?leak ((m, DeliverTokensWithMessage st), SendTokens a)
          forMseq_ parties $ \pidR -> do
            eventually $ do
              tk <- readIORef tokens
              if tk >=1 then do
                --writeIORef tokens (max 0 (tk-1-st))  -- Burn the delivery fee and send as many requested tokens to the receiver as possible
                writeIORef tokens (tk - st - 1)
                tk <- readIORef tokens
                totaltk <- readIORef totalTokens
                totalm <- readIORef totalMessages 
                --liftIO $ putStrLn $ "\n[fMulticast] total tokens received: " ++ show totaltk
                --liftIO $ putStrLn $ "\t\t total messages received: " ++ show totalm ++ "\n"
                --liftIO $ putStrLn $ "[fMulticast] tokens left: " ++ (show tk)
                --liftIO $ putStrLn $ "[fMulticast] st: " ++ show st
                writeChan f2p (pidR, (MulticastF2P_Deliver m, DeliverTokensWithMessage st))  -- Includes either st or all tokens left in case of insufficient reserves
                --writeChan f2p (pidR, (MulticastF2P_Deliver m, DeliverTokensWithMessage (min st (tk-1))))  -- Includes either st or all tokens left in case of insufficient reserves
              else return()
          writeChan f2p (pidS, (MulticastF2P_OK, DeliverTokensWithMessage 0))
        else error "multicast activated not by sender"
  else do
      -- If sender is corrupted, arbitrary messages can be delivered (once) to parties in any order
      delivered <- newIORef (empty :: Map PID ())
      fork $ forever $ do
         (MulticastA2F_Deliver pidR m, DeliverTokensWithMessage t) <- readChan a2f
         del <- readIORef delivered
         if member pidR del then return ()
         else do
           writeIORef delivered (insert pidR () del)
           writeChan f2p (pidR, (MulticastF2P_Deliver m, DeliverTokensWithMessage t))  -- Send tokens as specified by the Adversary (which should receive these tokens from the Environment)
  return ()

{-- An !fAuth hybrid protocol realizing fMulticast --}
protMulticast :: MonadAsyncP m =>
     Protocol (ClockP2F t) (MulticastF2P t) (SID, FAuthF2P t) (SID, t) m
protMulticast (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  let sid = ?sid :: SID
  let pid = ?pid :: PID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "protMulticast:" $ snd sid

  cOK <- newChan

  -- Only activated by the designated sender
  fork $ forever $ do
    m <- readChan z2p
    case m of
      ClockP2F_Through m | pid == pidS -> do
         liftIO $ putStrLn $ "protMulticast: PARTIES " ++ show parties
         forMseq_ parties $ \pidR -> do
          -- Send m to each party, through a separate functionality
          let ssid' = ("", show (pid, pidR, ""))
          writeChan p2f (ssid', m)
          readChan cOK
         writeChan p2z MulticastF2P_OK
      ClockP2F_Pass -> ?pass
      _ -> error "multicast activated not by sender"

  -- Messages send from other parties are relayed here
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    case mf of 
      FAuthF2P_Deliver m -> do
        -- Double check this is the intended message
        let (pidS' :: PID, pidR' :: PID, _ :: String) = readNote "protMulticast_2" $ snd ssid
        require (pidS' == pidS) "wrong sender"
        require (pidR' == pid)  "wrong recipient"
        writeChan p2z (MulticastF2P_Deliver m)
      FAuthF2P_OK -> writeChan cOK ()

  return ()


{-- The dummy simmulator for protMulticast --}
simMulticast (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  {-
  What happens when the environment asks the adversary to query the buffer?
  -}
  let sid = ?sid :: SID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "sim multicast" (snd sid)

  fork $ forever $ do
    mf <- readChan z2a
    case mf of
      -- TODO: For corrupted parties, the simulator translates "FAuthP2F_Msg m" messages intended for !fAuth (real world) into "MulticastA2F deliver" messages
      -- This requires tedious programming to get right, I wish we could just search for it!
      SttCruptZ2A_A2P (pid, ClockP2F_Pass) -> do
        writeChan a2p (pid, ClockP2F_Pass)
      SttCruptZ2A_A2P (pid, ClockP2F_Through m) -> do 
        let _s :: SID = fst m
        let _m :: String = snd m
        writeChan a2f $ Right $ MulticastA2F_Deliver pid _m 

      SttCruptZ2A_A2F (Left (ClockA2F_Deliver idx)) -> do
        -- The protocol guarantees that clock events are inserted in correct order, 
        -- so delivery can be passed through directly
        writeChan a2f (Left (ClockA2F_Deliver idx))
      SttCruptZ2A_A2F (Left ClockA2F_GetLeaks) -> do
        -- If the "ideal" leak buffer contains "Multicast m",
        -- then the "real" leak buffer should contain [(pid, (sid, m)] for every party
        writeChan a2f (Left ClockA2F_GetLeaks)
        _mb <- readChan f2a
        let (Left (ClockF2A_Leaks buf)) = _mb
        let extendRight conf = show ("", conf)
        let resp = case buf of
              []       ->  []
              [m] ->  [(extendSID sid "" (show (pidS, pid, "")),
                         m)
                      | pid <- parties]
        writeChan a2z $ SttCruptA2Z_F2A $ Left (ClockF2A_Leaks resp)
        
  return ()

testVEnv
  :: MonadEnvironment m =>
     Environment (MulticastF2P String) (ClockP2F String) (SttCruptA2Z (SID, FAuthF2P String) (Either (ClockF2A (SID, String)) (SID, Void))) (SttCruptZ2A (ClockP2F (SID, String)) (Either ClockA2F (SID, Void))) Void ClockZ2F String m
testVEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestMulticast", show ("Alice", ["Alice", "Bob", "Charlie"], ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Alice",())]
  --writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m 
    ?pass
  fork $ forever $ do
    f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2P $ ("Bob", ClockP2F_Through (sid, "I'm Alice"))

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2P $ ("Bob", ClockP2F_Through (sid, "You're not Alice"))
  () <- readChan pump  
  writeChan z2a $ SttCruptZ2A_A2P $ ("Charlie", ClockP2F_Through (sid, "You're not Alice"))

  () <- readChan pump
  writeChan outp "1"


testEnvMulticast
  :: (MonadEnvironment m) =>
     Environment (MulticastF2P String) (ClockP2F String)
           (SttCruptA2Z (SID, FAuthF2P String) (Either (ClockF2A (SID, String)) (SID, Void)))
           (SttCruptZ2A (ClockP2F (SID, String)) (Either ClockA2F (SID, Void))) Void
            ClockZ2F String m
testEnvMulticast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestMulticast", show ("Alice", ["Alice", "Bob"], ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m 
    ?pass
  fork $ forever $ do
    f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ClockP2F_Through  "I'm Alice")

  -- Let the adversary see
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks

  -- Optional: Adversary delivers messages out of order
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 1)

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

  -- Advance to round 1
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  -- Advance to round 2
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"


testMulticastReal :: IO String
testMulticastReal = runITMinIO 120 $ execUC testEnvMulticast (runAsyncP protMulticast) (runAsyncF $ bangFAsync $ fAuth) dummyAdversary


testMulticastIdeal :: IO String
testMulticastIdeal = runITMinIO 120 $ execUC testEnvMulticast (idealProtocol) (runAsyncF fMulticast) simMulticast

