 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
 PartialTypeSignatures
  #-} 

module ACast where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import Data.List (elemIndex, delete)
import TestTools (envReadOut)
import qualified Data.Map.Strict as Map

{- fACast: an asynchronous broadcast functionality, Bracha's Broadcast -}
{-
   Narrative description:
 -}


data ACastP2F a = ACastP2F_Input a deriving Show
data ACastF2P a = ACastF2P_OK | ACastF2P_Deliver a deriving (Show, Eq)
--data ACastA2F a = ACastA2F_Deliver PID deriving Show
data ACastTVariant = ACastTSmall | ACastTLarge | ACastTCorrect deriving (Show, Eq)
data ACastRVariant = ACastRSmall | ACastRLarge | ACastRCorrect deriving (Show, Eq)
data ACastDVariant = ACastDSmall | ACastDLarge | ACastDCorrect deriving (Show, Eq)


fACast :: MonadFunctionalityAsync m a => Functionality (ACastP2F a) (ACastF2P a) Void Void Void Void m
fACast (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender, set of parties, and tolerance parameter is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "fACast" $ snd ?sid


  -- Check the fault tolerance parameters
  let n = length parties
  require (Map.size ?crupt <= t) "Fault tolerance assumption violated"
  require (3*t < n) "Invalid fault tolerance parameter (must be 3t<n)"

  -- Allow sender to choose the input
  (pid, ACastP2F_Input m) <- readChan p2f
  liftIO $ putStrLn $ "[fACast]: input read " -- ++ show m
  leak m
  require (pid == pidS) "Messages not from sender are ignored"

  -- Every honest party eventually receives an output
  forMseq_ parties $ \pj -> do
    if not (Map.member pj ?crupt) then do
      eventually $ do
        liftIO $ putStrLn $ "Queued party: " ++ (show pj)
        writeChan f2p (pj, ACastF2P_Deliver m)
    else do
      return()

	-- give control back to the calling party after the input is accepted
  writeChan f2p (pidS, ACastF2P_OK)

-- Same as the functionality above but augmented with import tokens
-- the functionality demands 1 unit of import per receiver in a BEST EFFORT
-- so only k of n honest parties might receive output if only k import is given
fACastToken :: MonadFunctionalityAsync m (a, CarryTokens Int) => Functionality ((ACastP2F a), CarryTokens Int) (ACastF2P a) Void Void Void Void m
fACastToken (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender, set of parties, and tolerance parameter is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "fACast" $ snd ?sid


  -- Check the fault tolerance parameters
  let n = length parties
  require (Map.size ?crupt <= t) "Fault tolerance assumption violated"
  require (3*t < n) "Invalid fault tolerance parameter (must be 3t<n)"

  tokens <- newIORef 0

  -- Allow sender to choose the input
  (pid, ((ACastP2F_Input m), SendTokens a)) <- readChan p2f
	-- TODO: at the moment we manually update import in the code rather than doing it within MonadITM
  if a>=0 then do
    tk <- readIORef tokens
    writeIORef tokens (tk+a)
  else
    error "sending negative tokens"

  liftIO $ putStrLn $ "[fACast]: input read " -- ++ show m
  liftIO $ putStrLn $ "[fACast]: received " ++ (show a) ++ " tokens from " ++ (show pid)
  leak (m, SendTokens a)
  require (pid == pidS) "Messages not from sender are ignored"

  -- Every honest party eventually receives an output
  forMseq_ parties $ \pj -> do
    if not (Map.member pj ?crupt) then do
      eventually $ do
        tk <- readIORef tokens
        if tk >=1 then do		-- require 1 token for each receiver
          writeIORef tokens (tk-1)  -- Burn 1 token for delivery
          liftIO $ putStrLn $ "[fACast]: tokens left: " ++ (show (tk-1))
          liftIO $ putStrLn $ "[fACast]: queued party: " ++ (show pj)
          writeChan f2p (pj, ACastF2P_Deliver m)
        else return()   -- if out of tokens don't do anything
    else do
      return()

  writeChan f2p (pidS, ACastF2P_OK)


{- Protocol ACast -}

data ACastMsg t = ACast_VAL t | ACast_ECHO t | ACast_READY t deriving (Show, Eq, Read)

-- Give (fBang fMulticast) a nicer interface
manyMulticast :: MonadProtocol m =>
     PID -> [PID]
     -> (Chan (SID, (MulticastF2P t, CarryTokens Int)), Chan (SID, ((t, TransferTokens Int), CarryTokens Int)))
     -> m (Chan (PID, (t, CarryTokens Int)), Chan ((t, TransferTokens Int), CarryTokens Int), Chan ())
manyMulticast pid parties (f2p, p2f) = do
  p2f' <- newChan
  f2p' <- newChan
  cOK <- newChan

  -- Handle writing
  fork $ forMseq_ [0..] $ \(ctr :: Integer) -> do
       m <- readChan p2f'
       let ssid = (show ctr, show (pid, parties, ""))
       writeChan p2f (ssid, m)

  -- Handle reading (messages delivered in any order)
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    let (pidS :: PID, _ :: [PID], _ :: String) = readNote "manyMulti" $ snd ssid
    case mf of
      (MulticastF2P_OK, SendTokens _) -> do
                     require (pidS == pid) "ok delivered to wrong pid"
                     writeChan cOK ()
      (MulticastF2P_Deliver m, SendTokens t) -> do
                     writeChan f2p' (pidS, (m, SendTokens t))
  return (f2p', p2f', cOK)

readBangMulticast pid parties f2p = do
  c <- newChan
  fork $ forever $ do
    forMseq_ [0..] 

writeBangSequential p2f = do
  c <- newChan
  fork $ do
    forMseq_ [0..] $ \(ctr :: Integer) -> do
        m <- readChan c
        let ssid' = ("", show ctr)
        writeChan p2f (ssid', m)
  return c

readBangAnyOrder f2p = do
  c <- newChan
  fork $ forever $ do
    (_, m) <- readChan f2p
    writeChan c m
  return c


-- Simple test environment for fACast
testEnvACastIdeal
  :: MonadEnvironment m =>
  Environment (ACastF2P String) (ClockP2F (ACastP2F String)) (SttCruptA2Z a (Either (ClockF2A String) Void)) (SttCruptZ2A b (Either ClockA2F Void)) Void (ClockZ2F) String m
testEnvACastIdeal z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    printEnvIdeal $ "[testEnvACastIdeal]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ClockP2F_Through $ ACastP2F_Input "I'm Alice")

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
        mb <- readChan a2z
        let SttCruptA2Z_F2A (Left (ClockF2A_Count c)) = mb
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver the next message -}
    writeChan z2a $ SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))
    readChan pump

  writeChan outp "environment output: 1"

-- fACast with dummy adv make sure it works as intended in the benign setting
testACastBenign :: IO String
testACastBenign = runITMinIO 120 $ execUC testEnvACastIdeal (idealProtocol) (runAsyncF $ fACast) dummyAdversary

-- the type of the transcript output by
-- environments. TODO: abstract away the environment types this is horrendous
type Transcript = [Either
                         (SttCruptA2Z
                            (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                            (Either
                               (ClockF2A (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                               (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
                         (PID, ACastF2P String)]

testEnvACast
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int))
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                  (Either (ClockF2A (SID,((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                   (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) Transcript m
testEnvACast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  -- Have Alice write a message
  () <- readChan pump
  --writeChan z2p ("Alice", ((ClockP2F_Through $ ACastP2F_Input "I'm Alice"), SendTokens 1000))
  writeChan z2p ("Alice", ((ClockP2F_Through $ ACastP2F_Input "I'm Alice"), SendTokens 1000))

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 10)
        c <- readChan clockChan
        -- printEnvReal $ "[testEnvACast]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do

    b <- ?getBit
    if b then do
      -- Action 1: Inject fake messages from corrupt nodes
      return ()
    else return()
    
    -- Action 2:
    writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
    c <- readChan clockChan
    printEnvReal $ "[testEnvACast]: Events remaining: " ++ show c
    
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver first message -}
    idx <- getNbits 10
    let i = mod idx c
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver i))), SendTokens 0)
    readChan pump

  -- Output is the transcript
  writeChan outp =<< readIORef transcript

testACastReal :: IO Transcript
testACastReal = runITMinIO 120 $ execUC
  testEnvACast
  (runAsyncP $ protACastBroken ACastTCorrect ACastRCorrect ACastDCorrect)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken

-- a TESTING version of the protocol realizing fACast in order to test broken 
-- code pieces. The arguments exist only to test thresholds being set incorrectly
-- which the SIMPLEST form of error. TODO: can we write more nuanced errors? 
protACastBroken :: MonadAsyncP m => ACastTVariant -> ACastRVariant -> ACastDVariant ->
                                    Protocol ((ClockP2F (ACastP2F String)), CarryTokens Int) (ACastF2P String)
                                             --(SID, (MulticastF2P (ACastMsg String), TransferTokens Int))
                                             (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                                             (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)) m
protACastBroken variantT variantR variantD (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid
  cOK <- newChan

  -- Keep track of state
  inputReceived <- newIORef False
  decided <- newIORef False
  echoes <- newIORef (Map.empty :: Map String (Map PID ()))
  readys <- newIORef (Map.empty :: Map String (Map PID ()))
  tokens <- newIORef 0
  
{- TESTING MODS -}          
  f2p' <- newChan
  z2p' <- newChan
  failed <- newIORef False

	-- new require where the machine halts after a require check has failed
	-- a global flag `failed` is used and if set, activation just gives control
	-- back to the environment with ?pass
  let require cond msg = do
        if not cond then do
          liftIO $ putStrLn $ msg
          ?pass
          --readChan =<< newChan
          writeIORef failed True 
          return False
        else return True

  fork $ forever $ do
    m <- readChan f2p
    f <- readIORef failed
    if f then ?pass
    else writeChan f2p' m
  
  fork $ forever $ do
    m <- readChan z2p
    f <- readIORef failed
    if f then ?pass
    else writeChan z2p' m
{- TESTING MODS -}
       
  -- Prepare channels
  (recvC, multicastC, cOK) <- manyMulticast ?pid parties (f2p', p2f)

  let multicast (x, DeliverTokensWithMessage st) = do
        tk <- readIORef tokens
        let neededTokens = (length parties) * (st+1)  -- The multicast requires sending st tokens to each party, plus 1 delivery fee for each message
        writeIORef tokens (max 0 (tk-neededTokens))  -- Try to send the required tokens in a best effort approach
        liftIO $ putStrLn $ ">>>>>. Multicasting [" ++ show ?pid ++ "] " ++ show x ++ " with SendTokens " ++ show (min tk neededTokens) ++ " and DeliverTokensWithMessage " ++ show st
        -- st specifies the tokens F will send to each party; SendTokens represents the tokens F will receive
        writeChan multicastC ((x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens))
        readChan cOK

  let recv = readChan recvC -- :: m (ACastMsg t)

  -- For sending ready just once
  sentReady <- newIORef False
  let sendReadyOnce v = do
        already <- readIORef sentReady
        if not already then do
          liftIO $ putStrLn $ "[" ++ ?pid ++ "] Sending READY"
          writeIORef sentReady True
          multicast $ (ACast_READY v, DeliverTokensWithMessage 0)
          -- Each party should have already received Tokens scheduled by the sender's input, so no need to send more tokens from party to party
        else return ()

  -- Sender provides input
  fork $ do
    (mf, SendTokens a) <- readChan z2p'
    if a>=0 then do
      if ?pid == pidS then do
        tk <- readIORef tokens
        writeIORef tokens (tk+a)
        liftIO $ putStrLn $ (show ?pid) ++ " received " ++ (show a) ++ " tokens from Z"
      else
        return()
    else
      error "sending negative tokens"
    case mf of
       ClockP2F_Pass -> ?pass
       ClockP2F_Through (ACastP2F_Input m) -> do
         liftIO $ putStrLn $ "Step 1"
         check <- require (?pid == pidS) "[protACast]: only sender provides input"
         if check then do
           multicast (ACast_VAL m, DeliverTokensWithMessage ((length parties)*2))
           -- Give each party enough tokens for multicasting one round of ECHO and one round of READY
           -- liftIO $ putStrLn $ "[protACast]: multicast done"
           writeChan p2z ACastF2P_OK
         else return ()

  let n = length parties
  -- let thresh = ceiling (toRational (n+t+1) / 2) -- normal ECHO threshold
  -- let thresh = floor (toRational (n+t) / 2) -- too few ECHO
  -- let thresh = n-t+1 -- too many ECHO
  -- let readyThresh = t+1 -- normal READY threshold
  -- let readyThresh = t -- too few READY
  -- let readyThresh = n-t-t+1 -- too many READY
  -- let decideThresh = readyThresh+t -- normal Decide threshold
  -- let decideThresh = readyThresh+t-1 -- too few Decide threshold
  -- let decideThresh = n-t+1 -- too many Decide threshold

  -- Receive messages from multicast
  fork $ forever $ do
    --(pid', (m, DeliverTokensWithMessage a)) <- recv
    (pid', (m, SendTokens a)) <- recv
    liftIO $ putStrLn $ "[protACast] " ++ show ?pid ++ "Received message " ++ show m ++ " from fMulticast"
    if a>=0 then do
      tk <- readIORef tokens
      writeIORef tokens (tk+a)
    else
      error "receiving negative tokens"
    liftIO $ putStrLn $ "[protACast]"++ ?pid ++": " ++ show (pid', m)
    case m of
      ACast_VAL v -> do
          -- Check this is the FIRST such message from the right sender
          check <- require (pid' == pidS) "[protACast]: VAL(v) from wrong sender"
          if check then do
            check :: Bool <- readIORef inputReceived >>= \b -> require (not b) "[protACast]: Too many inputs received"
            liftIO $ putStrLn $ "\n\t check: " ++ show check ++ "\n"
            if check then do
              writeIORef inputReceived True
              multicast $ (ACast_ECHO v, DeliverTokensWithMessage 0)
              -- Each party should have already received Tokens scheduled by the sender's input, so no need to send more tokens from party to party
              ?pass
            else return ()
          else 
            return ()
      ACast_ECHO v -> do
          thresh <- case variantT of
              ACastTSmall -> return $ floor (toRational (n+t) / 2) -- too few ECHO
              ACastTLarge -> return $ n-t+1 -- too many ECHO
              otherwise -> return $ ceiling (toRational (n+t+1) / 2) -- normal ECHO threshold
          ech <- readIORef echoes
          let echV = Map.findWithDefault Map.empty v ech
          check <- require (not $ Map.member pid' echV) $ "Already echoed"
          if check then do
            let echV' = Map.insert pid' () echV
            writeIORef echoes $ Map.insert v echV' ech
            liftIO $ putStrLn $ "[protACast]"++ ?pid ++" echo updated at " ++ show ?pid
            liftIO $ putStrLn $ "[protACast]"++ ?pid ++" echo amount " ++ show (Map.size echV')
            --  Check if ready to decide
            --liftIO $ putStrLn $ "[protACast] " ++ show n ++ " " ++ show thresh ++ " " ++ show (Map.size echV')
            if Map.size echV' >= thresh then do
                liftIO $ putStrLn "Threshold met! Sending ready"            
                sendReadyOnce v
                --liftIO $ putStrLn $ "[" ++ ?pid ++ "] Sending READY"
                --writeIORef sentReady True
                --multicast $ (ACast_READY v, DeliverTokensWithMessage 0)
            else do
                liftIO $ putStrLn $ "[protACast]"++ ?pid ++" not met yet"
                return ()
            liftIO $ putStrLn $ "[protACast]"++ ?pid ++" return OK"
            ?pass
          else return ()

      ACast_READY v -> do
          readyThresh <- case variantR of
            ACastRSmall -> return $ t -- too few READY
            ACastRLarge -> return $ n-t-t+1 -- too many READY
            otherwise -> return $ t+1 -- normal READY threshold

          decideThresh <- case variantD of
            ACastDSmall -> return $ (readyThresh+t-1) -- too few Decide threshold
            ACastDLarge -> return $ (n-t+1) -- too many Decide threshold
            otherwise -> return $ readyThresh+t -- normal Decide threshold
          -- Check each signature
          rdy <- readIORef readys
          let rdyV = Map.findWithDefault Map.empty v rdy
          check <- require (not $ Map.member pid' rdyV) $ "Already readyd"
          if check then do
            let rdyV' = Map.insert pid' () rdyV
            writeIORef readys $ Map.insert v rdyV' rdy
            liftIO $ putStrLn $ "[protACast]"++ ?pid ++" ready updated"

            dec <- readIORef decided
            --if dec then
            --  liftIO $ putStrLn $ "<><><><><> [protACast] " ++ ?pid ++ " decided already"
            --else return ()
            if dec then ?pass
            else do
              let ct = Map.size rdyV'
              if ct >= readyThresh then do
                liftIO $ putStrLn $ "[protACast]"++ ?pid ++" readying"
                sendReadyOnce v
                return()
              else
                return()
              liftIO $ putStrLn $ "[protACast] " ++ show ?pid ++ " returned from multicast"
              if ct == decideThresh then do
                --liftIO $ putStrLn $ "<><><><><> [protACast] " ++ ?pid ++ " decided already"
                writeIORef decided True
                writeChan p2z (ACastF2P_Deliver v)
              else ?pass
          else return ()
  return ()


{- 
  from the environment code it looks like validity here means that 
  parties only decide a value that the leader proposed. Here the leader, Alice,
  proposes 1 but corrupt Dave tries to get others to agree to 2.
-}
testEnvACastBrokenValidity
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int))
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                  (Either (ClockF2A (SID,((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                   (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) Transcript m
testEnvACastBrokenValidity z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  let ssidDave1 = ("sidTestACast", show ("Dave", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidDave2 = ("sidTestACast", show ("Dave", ["Alice", "Bob", "Carol", "Dave"], "2"))


  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Dave",())]
  
  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  writeChan z2p ("Alice", ((ClockP2F_Through $ ACastP2F_Input "1"), SendTokens 100))

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks), SendTokens 24)

  forMseq_ [1..5] $ \x -> do
      () <- readChan pump
      writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidDave1, (MulticastA2F_Deliver "Bob" (ACast_ECHO "2"), DeliverTokensWithMessage 0))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidDave2, (MulticastA2F_Deliver "Bob" (ACast_READY "2"), DeliverTokensWithMessage 0))), SendTokens 0)

  forMseq_ [1..15] $ \x -> do
      () <- readChan pump
      writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)), SendTokens 0)

  -- Output is the transcript
  () <- readChan pump
  writeChan outp =<< readIORef transcript

testEnvACastBrokenAgreement
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int))
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                  (Either (ClockF2A (SID,((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                   (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) Transcript m
testEnvACastBrokenAgreement z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))


  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Alice",())]

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice1, (MulticastA2F_Deliver "Bob" (ACast_VAL "1"), DeliverTokensWithMessage 8))), SendTokens 24)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice1, (MulticastA2F_Deliver "Carol" (ACast_VAL "2"), DeliverTokensWithMessage 8))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice2, (MulticastA2F_Deliver "Carol" (ACast_ECHO "2"), DeliverTokensWithMessage 0))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice2, (MulticastA2F_Deliver "Dave" (ACast_ECHO "1"), DeliverTokensWithMessage 8))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice3, (MulticastA2F_Deliver "Bob" (ACast_READY "1"), DeliverTokensWithMessage 0))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice3, (MulticastA2F_Deliver "Carol" (ACast_READY "2"), DeliverTokensWithMessage 0))), SendTokens 0)

  forMseq_ [1..20] $ \x -> do
      () <- readChan pump
      writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)), SendTokens 0)

  -- Output is the transcript
  () <- readChan pump
  writeChan outp =<< readIORef transcript

testEnvACastBrokenReliability
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int))
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                  (Either (ClockF2A (SID,((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                   (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int)
     Void (ClockZ2F) Transcript m
testEnvACastBrokenReliability z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))

    
  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Alice",())]

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice1, (MulticastA2F_Deliver "Bob" (ACast_VAL "1"), DeliverTokensWithMessage 8))), SendTokens 21)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice1, (MulticastA2F_Deliver "Carol" (ACast_VAL "2"), DeliverTokensWithMessage 8))), SendTokens 0)

  () <- readChan pump 
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice2, (MulticastA2F_Deliver "Carol" (ACast_ECHO "2"), DeliverTokensWithMessage 0))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice2, (MulticastA2F_Deliver "Dave" (ACast_ECHO "1"), DeliverTokensWithMessage 8))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice3, (MulticastA2F_Deliver "Bob" (ACast_READY "1"), DeliverTokensWithMessage 0))), SendTokens 0)

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice3, (MulticastA2F_Deliver "Carol" (ACast_READY "2"), DeliverTokensWithMessage 0))), SendTokens 0)

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
  c <- readChan clockChan
  
  printEnvIdeal $ "Runqueue size: " ++ show c

  forMseq_ [1..20] $ \x -> do
      () <- readChan pump
      writeChan z2f ClockZ2F_MakeProgress

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Delay 2)), SendTokens 0)
  forMseq_ [1..25] $ \x -> do
      () <- readChan pump
      writeChan z2f ClockZ2F_MakeProgress

  -- Output is the transcript
  () <- readChan pump
  writeChan outp =<< readIORef transcript

testEnvACastBrokenTermination
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int))
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                  (Either (ClockF2A (SID,((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                   (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) Transcript m
testEnvACastBrokenTermination z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  
  -- Have Alice write a message
  () <- readChan pump
  writeChan z2p ("Alice", ((ClockP2F_Through $ ACastP2F_Input "I'm Alice"), SendTokens 4))

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 10)
        c <- readChan clockChan
        -- printEnvReal $ "[testEnvACast]: Events remaining: " ++ show c
        return (c > 0)
  

  --fork $ forever $ do  
  --  () <- readChan pump
  --  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks), SendTokens 24) 
  --  lk <- readIORef leak
      
 
  () <- readChan pump
  whileM_ checkQueue $ do

    b <- ?getBit
    if b then do
      -- Action 1: Inject fake messages from corrupt nodes
      return ()
    else return()
    
    -- Action 2:
    writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
    c <- readChan clockChan
    printEnvReal $ "[testEnvACast]: Events remaining: " ++ show c
    
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver first message -}
    idx <- getNbits 10
    let i = mod idx c
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver i))), SendTokens 0)
    readChan pump

  -- Output is the transcript
  writeChan outp =<< readIORef transcript
  --writeChan outp =<< readIORef transcript

testACastTermination :: IO Transcript
testACastTermination = runITMinIO 120 $ execUC
  testEnvACastBrokenTermination
  --(runAsyncP $ protACastBroken ACastTCorrect ACastRCorrect ACastDCorrect)
  (runAsyncP $ protACastBroken ACastTCorrect ACastRCorrect ACastDCorrect)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken

testACastBroken :: IO Transcript
testACastBroken = runITMinIO 120 $ execUC
  testEnvACastBrokenAgreement
  (runAsyncP $ protACastBroken ACastTSmall ACastRCorrect ACastDSmall)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken

testCompareBrokenAgreement :: IO Bool
testCompareBrokenAgreement = runITMinIO 120 $ do
  let variantT = ACastTSmall
  let variantR = ACastRCorrect
  let variantD = ACastDCorrect
  let prot () = protACastBroken variantT variantR variantD
  liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
  t1R <- runRandRecord $ execUC
             testEnvACastBrokenAgreement
             (runAsyncP $ prot ())
             (runAsyncF $ bangFAsync fMulticastToken)
             dummyAdversaryToken
  let (t1, bits) = t1R
  liftIO $ putStrLn ""
  liftIO $ putStrLn ""
  liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
  t2 <- runRandReplay bits $ execUC
             testEnvACastBrokenAgreement
             (idealProtocolToken)
             (runAsyncF $ fACastToken)
             (runTokenA $ simACastBroken $ prot ())
  return (t1 == t2)


testCompareBrokenReliability :: IO Bool
testCompareBrokenReliability = runITMinIO 120 $ do
  let variantT = ACastTSmall
  let variantR = ACastRCorrect
  let variantD = ACastDCorrect
  let prot () = protACastBroken variantT variantR variantD
  liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
  t1R <- runRandRecord $ execUC
             testEnvACastBrokenReliability
             (runAsyncP $ prot ())
             (runAsyncF $ bangFAsync fMulticastToken)
             dummyAdversaryToken
  let (t1, bits) = t1R
  liftIO $ putStrLn ""
  liftIO $ putStrLn ""
  liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
  t2 <- runRandReplay bits $ execUC
             testEnvACastBrokenReliability
             (idealProtocolToken)
             (runAsyncF fACastToken)
             (runTokenA $ simACastBroken $ prot ())
  --let t2 = []
  return (t1 == t2)

testCompareBrokenValidity :: IO Bool
testCompareBrokenValidity = runITMinIO 120 $ do
  let variantT = ACastTCorrect
  let variantR = ACastRSmall
  let variantD = ACastDCorrect
  let prot () = protACastBroken variantT variantR variantD
  liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
  t1R <- runRandRecord $ execUC
             testEnvACastBrokenValidity
             (runAsyncP $ prot ())
             (runAsyncF $ bangFAsync fMulticastToken)
             dummyAdversaryToken
  let (t1, bits) = t1R
  liftIO $ putStrLn ""
  liftIO $ putStrLn ""
  liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
  t2 <- runRandReplay bits $ execUC
             testEnvACastBrokenValidity
             (idealProtocolToken)
             (runAsyncF $ fACastToken)
             (runTokenA $ simACastBroken $ prot ())
  return (t1 == t2)

{-- TODO: This is duplicated in MPC2.hs, fix it --}
makeSyncLog handler req = do
  ctr <- newIORef 0
  let syncLog = do
        -- Post the request
        log <- req
        -- Only process the new elements
        t <- readIORef ctr
        let tail = drop t log
        modifyIORef ctr (+ length tail)
        forM tail handler
        return ()
  return syncLog
  
{-- TODO: Simulator for ACast --}
simACastBroken :: MonadAdversaryToken m => 
  (MonadProtocol m => Protocol ((ClockP2F (ACastP2F String)), CarryTokens Int)
    (ACastF2P String) (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
    (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)) m) ->
                                           
  Adversary 
    ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                  (Either (ClockA2F) (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int)
    (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int))
                 (Either (ClockF2A  (SID,((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                         (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
    (ACastF2P String) (ClockP2F (ACastP2F String, CarryTokens Int))
    (Either (ClockF2A (String, CarryTokens Int)) Void) (Either ClockA2F Void) m
simACastBroken sbxProt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
    -- Sender and set of parties is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid

  let isCruptSender = Map.member pidS ?crupt

  {--
   This is a full information simulator.
   This means that our strategy will be for the simulator to run a sandbox version of the real
      world protocol that's kept in the same configuration as the ideal world.
   The sandbox includes honest parties
   The environment/dummyAdversary interface is routed directly to this virtualized execution.
   --}

  -- Routing z2a <-->
  f2aLeak <- newChan

  sbxpump <- newChan
  sbxz2p <- newChan   -- writeable by host
  sbxp2z <- newChan   -- readable by host
  sbxz2f <- newChan
  let sbxEnv z2exec (p2z',z2p') (a2z',z2a') (f2z', z2f') pump' outp' = do
        -- Copy the SID and corruptions
        writeChan z2exec $ SttCrupt_SidCrupt ?sid ?crupt

        -- Expose wrappers for the p2z interactions.
        forward p2z' sbxp2z
        forward sbxz2p z2p'

        -- Forward messages from environment to host, into the sandbox dummy adv
        forward z2a z2a'
        forward a2z' a2z

        forward sbxz2f z2f'

        -- When the sandbox receives on pump', pass control back to the host
        forward pump' sbxpump

        return ()

  let sbxBullRand () = bangFAsync fMulticastToken

  -- Monitor the sandbox for outputs
  chanOK <- newChan
  partiesYet <- newIORef $ filter (`Map.notMember` ?crupt) parties
  isFuncSetForCruptSender <- newIORef False

  fork $ forever $ do
    mf <- readChan sbxp2z
    case mf of
      (_pidS, ACastF2P_OK) -> writeChan chanOK ()
      (pid, ACastF2P_Deliver message) -> do
        -- The sandbox produced output. We can deliver the corresponding message in fACast
        p <- readIORef partiesYet
        let Just idx = elemIndex pid p
        modifyIORef partiesYet $ delete pid
        liftIO $ putStrLn $ "delivering: " ++ pid
        isSet <- readIORef isFuncSetForCruptSender
        if isCruptSender && isSet == False then do
          liftIO $ putStrLn $ "setting up functionality in case of corrupt sender"
          tks <- ?getToken
          writeChan a2p (pidS, (ClockP2F_Through $ (ACastP2F_Input message, SendTokens (min tks (length parties)))))
          (_,_) <- readChan p2a
          writeIORef isFuncSetForCruptSender True
          return ()
        else
          return ()
        tks <- ?getToken
        if tks>= 1 then do
          liftIO $ putStrLn $ "delivered: " ++ pid ++ "," ++ show idx
          writeChan a2f $ Left $ ClockA2F_Deliver idx
        else
          ?pass

  let handleLeak (m, SendTokens a) = do
         printAdv $ "handleLeak simulator"
         if isCruptSender then
           return ()
         else do
           -- The input is provided to the ideal functionality.
           -- We initiate the input operation in the sandbox.
           -- writeIORef fInputWaiting (Just x)
           writeChan sbxz2p (pidS, ((ClockP2F_Through $ ACastP2F_Input m), SendTokens a))
           () <- readChan chanOK
           return ()

  sendAdvance <- newIORef False

  fork $ forever $ do
    mf <- readChan f2a
    printAdv $ show "Received f2a" ++ show mf
    case mf of
      (Left (ClockF2A_Leaks _)) -> writeChan f2aLeak mf
      (Left (ClockF2A_Advance)) -> do
        tks <- ?getToken
        printAdv $ "adversary has " ++ (show tks) ++ " tokens"
        if tks>= 1 then do
          printAdv $ "adversary delays advance"
          writeIORef sendAdvance True
          writeChan a2f (Left (ClockA2F_Delay 1))
        else
          writeChan sbxz2f ClockZ2F_MakeProgress
      (Left (ClockF2A_Pass)) -> do
        adv <- readIORef sendAdvance
        if adv then do
          -- Suppress results from the simulator's extra delay
          writeIORef sendAdvance False
          writeChan sbxz2f ClockZ2F_MakeProgress
        else
          writeChan a2z $ SttCruptA2Z_F2A (Left (ClockF2A_Pass))

  -- Only process the new bulletin board entries since last time
  syncLeaks <- makeSyncLog handleLeak $ do
        writeChan a2f $ Left ClockA2F_GetLeaks
        mf <- readChan f2aLeak
        let Left (ClockF2A_Leaks (leaks :: [(String, CarryTokens Int)])) = mf
        return leaks

  let sbxAdv (z2a',a2z') (p2a',a2p') (f2a',a2f') = do
        -- The sandbox adversary poses as the dummy adversary, but takes every
        -- activation opportunity to synchronize with the ideal world functionality
        fork $ forever $ do
          (mf, SendTokens _) <- readChan z2a'
          printAdv $ show "Intercepted z2a'" ++ show mf
          syncLeaks
          printAdv $ "forwarding into to sandbox"
          case mf of
            SttCruptZ2A_A2F f -> do
              liftIO $ putStrLn $ "writing message " ++ show f ++ " to sbxf"
              writeChan a2f' f
            SttCruptZ2A_A2P pm -> writeChan a2p' pm
        fork $ forever $ do
          m <- readChan f2a'
          liftIO $ putStrLn $ "\n\t >>>>>>>>>>>>>\n"

          liftIO $ putStrLn $ show "f2a'" ++ show m
          writeChan a2z' $ SttCruptA2Z_F2A m
        fork $ forever $ do
          (pid,m) <- readChan p2a'
          liftIO $ putStrLn $ show "p2a'"
          writeChan a2z' $ SttCruptA2Z_P2A (pid, m)
        return ()

  -- We need to wait for the write token before we can finish initalizing the
  -- sandbox simulation.
  mf <- selectRead z2a f2a   -- TODO: could there be a P2A here?

  fork $ execUC_ sbxEnv (runAsyncP sbxProt) (runAsyncF (sbxBullRand ())) sbxAdv
  () <- readChan sbxpump

  -- After initializing, the sbxAdv is now listening on z2a,f2a,p2a. So this passes to those
  case mf of
    Left m -> writeChan z2a m
    Right m -> writeChan f2a m

  once <- newIORef False
  times <- newIORef 0

  fork $ forever $ do
      () <- readChan sbxpump
      -- undefined
      t <- readIORef times
      modifyIORef times $ (+) 1
      ?pass
      return ()
      --else 
      --  return ()
      -- ?pass
      --return ()
  return ()

testACastIdeal :: IO Transcript
testACastIdeal = runITMinIO 120 $ execUC
  testEnvACast
  (idealProtocolToken)
  (runAsyncF $ fACastToken)
  (runTokenA $ simACastBroken $ protACastBroken ACastTCorrect ACastRCorrect ACastDCorrect)

{--
 What are the options available to the environment?
 - Can choose to deliver messages in any order
 - Can choose to inject point-to-point messages to send from malicious parties
 - Can provide input to sender (if sender is honest)

 These choices could be adaptive and depend on the transcript observed so far,
 In this example, we'll only generate in a non-adaptive way, without looking at
 the content.
 --}

{-- Comparing transcripts
   Since the protocol and ideal functionalities are all determinsitic, we can
   only the environment makes random choices, hence for a fixed seed provided to
   the environment, we can check that these must be exactly the same in both worlds.
  --}

testCompare :: IO Bool
testCompare = runITMinIO 120 $ do
  let prot () = protACastBroken ACastTCorrect ACastRCorrect ACastDCorrect
  liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
  t1R <- runRandRecord $ execUC
             testEnvACast 
             (runAsyncP $ prot ())
             (runAsyncF $ bangFAsync fMulticastToken)
             dummyAdversaryToken
  let (t1, bits) = t1R
  liftIO $ putStrLn ""
  liftIO $ putStrLn ""  
  liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
  t2 <- runRandReplay bits $ execUC
             testEnvACast 
             (idealProtocolToken)
             (runAsyncF $ fACastToken)
             (runTokenA $ simACastBroken $ prot ())
  return (t1 == t2)
