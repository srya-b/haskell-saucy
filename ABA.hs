{-
    Open questions regarding the protocol in https://arxiv.org/pdf/2002.08765.pdf:
        1. In the first round if a party is given input Propose(X) then you end up s_broadcasting X. If all other parties s_broadcast ~X instead,
            should you accept them towards a county for the ~X value or ignore it because you've only spawned an instance of s_broadcast for X.
            There is a place in the protocol where in round+1 it will attempt to try ~X to see if it is a valid choice to commit to so maybe it is
            correct to ignore the message. It will be checked in round+1.


    Some Assumptions Made: the protocol seems to assume that all the honest parties must be given
        propose(v) input otherwise you don't get the guarantees of the protocol. 

-}


 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
 PartialTypeSignatures
  #-} 

module ABA where

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

--data TokenMsg a = (a, CarryTokens Int) deriving (Show, Eq)
--type TokenMsg a = (a, CarryTokens b) deriving (Show, Eq)
data CastP2F a = CastP2F_cast a | CastP2F_ro Int deriving Show
----type CastP2F a = TokenMsg (a, TransferTokens Int)
----type RoP2F = TokenMsg Bool
--data CastF2P a = CastF2P_OK | CastF2P_Deliver a deriving (Show, Eq)
--data RoP2F = RoP2F_ro Int deriving (Show, Eq)
data CastF2P a = CastF2P_OK | CastF2P_Deliver a | CastF2P_ro Bool deriving (Show, Eq)
--type CastF2P a = TokenMsg a
--type RoF2P = TokenMsg Bool
--data CoinP2F a = Either (CastP2F a) RoP2F deriving (Show, Eq)
--data CoinF2P a = Either (CastF2P a) RoF2P deriving (Show, Eq)

--type CastF2A a = (a, TransferTokens Int)
--data CoinF2A = Either (CastF2A a) RoF2A deriving (Show, Eq)
--data CoinA2F a = CastA2F_Deliver PID a deriving (Show, Eq) 
data CastF2A a = CastF2A a | CastF2A_ro Bool deriving (Show, Eq)
data CastA2F a = CastA2F_Deliver PID a deriving Show

--type CastP2F_cast a = (a, TransferTokens Int)
data CoinCastP2F a = CoinCastP2F_cast (a, TransferTokens Int) | CoinCastP2F_ro Int deriving (Show, Eq)
data CoinCastF2P a = CoinCastF2P_OK | CoinCastF2P_Deliver a | CoinCastF2P_ro Bool deriving (Show, Eq)
data CoinCastA2F a = CoinCastA2F_Deliver PID (a, TransferTokens Int) | CoinCastA2F_ro Int deriving (Show, Eq)
data CoinCastF2A = CoinCastF2A_ro Bool deriving (Show, Eq)

-- TODO: currently adv sends for free, we should change that
{- We have   (CoinCastA2F t, TranferTokens Int) becuase runTokenA requires it -}
fMulticastAndCoinToken :: MonadFunctionalityAsync m ((t, TransferTokens Int), CarryTokens Int) =>
    Functionality (CoinCastP2F t, CarryTokens Int) (CoinCastF2P t, CarryTokens Int)
                  (CoinCastA2F t, TransferTokens Int) CoinCastF2A Void Void m 
                  --(CoinCastA2F t, CarryTokens Int) CoinCastF2A Void Void m 
fMulticastAndCoinToken (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  let sid = ?sid :: SID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticastAndCoinToken" $ snd sid
  let useTokens = False
  tokens <- newIORef 0
  -- strong coin requires the same coin for each party in a round
  coinFlips <- newIORef (empty :: Map Int Bool)
  
  let print x = do
          liftIO $ putStrLn $ x
  -- strong coin requires the same coin for each party in a round
  coinFlips <- newIORef (empty :: Map Int Bool)

  let require cond msg = 
            if not cond then do
                liftIO $ putStrLn $ "\n\n\t[fMulticastToken Error]>>>>>>>" ++ show msg ++ "\n"
                ?pass
                readChan =<< newChan
            else return ()
  
  if not $ member pidS ?crupt then do
    fork $ forever $ do
      (pid, x) <- readChan p2f
      case x of
        (CoinCastP2F_cast (m, DeliverTokensWithMessage st), SendTokens a) -> do
          require (a >= 0) "negative tokens sent"
          modifyIORef tokens $ (+) a
          if pid == pidS then do
{- TODO: is defaulting to sending 0 token the right thing or just halt ? -}
            ?leak ((m, DeliverTokensWithMessage st), SendTokens a)
            forMseq_ parties $ \pidR -> do
              eventually $ do
                tk <- readIORef tokens
                if (tk >= 1)  then do
                  --require (tk >= st) ("Not enough tokens. Need " ++ show st ++ ", have " ++ showf)
                  writeIORef tokens (max 0 (tk-1-st))
                  writeChan f2p (pidR, (CoinCastF2P_Deliver m, SendTokens (min st (tk-1))))
                else return () -- ?pass
            writeChan f2p (pidS, (CoinCastF2P_OK, SendTokens 0))
          else ?pass 
        (CoinCastP2F_ro r, SendTokens a) -> do
          --require (a>=0) "no free ro queries >:("
          liftIO $ putStrLn $ "ro request a: " ++ show a
          tk <- readIORef tokens
          --liftIO $ putStrLn $ "tokens bfore coin: " ++ show tk
          modifyIORef tokens $ (+) (a-1)
          --if r == 1 then writeChan f2p (pid, (CoinCastF2P_ro True, SendTokens 0))
          --else if r == 2 then writeChan f2p (pid, (CoinCastF2P_ro False, SendTokens 0))
          --else readChan =<< newChan
          cf <- readIORef coinFlips
          if not $ member r cf then do
            b <- ?getBit
            liftIO $ putStrLn $ "coin if not member"
            modifyIORef coinFlips $ Map.insert r b
            writeChan f2p (pid, (CoinCastF2P_ro b, SendTokens 0))
          else do
            liftIO $ putStrLn $ "coin already cast"
            b <- readIORef coinFlips >>= return . (! r)
            writeChan f2p (pid, (CoinCastF2P_ro b, SendTokens 0))
  else do
    delivered <- newIORef (empty :: Map PID ())
    fork $ forever $ do
      --(x, SendTokens tk) <- readChan a2f 
      (x, DeliverTokensWithMessage tk) <- readChan a2f 
      require (tk>=0) "negative tokens sent"
      modifyIORef tokens $ (+) tk
      case x of
        CoinCastA2F_Deliver pidR (m, DeliverTokensWithMessage st) -> do
          del <- readIORef delivered
          --if member pidR del then return ()
          if member pidR del then do
            ?pass
          else do
            tks <- readIORef tokens
            if  (tks >= st) then do 
            --require (tks >= st) ("not enough tokens. need " ++ show st ++ ", have " ++ show tks)
              modifyIORef tokens $ (subtract st)
              modifyIORef delivered $ Map.insert pidR ()
              writeChan f2p (pidR, (CoinCastF2P_Deliver m, SendTokens st))
            else ?pass
        CoinCastA2F_ro x -> do
{- TODO: should the adv directly observe this? -}
          require (tk > 0) "no free ro queries >:(" 
          cf <- readIORef coinFlips
          writeChan f2a (CoinCastF2A_ro True)
  return ()

data ABACast = AUX Int Bool | EST Int Bool deriving (Show, Eq)

{-
    Total token cost: 2N+2
        2 broadcasts
-}

data SBcastVariant = SBcastSmall | SBcastLarge | SBcastCorrect deriving (Show, Eq)
data SBSVariant = SBSSmall | SBSLarge | SBSCorrect deriving (Show, Eq)

sBroadcastBreak :: (MonadIO m, MonadITM m) => SBcastVariant -> SBSVariant ->
    IORef Int -> IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
    Chan () -> Chan () -> IORef (Map Bool Bool) -> Bool -> m () -> m ()
sBroadcastBreak castVariant valVariant tokens totSent tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
  --let (parties :: [PID], t :: Int, sssid :: String) = readNote "protABA" $ snd ?sid
  --let n = length parties
  let t = tThreshold
  let castThreshold = case castVariant of
                        SBcastSmall -> t
                        SBcastLarge -> t+2
                        SBcastCorrect -> t+1
  let svalThreshold = case valVariant of
                        SBSSmall -> 2*t
                        SBSLarge -> 2*t+2
                        SBSCorrect -> 2*t + 1
  (sBroadcastBroken castThreshold svalThreshold tokens totSent tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass)

sBroadcast :: (MonadIO m, MonadITM m) =>
    IORef Int -> IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
    Chan () -> Chan () -> IORef (Map Bool Bool) -> Bool -> m () -> m ()
sBroadcast = sBroadcastBreak SBcastCorrect SBSCorrect

--sBroadcast :: (MonadIO m, MonadITM m) =>
--    IORef Int -> IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
--    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
--    Chan () -> Chan () -> IORef (Map Bool Bool) -> Bool -> m () -> m ()
--sBroadcast tokens totSent tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
sBroadcastBroken :: (MonadIO m, MonadITM m) => Int -> Int ->
    IORef Int -> IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
    Chan () -> Chan () -> IORef (Map Bool Bool) -> Bool -> m () -> m ()
sBroadcastBroken castThreshold svalThreshold tokens totSent tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
    -- set the current bin_ptr[s_i] = False because main protocol will wait till one of them is True
    modifyIORef binptr $ Map.insert bit False
    vCount <- newIORef 0
    receivedESTFrom <- newIORef $ (Map.empty :: Map PID ())
    receivedAUXFrom <- newIORef $ (Map.empty :: Map PID ())

    -- the SSID for the sub-session of fMulticats this instance of sBroadcast will use      
    let sidmycast :: SID = (show ("sbcast", pid, round, bit), show (pid, parties, ""))
    liftIO $ putStrLn $ "\t\t\t\t[" ++ show pid ++ "] sbcast (" ++ show bit ++ ", " ++ show shouldBCast ++ ")"

    let multicast (x, DeliverTokensWithMessage st) = do
              tk <- readIORef tokens
              let neededTokens = (length parties) * (st+1)
              writeIORef tokens (max 0 (tk-neededTokens))
              liftIO $ putStrLn $ ">>>>>>> Multicasting [" ++ show pid ++ "]: ((" ++ show x ++ ", DeliverTokensWithMessage " ++ show st ++ "), SendTokens " ++ show (min tk neededTokens) ++ ")"
              
              writeChan p2f (sidmycast, (CoinCastP2F_cast (x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens)))
              readChan okChan

    if shouldBCast then do
        -- broadcast the proposed value
{- TOKENS: (N+1) N for users and 1 for ! -}
        --writeChan p2f (sidmycast, (CoinCastP2F_cast (EST round bit, DeliverTokensWithMessage 0), SendTokens 0))
        multicast (EST round bit, DeliverTokensWithMessage 0)
        --writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
        --readChan okChan 
    else
        return ()

    fork $ forever $ do
        -- assumed we're receiving from the correct session of fMulticast by the dispatcher
        -- in the main protocol body
        --(from, (m, SendTokens tks)) <- readChan f2p
        (from, m) <- readChan f2p

        case m of
            -- Receiving messages from other parties with TAG,S_VAL(v_i) where TAG is EST[r_i] where r_i is the round this sBroadcast is for
            --CastF2P_Deliver (EST r b) -> do
            CoinCastF2P_Deliver (EST r b) -> do
                -- Only consider messages received for the same `bit` and from other parties
                receivedFromPidS <- readIORef receivedESTFrom >>= return . (member from)

                -- Only accept EST messages from new parties
                if (b == bit) && (not receivedFromPidS) then do
                    -- bit should only be received on not broadcast
                    -- count how many we've received
                    modifyIORef vCount $ (+) 1
                    modifyIORef receivedESTFrom $ Map.insert from ()

                    v <- readIORef vCount
                    liftIO $ putStrLn $ "[" ++ show pid ++ ", " ++ show bit ++ "] vcount: " ++ show v

                    --if (v == (tThreshold + 1)) then do
                    if (v == castThreshold) then do
                        -- only broadcast EST round bit if we haven't before
                        if (not shouldBCast) then do
{- TOKENS: (N+1) -}
                            multicast (EST round bit, DeliverTokensWithMessage 0)
                            --writeChan p2f (sidmycast, (CoinCastP2F_cast (EST round bit, DeliverTokensWithMessage 0), SendTokens 0))
                            --readChan okChan
                            pass
                        else do
                            pass
                    --else if v == ((tThreshold * 2) + 1) then do
                    else if v == svalThreshold then do
                        -- if the second threshold is reached for this bit then set the svalue_i (i.e. the bin_ptr[bit]) to True
                        liftIO $ putStrLn $ "\nsBroadcast [" ++ show pid  ++ ", " ++ show bit ++ ", " ++ show round ++ ", " ++ show shouldBCast ++ "] svalue for " ++ show bit ++ " is True\n"
                        modifyIORef binptr $ Map.insert bit True
                        -- notify the main protocol that this sBroadcast value has been set to True
                        writeChan toMainChan ()  
                    else do
                        pass
                else pass
            _ -> pass 

    -- pass control back to the main protocol body
    writeChan toMainChan ()
        

--data ABAF2P = ABAF2P_Out Bool deriving Show
data ABAF2P = ABAF2P_Out Bool | ABAF2P_Ok deriving (Show, Eq)
data ABAThreshold = ABASmall | ABALarge | ABACorrect deriving (Show, Eq) 

protABABreak :: (MonadAsyncP m) => ABAThreshold -> SBcastVariant -> SBSVariant ->
    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
protABABreak abaVariant bcastVariant svalVariant (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd ?sid 
  let n = length parties

  let thresh = case abaVariant of
                --ABASmall -> n-t-1
                ABASmall -> n-t-1
                ABALarge -> n-t+1
                ABACorrect -> n-t
  (protABABroken thresh bcastVariant svalVariant (z2p, p2z) (f2p, p2f))

protABA :: (MonadAsyncP m) =>
    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
protABA (z2p, p2z) (f2p, p2f) = do
  (protABABreak ABACorrect SBcastCorrect SBSCorrect (z2p, p2z) (f2p, p2f))

protABABroken :: (MonadAsyncP m) => Int -> SBcastVariant -> SBSVariant -> 
    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
protABABroken thresh bcastVariant svalVariant (z2p, p2z) (f2p, p2f) = do
    let xyz :: Int = thresh
    let sid = ?sid :: SID
    let pid = ?pid :: PID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd sid 
    let n = length parties

    let ro_sid r = (show ("sRO", r), show("-1", parties, "")) 
    let gprint s r = do
                    liftIO $ putStrLn $ "\ESC[32m [" ++ show pid ++ ", " ++ show r ++ "] " ++ show s ++ "\ESC[0m"

{- [TOKENS] -}
    tokens <- newIORef 0
    totSent <- newIORef 0
    receivedAUXFrom <- newIORef $ (Map.empty :: Map PID ())

    -- bin_ptrs hold the s_values for each bit, initially both False
    binptr <- newIORef (empty :: Map Bool Bool)
    modifyIORef binptr $ Map.insert False False
    modifyIORef binptr $ Map.insert True False

    -- Separate views that counts unique parties that have sent a TRUE aux message for each round
    viewRTrue <- newIORef (empty :: Map Int Int)
    viewRFalse <- newIORef (empty :: Map Int Int)

    -- read message and route to either sBroadcast or to the main protocol
    f2sbChans <- newIORef (empty :: Map (Int, Bool) (Chan (PID, (CoinCastF2P ABACast))))
    f2sbOKChans <- newIORef (empty :: Map (Int, Bool) (Chan ()))
    sb2mainChans <- newIORef (empty :: Map Int (Chan ()))
    
    viewReady <- newChan
    f2mainOK <- newChan

    outOfTokens <- newIORef False

    -- roundSValue used by the dispatcher to ignore future messages for a round once one of the s_values is already True
    -- TODO: this may be the wrong approach, with a channel that notfied of a True s_value you never have the case that both s_values are True because the channel makes in synchronous in that sense, maybe this is a conquence of UC that we need to discuss 
    roundSValue <- newIORef (empty :: Map Int Bool)
    f2p' <- newChan
    f2p'' <- newChan
    decided <- newIORef False
    decision <- newIORef False 


    -- get the message channel for the SBroadcast instance
    let getSChan s r b d = do
            readIORef f2sbChans >>= return . (! (r, b))

    -- get the OK channel for the SBroadcast instance
    let getOKChan s r b d = do 
            readIORef f2sbOKChans >>= return . (! (r, b))

    -- Compute the ssid from the broadcast parameters
    -- Identify messages by sid, round, and bit of SBroadcast
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))

    -- get f2p input
    fork $ forever $ do
        (s, (m, SendTokens tks)) <- readChan f2p
        --liftIO $ putStrLn $ "adding tokens: " ++ show tks
        modifyIORef tokens $ (+) tks

        let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s

        case m of 
            CoinCastF2P_ro b ->
                writeChan f2p'' b
            _ -> do
                writeChan f2p' (s, m)
            --CastF2P_ro b -> do
            --    writeChan f2p'' b
            --_ -> do
            --    writeChan f2p' (s, m)
   

    -- dispatcher from F to sBroadcast and main protocol body  
    -- and dispatcher between sBroadcast and main protocol body
    fork $ forever $ do
        oot <- readIORef outOfTokens
        (s, m) <- readChan f2p'
        isDecided <- readIORef decided
        --readIORef viewRTrue >>= return . (("[" ++ ?pid ++ "] viewRTrue") ++) . show
        --readIORef viewRFalse >>= return . (("[" ++ ?pid ++ "] viewRFalse") ++) . show
        if not isDecided then do
            let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s
            let (sstring :: String, _pidS :: PID, _round :: Int, _bit :: Bool) = readNote "" $ fst s
            -- send to the right sBroadcast or the main protocol body based on ssid
            gprint ("getting something " ++ show m ++ " from " ++ show _pidS) _round
            case m of 
                CoinCastF2P_Deliver (EST r b) -> do
                --CastF2P_Deliver (EST r b) -> do
                    -- give the message to the sbcast for this round and bit
                    -- if one of the sbcasts has already set its svalues for TRUE for this round 
                    -- then ignore further messages. TODO: this prohibits the case in the code where
                    -- svalues for both sbcasts is TRUE
                    exists <- readIORef f2sbChans >>= return . (member (r, b))
                    --alreadySValues <- readIORef roundSValue >>= return . (! r)
                    gprint ("Exists " ++ show exists) r
                    --if exists && not alreadySValues then do
                    if exists then do
                        gprint ("Routing to SBCast") r
                        _toS <- getSChan s r b f2sbChans
                        writeChan _toS (pidS, m)
                    else do
                        ?pass 
                CoinCastF2P_Deliver (AUX r b) -> do
                    -- track the view[r_i]   
                    --shit1 <- readIORef viewRTrue 
                    --liftIO $ putStrLn $ "[" ++ show ?pid ++ "] viewRTrue: " ++ show shit1 
                    --shit2 <- readIORef viewRFalse
                    --liftIO $ putStrLn $ "[" ++ show ?pid ++ "] viewRFalse: " ++ show shit2
                    receivedFromPidS <- readIORef receivedAUXFrom >>= return . (member pidS)
                    if (not receivedFromPidS) then do
                      if b == True then do
                          modifyIORef viewRTrue $ Map.insertWith (\_ old -> old+1) r 1
                          numTrue <- readIORef viewRTrue >>= return . (! r)
                          liftIO $ putStrLn $ "\t\t\t\t\t\t[" ++ show pid ++ ", " ++ show m ++ "] num true: " ++ show numTrue ++ " from " ++ show pidS
                      else do
                          modifyIORef viewRFalse $ Map.insertWith (\_ old -> old+1) r 1
                          numFalse <- readIORef viewRFalse >>= return . (! r)
                          liftIO $ putStrLn $ "\t\t\t\t\t\t[" ++ show pid ++ ", " ++ show m ++ "] num false: " ++ show numFalse ++ " from " ++ show pidS
                      --shit1 <- readIORef viewRTrue 
                      --liftIO $ putStrLn $ "[" ++ show ?pid ++ "] viewRTrue: " ++ show shit1 
                      --shit2 <- readIORef viewRFalse
                      --liftIO $ putStrLn $ "[" ++ show ?pid ++ "] viewRFalse: " ++ show shit2
                      modifyIORef receivedAUXFrom $ Map.insert pidS ()
                      -- Determine whetherh view[r] is satisified for either of the bits
                      isTrue <- readIORef viewRTrue >>= return . (member r) 
                      isFalse <- readIORef viewRFalse >>= return . (member r)
                      result <- if isTrue && isFalse then do
                                    tN <- readIORef viewRTrue >>= return . (! r)
                                    fN <- readIORef viewRFalse >>= return . (! r)
                                    if tN == thresh && fN == thresh then return True else return False
                                else if isTrue then do 
                                    tN <- readIORef viewRTrue >>= return . (! r)
                                    if tN == thresh then return True else return False
                                else do
                                    fN <- readIORef viewRFalse >>= return . (! r)
                                    if fN == thresh then return True else return False
                      -- if some view[r] is satisfied notify the main code block
                      if result then writeChan viewReady () else ?pass
                    else return ()
                CoinCastF2P_OK -> do
                --CastF2P_OK -> do
                    -- Deliver the OK message back from fMulticast when bcasting
                    -- to either the sbcast or the main body
                    if sstring == "sbcast" then do
                        _toOK <- getOKChan s _round _bit f2sbOKChans
                        writeChan _toOK ()
                    else
                        writeChan f2mainOK ()
                _ -> 
                    writeChan viewReady ()
        else ?pass

    -- Create the channels for the sBroadcast to use
    -- One channel for p2f --> sbcast, one for p2f OK --> sbcast, and sbcast --> main
    let newSBcastChan _round _bit _f2sb _f2sbok _sb2main = do
                _S <- newChan
                _OK <- newChan
                _toMain <- newChan
                modifyIORef _f2sb $ Map.insert (_round, _bit) _S
                modifyIORef _f2sbok $ Map.insert (_round, _bit) _OK

                exists <- readIORef _sb2main >>= return . (member _round)
                if exists then do
                    ch <- readIORef _sb2main >>= return . (! _round)
                    return (_S, _OK, ch)
                else do
                    modifyIORef _sb2main $ Map.insert _round _toMain
                    return (_S,_OK, _toMain)

    -- function to deploy a new instance of sBroadcast with round r and bit b
    let newSBCast r b shouldBroadcast = do
            (f2sb, f2sbok, sb2main) <- newSBcastChan r b f2sbChans f2sbOKChans sb2mainChans
            --sBroadcast tokens totSent t pid parties r b f2sb p2f f2sbok sb2main binptr shouldBroadcast ?pass
            sBroadcastBreak bcastVariant svalVariant tokens totSent t pid parties r b f2sb p2f f2sbok sb2main binptr shouldBroadcast ?pass
            -- wait for the sBCast to do spawn and do its thing then return control back to main body
            s2MainChan <- readIORef sb2mainChans >>= return . (! r) 
            readChan s2MainChan
    
    round <- newIORef 0
   
    -- Get a common coin from the random oracle 
    let commonCoinR r = do
        liftIO $ putStrLn $ "Making a god damn COIN FLIP"
        tk <- readIORef tokens
        if (tk >= 1) then do
          modifyIORef tokens $ (subtract 1)
          liftIO $ putStrLn $ "getting coin flip"
          writeChan p2f (ro_sid r, (CoinCastP2F_ro r, SendTokens 1))
          b <- readChan f2p'' -- get OK back from fMulticast
          liftIO $ putStrLn $ "waiting for thebit back"
          return (Just b)
        else do 
          liftIO $ putStrLn "no tokens to call coin" 
          return (Nothing)
    
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))
    
    let gprint s r = do
          liftIO $ putStrLn $ "\ESC[32m [" ++ show pid ++ ", " ++ show r ++ "] " ++ show s ++ "\ESC[0m"
    
    let multicast s (x, DeliverTokensWithMessage st) = do
              tk <- readIORef tokens
              let neededTokens = (length parties) * (st+1)
              writeIORef tokens (max 0 (tk-neededTokens))
              liftIO $ putStrLn $ ">>>>>>> MAIN Multicasting [" ++ show pid ++ "]: ((" ++ show x ++ ", DeliverTokensWithMessage " ++ show st ++ "), SendTokens " ++ show (min tk neededTokens) ++ ")"
              modifyIORef totSent $ (+) (min tk neededTokens)  
              writeChan p2f (s, (CoinCastP2F_cast (x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens)))
              ts <- readIORef totSent 
              --gprint ("\n\ttotal send: " ++ show ts) 0
              readChan f2mainOK

  
{- Start of the main body of the protocol. Above is just dispatching communication between 
   sBroadcast and this main loop below. -}

    -- on input propose(v) from Z:
    (msg, SendTokens tks) <- readChan z2p

    firstIteration <- newIORef True
    firstDecide <- newIORef True
    fork $ forever $ do
      readChan z2p  
      ?pass

    modifyIORef tokens $ (+) tks
    case msg of
            ClockP2F_Pass -> error "shouldn't be passing anything"
            ClockP2F_Through v -> do
                r <- readIORef round
                s <- return (not v)
                supportCoin <- (return False)
                supportCoin <- newIORef False
{- [TOKEN]: this bCast doesn't broadcast immediately, only the 1 if the condition is triggered 
    becuase shouldBroadcast = False -}
                liftIO $ putStrLn $ "[" ++ show ?pid ++ "] input is " ++ show v
                newSBCast 1 s False 

                fork $ forever $ do
                    isDecided <- readIORef decided
                    --if not isDecided then do
                    modifyIORef round $ (+) 1
                    r <- readIORef round

                    -- no s_value in this round yet
                    modifyIORef roundSValue $ Map.insert r False 
                    liftIO $ putStrLn $ "\n[" ++ show pid ++ "] new round " ++ show r ++ "\n"

{- [Token]: triggerssibly two broacasts so 2n max? -}
                    sc <- readIORef supportCoin
                    --liftIO $ putStrLn $ "[" ++ show ?pid ++ "] supportCoin " ++ show sc
                    newSBCast r (not s) (not sc)
                    -- for the first check, it is okay to give them the same channel
                    -- because one of them will aways be True first and that's all we are about
                    -- later on though, we may encounter another message on this channel

                    -- wait for one of the processes to write to the main thread
                    -- saying that they set binptr[b] = True
-- Here it makes sense to do the UC-required write operations 
-- namely, saying OK to Z
-- outputting the decision to Z
-- or ?passing if neither applies
                    first <- readIORef firstIteration
                    firstDec <- readIORef firstDecide
                    if first then do
                      liftIO $ putStrLn $ "\n[" ++ show ?pid ++ "] Oking\n"
                      writeChan p2z (ABAF2P_Ok, SendTokens 0)
                      modifyIORef firstIteration $ not
                    else if isDecided && firstDec then do
                      liftIO $ putStrLn $ "\n[" ++ show ?pid ++ "] Deciding\n"
                      dec <- readIORef decision
                      writeChan p2z ((ABAF2P_Out dec), SendTokens 0)
                      modifyIORef firstDecide $ not
                    else do
                      liftIO $ putStrLn $ "\n[" ++ show ?pid ++ "] passing\n"
                      ?pass 

                    s2MainChan <- readIORef sb2mainChans >>= return . (! r) 
                    () <- readChan s2MainChan
                    modifyIORef roundSValue $ Map.insert r True
                    liftIO $ putStrLn $ "finished s2MainChan"

                    -- check which bin_ptr[bit] is True
                    b0 <- readIORef binptr >>= return . (! False)
                    b1 <- readIORef binptr >>= return . (! True)
                    
                    liftIO $ putStrLn $ "[" ++ show ?pid ++ "] b0: " ++ show b0 ++ ", b1: " ++ show b1
                    
                    if b0 && b1 then error $ "[" ++ show ?pid ++ ", " ++ show r ++ "] has both true whic shouldn't happen"
                    else return ()

                    -- set w for broadcast
                    sc <- readIORef supportCoin
                    randomChoice <- ?getBit
                    let w = if randomChoice then
                              if sc
                              then s
                              else if b0
                              then False
                              else True 
                            else
                              if sc
                              then s
                              else if b1
                              then True
                              else False
   
                    let sidMain :: SID = (show ("maincast", pid, r, w), show (pid, parties, ""))
{- [Token] another bcast of N -}
                    --writeChan p2f (sidMain, (CoinCastP2F_cast (AUX r w, DeliverTokensWithMessage 0), SendTokens 0))
                    --readChan f2mainOK
                    gprint "main multicasting" r
                    multicast sidMain (AUX r w, DeliverTokensWithMessage 0)
                    ?pass                   -- WRITE

                    -- wait for view[r]
                    readChan viewReady      -- READ
                    gprint "got viewReady" r

                    -- get strong common coin
                    --liftIO $ putStrLn $ "main common coin"
                    bres <- commonCoinR r
                    case bres of
                      Just b -> do
                        gprint ("Common coin: " ++ show b) r 
                        
                        -- decide?
                        t <- readIORef viewRTrue >>= return . (member r)
                        f <- readIORef viewRFalse >>= return . (member r)
                        --gprint ("\t\t t: " ++ show t ++ " f: " ++ show f) r
                        --supportCoin <- if t && f then do
                        writeIORef supportCoin =<< if t && f then do
                                           return True
                                       else if t || f then do 
                                           if t then do
                                               liftIO $ putStrLn $ "[" ++ show ?pid ++ "] deciding True"
                                               if not isDecided then do
                                                 modifyIORef decided $ not
                                                 writeIORef decision True
                                                 --writeChan p2z ((ABAF2P_Out True), SendTokens 0)
                                               else return ()
                                           else do
                                               liftIO $ putStrLn $ "[" ++ show ?pid ++ "] deciding False"
                                               if not isDecided then do
                                                 --writeChan p2z ((ABAF2P_Out False), SendTokens 0)
                                                 modifyIORef decided $ not
                                                 writeIORef decision False
                                               else return ()
                                           return True
                                       else do  
                                           return False
                        --sc <- readIORef supportCoin
                        --liftIO $ putStrLn $ "[" ++ show ?pid ++ "] sc: " ++ show sc
                        -- set the binptr values back to False for the next round
                        modifyIORef binptr $ Map.insert True False
                        modifyIORef binptr $ Map.insert False False
                        return ()
                      Nothing -> return ()
                    --else do
                    --    ?pass
                    --    return ()
     
    return () 

type ABATranscript = [Either
                        (SttCruptA2Z
                          (SID, (CoinCastF2P ABACast, CarryTokens Int))
                          (Either 
                            (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                            (SID, CoinCastF2A)))
                        (PID, (ABAF2P, CarryTokens Int))]


testEnvABAHonestAllTrue 
    :: (MonadEnvironment m) =>
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      --(Either ClockA2F (SID, (CoinCastA2F ABACast, CarryTokens Int)))), CarryTokens Int) Void
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) ABATranscript m
testEnvABAHonestAllTrue z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMulticastCoin", show (["Alice", "Bob", "Charlie", "Mary"], 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z

   --let sid1 :: SID = ("sidX", show ("Alice", ["Alice", "Bob", "Charlie", "Mary"], ""))
    () <- readChan pump
    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 100))
    
    () <- readChan pump
    writeChan z2p ("Bob", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Charlie", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Mary", (ClockP2F_Through True, SendTokens 100))
   
    -- Deliver all EST messages to Alice
    forMseq_ [0,3,6,9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all EST messages to Bob
    forMseq_ [0,2,4,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliver all EST messages to Charlie
    forMseq_ [0,1,2,3] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all EST messages to Mary
    forMseq_ [0,0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliver all AUX messages to Alice 
    forMseq_ [0,3,6,9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all AUX messages to Bob
    forMseq_ [0,2,4,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliver all AUX messages to Charlie
    forMseq_ [0,1,2,3] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all AUX messages to Mary
    forMseq_ [0,0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    () <- readChan pump
    tr <- readIORef transcript
    writeChan outp tr

testABAHonestAllTrue = runITMinIO 120 $ execUC testEnvABAHonestAllTrue (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoinToken) dummyAdversaryToken

testEnvABAOneCruptOneRound z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Bob",())]

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z

    () <- readChan pump
    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 100))
    
    --() <- readChan pump
    --writeChan z2p ("Bob", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Charlie", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Mary", (ClockP2F_Through True, SendTokens 100))
   
    -- Deliver all EST messages
    forMseq_ [0,3,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Send Bob's EST to Alice and Charlie
    () <- readChan pump
    let bobSID :: SID = (show ("sbcast", "Bob", 1, False), show ("Bob", parties, ""))
    --writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Alice" $ EST 1 False)
    --writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Alice" $ (EST 1 False, DeliverTokensWithMessage 0)), SendTokens 0)))), SendTokens 0)
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Alice" $ (EST 1 False, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    
    () <- readChan pump
    --writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Charlie" $ (EST 1 True, DeliverTokensWithMessage 0)), SendTokens 0)))), SendTokens 0)
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Charlie" $ (EST 1 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)

    -- Deliver all EST messages to corrupt Bob
    forMseq_ [0,2,4] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Send Bob's EST to Mary
    () <- readChan pump
    --writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Mary" $ (EST 1 False, DeliverTokensWithMessage 0)), SendTokens 0)))), SendTokens 0)
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Mary" $ (EST 1 False, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)

    -- Deliverall EST messages to Charlie
    forMseq_ [0,1,2] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliverall EST messages to Mary
    forMseq_ [0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- We only stop at the honest partys' s_broadcast setting s_value[1/True] = True
    -- this environment offers nothing more elucidating than checking handling of corrupt party.

    () <- readChan pump
    tr <- readIORef transcript
    writeChan outp tr

testABAOneCruptOneRound = runITMinIO 120 $ execUC testEnvABAOneCruptOneRound (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoinToken) dummyAdversaryToken

testEnvABAHonestMultiRound z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z

    -- tl;dr give half parties True as Input and the other half False and let them reach a consenus on the bit
    () <- readChan pump
    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 100))
    
    () <- readChan pump
    writeChan z2p ("Bob", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Charlie", (ClockP2F_Through False, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Mary", (ClockP2F_Through False, SendTokens 100))
    () <- readChan pump

    liftIO $ putStrLn $ "\n\ESC[31m Alice and Bob should rebroadcast False\ESC[0m\n"
    -- Deliver ESTs False from Charlie and Mary first
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver 8))), SendTokens 0)
        () <- readChan pump
        return ()


    liftIO $ putStrLn $ "\n\ESC[31m Mary and Charlie should rebroadcast True\ESC[0m\n"
    -- Deliver the ESTs from Alice and Bob
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver 0))), SendTokens 0)
        () <- readChan pump
        return ()


    liftIO $ putStrLn $ "\n\ESC[31m Everyone's s_value for False should be set to True\ESC[0m\n"
    -- Deliver Alice and Bob's rebroadcasted Falses
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver 0))), SendTokens 0)
        () <- readChan pump
        return ()

    liftIO $ putStrLn $ "\n\ESC[31m nothing should happen because they have all already accepted False\ESC[0m\n"
    -- Deliver Charlie and Mary's rebroadcasted Trues (SHOULD DO NOTHING)
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver 0))), SendTokens 0)
        () <- readChan pump
        return ()
  
    liftIO $ putStrLn $ "\n\ESC[31m Everone gets 3 AUX messages and does something \ESC[0m\n"  
    -- Deliver 3 AUX messages to everyone 
    forMseq_ [0..13] $ \x -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver 0))), SendTokens 0)
        () <- readChan pump
        return ()

    --() <- readChan pump
    tr <- readIORef transcript
    writeChan outp tr
testABAHonestMultiRound = runITMinIO 120 $ execUC testEnvABAHonestMultiRound (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoinToken) dummyAdversaryToken

testEnvABAMinority :: (MonadEnvironment m) => 
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      --(Either ClockA2F (SID, (CoinCastA2F ABACast, CarryTokens Int)))), CarryTokens Int) Void
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) ABATranscript m
testEnvABAMinority z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Frank"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList $ [("Frank",())])
    () <- readChan pump

    let valueFilter msg = case msg of
                            AUX r b -> (2, r, b)
                            EST r b -> (1, r, b)

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z
    (deliverer, deliverByPairs, getByPairs, getBySender, getByReceiver, getByFilter) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter
   
    c <- envQueueSize z2a clockChan 1000 
    let gprint s = do
                    liftIO $ putStrLn $ "\ESC[32m" ++ show s ++ "\ESC[0m"
    let yprint s = do liftIO $ putStrLn $ "\t\t\t\ESC[33m" ++ show s ++ "\ESC[0m"

    -- tl;dr give half parties True as Input and the other half False and let them reach a consenus on the bit
    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 64))
    
    () <- readChan pump
    writeChan z2p ("Bob", (ClockP2F_Through True, SendTokens 64))

    () <- readChan pump
    writeChan z2p ("Charlie", (ClockP2F_Through True, SendTokens 64))

    () <- readChan pump
    writeChan z2p ("Dave", (ClockP2F_Through False, SendTokens 64))

    () <- readChan pump
    writeChan z2p ("Eve", (ClockP2F_Through False, SendTokens 64))

    () <- readChan pump
    let rounds = 1
    forMseq_ [1..rounds] $ \r -> do
      -- deliver (1, 1, T) to A,B,C
      c <- envQueueSize z2a clockChan 0
      estT <- getByFilter (1, r, True)
      gprint ("EstT: " ++ show estT)
      estToA <- getByReceiver ("Alice" :: PID)
      estToB <- getByReceiver ("Bob" :: PID)
      estToC <- getByReceiver ("Charlie" :: PID)
      let estToABC = estToA ++ estToB ++ estToC
      estF <- getByFilter (1, r, False)
      estToD <- getByReceiver "Dave"
      estToE <- getByReceiver "Eve"
      let estToDE = estToD ++ estToE
      let estTtoABC = intersect estToABC estT
      let estFtoDE = intersect estToDE estF
      gprint ("EST(T) to ABC: " ++ show estTtoABC)
      gprint ("EST(F) to DE: " ++ show estFtoDE)
      forMseq_ (deliverListAll (estTtoABC ++ estFtoDE)) $ \i -> deliverer [] i  

      let minimumIdx = (c - (length (estTtoABC ++ estFtoDE)))
      gprint ("minimum index: " ++ show minimumIdx)

      let makeSBCastSid ps p r b = (show ("sbcast", p, r, b), show (p, ps, ""))
      let makeMainSid ps p r w = (show ("maincast", p, r, w), show (p, ps, ""))
     
      -- send 4 x AUX(T) to A
      auxT <- getByFilter (2, r, True)
      auxToAAll <- getByReceiver "Alice"
      gprint ("all aux to A: " ++ show auxToAAll)
      let auxToA = filter (\x -> x >= minimumIdx) (intersect auxToAAll auxT)
      gprint ("Aux to A: " ++ show auxToA)
      forMseq_ (deliverListAll auxToA) $ \i -> deliverer [] i
      --let bobSID :: SID = (show ("sbcast", "Bob", 1, False), show ("Bob", parties, ""))
      let franksid1 = makeMainSid parties "Frank" r True
      writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (franksid1, ((CoinCastA2F_Deliver "Alice" $ (AUX 1 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
      () <- readChan pump
      yprint "Alice has decided T"

      -- give EST F to B,C to get binptr[F] = T
      yprint "making bin_ptr[F] = true for B,C"
      forMseq_ [1..2] $ \_ -> do
        estF <- getByFilter (1, r, False)
        estToB <- getByReceiver ("Bob" :: PID)
        estToC <- getByReceiver ("Charlie" :: PID)
        let estFtoBC = intersect estF (estToB ++ estToC)
        yprint ("est messages to BC: " ++ show estFtoBC)
        forMseq_ (deliverListAll estFtoBC) $ \i -> deliverer [] i

      return ()
      
    tr <- readIORef transcript
    writeChan outp tr

testABAMinority = do
  let prot () = protABABreak ABASmall SBcastSmall SBSSmall
  tr <- runITMinIO 120 $ execUC 
    testEnvABAMinority 
    (runAsyncP $ prot ())
    (runAsyncF $ bangFAsync $ fMulticastAndCoinToken) 
    dummyAdversaryToken
  return () 

data ABAA2F = ABAA2F_Decide Bool | ABAA2F_Input PID Bool deriving Show
data ABAF2A = ABAF2A_Ok deriving Show

-- fABA should leak the inputs of each of the parties, the simulator needs to guarantee BBC-validity where if every party proposes the same value, they all agree on that value 
fABA :: MonadFunctionalityAsync m (PID, (Bool, CarryTokens Int)) =>
    Functionality (Bool, CarryTokens Int) (ABAF2P, CarryTokens Int) (ABAA2F, CarryTokens Int) ABAF2A Void Void m 
    --Functionality (Bool, CarryTokens Int) ABAF2P (ABAA2F, CarryTokens Int) ABAF2A Void Void m 
fABA (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fABA" $ snd sid

    inputs <- newIORef (empty :: Map PID Bool)
    decision <- newIORef False
    tokens <- newIORef 0 

    let countInputs = do
                    numTrue <- readIORef inputs >>= return . sum . map (\x -> if x then 1 else 0) . Map.elems
                    numFalse <- readIORef inputs >>= return . sum . map (\x -> if not x then 1 else 0) . Map.elems
                    return (numTrue, numFalse)
    let isAdvChoice = do
        countInputs >>= (\(nt, nf) -> return (((nt > t) && (nf > t)), nt, nf))

    -- party inputs and schedule decision when inputs from honest parties
    fork $ forever $ do
        (pid, (m :: Bool, SendTokens tk)) <- readChan p2f
        modifyIORef tokens $ (+) 1
        exists <- readIORef inputs >>= return . (member pid)
        if not exists then do
            modifyIORef inputs $ Map.insert pid m
            ?leak (pid, (m, SendTokens tk))
            
            ready <- readIORef inputs >>= return . ((length parties) ==) . length . Map.keys
            if ready then do
                b <- ?getBit
                isAdvChoice >>= \(u, nt, nf) ->
                       writeIORef decision $ if u then b else if (nt > t) then True else False

                forMseq_ parties $ \pidX -> do
                    eventually $ do
                      tk <- readIORef tokens
                      writeIORef tokens (tk-1)
                      (readIORef decision >>= \d -> writeChan f2p (pidX, (ABAF2P_Out d, SendTokens 0)))
                return ()
            else return ()
            writeChan f2p (pid, (ABAF2P_Ok, SendTokens 0))
            -- ?pass
        else error ("second input for same party " ++ show pid)
    
    -- adversary can set crupt inputs and decide bit
    fork $ forever $ do
        (m, SendTokens tk) <- readChan a2f
        modifyIORef tokens $ (+) tk
        case m of 
            -- adv can override any crupt party's input
            ABAA2F_Input p b -> do
                if not $ member p ?crupt then modifyIORef inputs $ Map.insert p b else return ()
            -- if adv choice is set then adv chooses bit
            ABAA2F_Decide b -> 
                isAdvChoice >>= \(c,_,_) -> if c then writeIORef decision b else return ()
        writeChan f2a ABAF2A_Ok
        -- ?pass
    return ()

--- TODO: if there are n=5 parties. 3 of them propose 0 and 2 of the propose 1: is it still possible for them to decide on 0 given the right ordering of delivering the messages? It seems to me that it's a tossup only when there are equal numbers of people proposing 0 and 1. Then the delivery order matters.

-- TODO: the environment doens't compile because the dummyAdversaryToken is written to work with !fMulticast rater than a generic functionality like fABA.
--testEnvfABAHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
--    let parties = ["Alice", "Bob", "Charlie", "Mary"]
--    let sid = ("sidfABA", show (parties, 1, ""))
--    writeChan z2exec $ SttCrupt_SidCrupt sid empty 
--
--    fork $ forever $ do
--        --(pid, (s, m)) <- readChan p2z
--        (pid, m) <- readChan p2z
--        case m of
--            (ABAF2P_Out b, SendTokens tks) -> liftIO $ putStrLn $ "\ESC[31mParty [" ++ show pid ++ "] decided " ++ show b ++ "\ESC[0m"
--            _ -> printEnvReal "OK"
--        ?pass
--
--    fork $ forever $ do 
--        m <- readChan a2z
--        liftIO $ putStrLn $ "Z: a sent " ++ show m 
--        ?pass
--
--    return ()
--    () <- readChan pump
--    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 0))
--    () <- readChan pump
--    writeChan z2p ("Bob", (ClockP2F_Through True, SendTokens 0))
--    () <- readChan pump
--    writeChan z2p ("Charlie", (ClockP2F_Through False, SendTokens 0))
--    () <- readChan pump
--    writeChan z2p ("Mary", (ClockP2F_Through False, SendTokens 0))
--
--  -- Adversary should be able to set the bit now
--    () <- readChan pump
--    writeChan z2a $ ((SttCruptZ2A_A2F (Right ((ABAA2F_Decide True, SendTokens 0)))), SendTokens 0)
--
--    forMseq_ [0..3] $ \_ -> do
--        () <- readChan pump
--        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver 0))), SendTokens 0)
--   
--  --writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Charlie" $ (EST 1 True, DeliverTokensWithMessage 0)), SendTokens 0)))), SendTokens 0)
--
--
--testfABAHonest= runITMinIO 120 $ execUC testEnvfABAHonest idealProtocolToken  (runAsyncF $ fABA) dummyAdversaryToken


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

--simABA :: MonadAdversary m => Adversary (SttCruptZ2A (ClockP2F (SID, CastP2F ABACast))
--                                            (Either ClockA2F (SID, CastA2F ABACast)))
--                                        (SttCruptA2Z (SID, CastF2P ABACast)
--                                            (Either (ClockF2A (SID, ABACast))
--                                                    (SID , CastF2A ABACast)))
--                                        ABAF2P (ClockP2F Bool)
--                                        (Either (ClockF2A (PID, Bool)) ABAF2A) (Either ClockA2F ABAA2F) m

{- Known compiler complaints
   * the compiler complains that we have 
-} 
simABA :: MonadAdversary m => Adversary 
  ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int)
  (SttCruptA2Z (SID, (CoinCastF2P ABACast, CarryTokens Int))
               (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                       (SID, CoinCastF2A)))
  (ABAF2P, CarryTokens Int) (ClockP2F (Bool, CarryTokens Int))
  (Either (ClockF2A (PID, (Bool, CarryTokens Int))) ABAF2A) (Either ClockA2F (ABAA2F, CarryTokens Int)) m
simABA (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
    let sid :: SID = ?sid
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "ABA" $ snd sid

    numTrue <- newIORef 0
    numFalse <- newIORef 0
    partiesToDeliver <- newIORef parties

    -- routing z2a <-->
    sbxpump <- newChan
    sbxz2p <- newChan
    sbxp2z <- newChan
    sbxz2f <- newChan

    let sbxEnv z2exec (p2z', z2p') (a2z', z2a') (f2z', z2f') pump' outp' = do
        writeChan z2exec $ SttCrupt_SidCrupt ?sid ?crupt

        forward p2z' sbxp2z
        forward sbxz2p z2p'

        forward z2a z2a'
        forward a2z' a2z

        forward sbxz2f z2f'

        forward pump' sbxpump
    
        return ()

    let sbxBullRand () = bangFAsync fMulticastAndCoinToken
   
    -- monitor the sandbox for outputs  
    chanOk <- newChan
    
    fork $ forever $ do
        mf <- readChan sbxp2z
        case mf of
            (_pidS, (ABAF2P_Ok, SendTokens tk')) -> writeChan chanOk ()
            (_pidS, (ABAF2P_Out b, SendTokens tk')) -> do
                -- simulator just tries to force the bit: give all crupt
                -- parties b as input and try to force the decision
                forMseq_ (Map.keys ?crupt) $ \pidC -> do
                    writeChan a2p (pidC, ClockP2F_Through (b, SendTokens 0))
                    readChan p2a  --OK messsage

                -- also try to set the bit in fABA just in case
                writeChan a2f (Right (ABAA2F_Decide b, SendTokens 0))
                readChan f2a --OK
    
                -- Deliver this pid's output in fABA
                idx <- readIORef partiesToDeliver >>= return . (findIndex (== _pidS))
                case idx of
                    Just x -> do 
                        modifyIORef partiesToDeliver (deleteNth x)
                        writeChan a2f (Left (ClockA2F_Deliver x))
                    _ -> error "pid that doens't exist"
        return ()
    let handleLeak (pid, (b, SendTokens a)) = do
        printAdv $ "handleLeak simulator"
        --let (pid, b) = m
        case b of
            True -> modifyIORef numTrue (+ 1)
            False -> modifyIORef numFalse (+ 1)
        writeChan sbxz2p (pid, (ClockP2F_Through b, SendTokens a))
        () <- readChan chanOk
        --() <- readChan sbxpump
        return ()

    syncLeaks <- makeSyncLog handleLeak $ do
        writeChan a2f $ Left ClockA2F_GetLeaks
        mf <- readChan f2a
        
        let Left (ClockF2A_Leaks leaks) = mf
        return leaks

    let sbxProt () = protABA

    let sbxAdv (z2a',a2z') (p2a',a2p') (f2a',a2f') = do
        fork $ forever $ do
            (mf, SendTokens _) <- readChan z2a'
            printAdv $ show "Intercepted z2a'" ++ show mf
            syncLeaks
            printAdv $ "forwarding into the sandbox"
            case mf of
                SttCruptZ2A_A2F f -> writeChan a2f' f
                SttCruptZ2A_A2P pm -> writeChan a2p' pm
        fork $ forever $ do
            m <- readChan f2a'
            liftIO $ putStrLn $ show "f2a'" ++ show m
            writeChan a2z' $ SttCruptA2Z_F2A m
        fork $ forever $ do
            (pid,m) <- readChan p2a'
            liftIO $ putStrLn $ "p2a'"
            writeChan a2z' $ SttCruptA2Z_P2A (pid, m)
        return ()

    mf <- selectRead z2a f2a

    fork $ execUC_ sbxEnv (runAsyncP $ sbxProt ()) (runAsyncF (sbxBullRand ())) sbxAdv
    () <- readChan sbxpump

    case mf of
        Left m -> writeChan z2a m
        Right m -> writeChan f2a m

    fork $ forever $ do
        () <- readChan sbxpump
        return ()

    return ()


testEnvSimHonest 
  :: (MonadEnvironment m) =>
  Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
    (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                 (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                         (SID, CoinCastF2A)))
    ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                  --(Either ClockA2F (SID, (CoinCastA2F ABACast, CarryTokens Int)))), CarryTokens Int) Void
                  (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
    (ClockZ2F) ABATranscript m
testEnvSimHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMulticastCoin", show (["Alice", "Bob", "Charlie", "Mary"], 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z

   --let sid1 :: SID = ("sidX", show ("Alice", ["Alice", "Bob", "Charlie", "Mary"], ""))
    () <- readChan pump
    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 100))
    
    () <- readChan pump
    writeChan z2p ("Bob", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Charlie", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Mary", (ClockP2F_Through True, SendTokens 100))
   
    -- Deliver all EST messages to Alice
    forMseq_ [0,3,6,9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all EST messages to Bob
    forMseq_ [0,2,4,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliver all EST messages to Charlie
    forMseq_ [0,1,2,3] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all EST messages to Mary
    forMseq_ [0,0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliver all AUX messages to Alice 
    forMseq_ [0,3,6,9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all AUX messages to Bob
    forMseq_ [0,2,4,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliver all AUX messages to Charlie
    forMseq_ [0,1,2,3] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)
    
    -- Deliver all AUX messages to Mary
    forMseq_ [0,0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    () <- readChan pump
    writeChan outp =<< readIORef transcript
 
testSimHonest = runITMinIO 120 $ execUC testEnvSimHonest idealProtocolToken (runAsyncF $ fABA) (runTokenA $ simABA)

testCompare :: IO Bool
testCompare = runITMinIO 120 $ do
    liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
    t1 <- execUC
            testEnvSimHonest
            (runAsyncP protABA)
            (runAsyncF $ bangFAsync $ fMulticastAndCoinToken)
            dummyAdversaryToken
    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
    t2 <- execUC
            testEnvSimHonest
            idealProtocolToken
            (runAsyncF $ fABA)
            simABA
    return (t1 == t2)
----prop_abaequivocation = monadicIO $ do
----    outputs <- newIORef (Set.empty :: Set Bool)
----
----    testQuickCheckEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
----        let sid = ("sidTestEnvMulticastCoin", show (["Alice", "Bob", "Charlie", "Mary"], 1, ""))
----        writeChan z2exec $ SttCrupt_SidCrupt sid empty 
----    
----        transcript <- newIORef []
---- 
----        fork $ forever $ do
----            --(pid, (s, m)) <- readChan p2z
----            (pid, m) <- readChan p2z
----            modifyIORef transcript (++ [Right (pid, m)])
----            case m of
----                ABAF2P_Out b -> do
----                    liftIO $ putStrLn $ "\ESC[33mParty [" ++ show pid ++ "] decided " ++ show b ++ "\ESC[0m"
----                    modifyIORef outputs $ Set.insert b
----                _ -> printEnvReal "OK"
----            ?pass
----    
----        fork $ forever $ do 
----            m <- readChan a2z
----            modifyIORef transcript (++ [Left m])
----            liftIO $ putStrLn $ "Z: a sent " ++ show m 
----            ?pass
----        () <- readChan pump
----        writeChan z2p ("Alice", ClockP2F_Through True)
----        
----        () <- readChan pump
----        writeChan z2p ("Bob", ClockP2F_Through True)
----
----        () <- readChan pump
----        writeChan z2p ("Charlie", ClockP2F_Through True)
----
----        () <- readChan pump
----        writeChan z2p ("Mary", ClockP2F_Through True)
----   
----        -- Deliver all EST messages to Alice
----        forMseq_ [0,3,6,9] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----        
----        -- Deliver all EST messages to Bob
----        forMseq_ [0,2,4,6] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----
----        -- Deliver all EST messages to Charlie
----        forMseq_ [0,1,2,3] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----        
----        -- Deliver all EST messages to Mary
----        forMseq_ [0,0,0,0] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----
----        -- Deliver all AUX messages to Alice 
----        forMseq_ [0,3,6,9] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----        
----        -- Deliver all AUX messages to Bob
----        forMseq_ [0,2,4,6] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----
----        -- Deliver all AUX messages to Charlie
----        forMseq_ [0,1,2,3] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----        
----        -- Deliver all AUX messages to Mary
----        forMseq_ [0,0,0,0] $ \x -> do
----            () <- readChan pump
----            writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
----
----        () <- readChan pump
----        writeChan outp =<< readIORef transcript
----
----    runITMinIO 120 $ do
----                execUC
----                testEnvSimHonest
----                (runAsyncP protABA)
----                (runAsyncF $ bangFAsync fMulticastAndCoin)
----                dummyAdversary
----
----    readIORef outputs >>= \x -> return ((Set.size x) ?== 1)


testEnvSimCrupt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Bob",())]

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z

    () <- readChan pump
    writeChan z2p ("Alice", (ClockP2F_Through True, SendTokens 100))
    
    --() <- readChan pump
    --writeChan z2p ("Bob", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Charlie", (ClockP2F_Through True, SendTokens 100))

    () <- readChan pump
    writeChan z2p ("Mary", (ClockP2F_Through True, SendTokens 100))
   
    -- Deliver all EST messages
    forMseq_ [0,3,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Send Bob's EST to Alice and Charlie
    () <- readChan pump
    let bobSID :: SID = (show ("sbcast", "Bob", 1, False), show ("Bob", parties, ""))
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Alice" $ (EST 1 False, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    
    () <- readChan pump
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Charlie" $ (EST 1 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)

    -- Deliver all EST messages to corrupt Bob
    forMseq_ [0,2,4] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Send Bob's EST to Mary
    () <- readChan pump
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (bobSID, ((CoinCastA2F_Deliver "Mary" $ (EST 1 False, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)

    -- Deliverall EST messages to Charlie
    forMseq_ [0,1,2] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- Deliverall EST messages to Mary
    forMseq_ [0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ ((SttCruptZ2A_A2F $ (Left (ClockA2F_Deliver x))), SendTokens 0)

    -- We only stop at the honest partys' s_broadcast setting s_value[1/True] = True
    -- this environment offers nothing more elucidating than checking handling of corrupt party.

    () <- readChan pump
    writeChan outp =<< readIORef transcript

testCruptCompare :: IO Bool
testCruptCompare = runITMinIO 120 $ do
    liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
    t1 <- execUC
            testEnvSimCrupt
            (runAsyncP protABA)
            (runAsyncF $ bangFAsync fMulticastAndCoinToken)
            dummyAdversaryToken
    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
    t2 <- execUC
            testEnvSimCrupt
            idealProtocolToken
            (runAsyncF $ fABA)
            simABA

    liftIO $ putStrLn "REAL WORLD"
    liftIO $ putStrLn (show t1)
    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "IDEAL WORLD"
    liftIO $ putStrLn (show t2)


    return (t1 == t2)
