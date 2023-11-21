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

module BrokenABA where

import ProcessIO
import StaticCorruptions
import Async
import Multicast (forMseq_)
import Multisession
import TokenWrapper
import SCCMulticast

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

data CastP2F a = CastP2F_cast a | CastP2F_ro Int deriving Show
data CastF2P a = CastF2P_OK | CastF2P_Deliver a | CastF2P_ro Bool deriving (Show, Eq)
data CastF2A a = CastF2A a | CastF2A_ro Bool deriving (Show, Eq)
data CastA2F a = CastA2F_Deliver PID a deriving Show

data ABACast = AUX Int Bool | EST Int Bool deriving (Show, Eq)

{-
    Total token cost: 2N+2
        2 broadcasts
-}
data SBcastVariant = SBcastSmall | SBcastLarge | SBcastCorrect deriving (Show, Eq)
data SBSVariant = SBSSmall | SBSLarge | SBSCorrect deriving (Show, Eq)


sBroadcastBreak :: (MonadIO m, MonadITM m) => SBcastVariant -> SBSVariant -> Bool ->
    IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
    Chan () -> Chan () -> IORef Bool -> Bool -> m () -> m ThreadId
sBroadcastBreak castVariant valVariant checkRound tokens tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
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
  (sBroadcastBroken castThreshold svalThreshold checkRound tokens tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass)

sBroadcast :: (MonadIO m, MonadITM m) =>
    IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
    Chan () -> Chan () -> IORef Bool -> Bool -> m () -> m ThreadId
sBroadcast = sBroadcastBreak SBcastCorrect SBSCorrect True

sBroadcastBroken :: (MonadIO m, MonadITM m) => Int -> Int -> Bool ->
    IORef Int -> Int -> PID -> [PID] -> Int -> Bool -> 
    Chan (PID, (CoinCastF2P ABACast)) -> Chan (SID, (CoinCastP2F ABACast, CarryTokens Int)) -> 
    Chan () -> Chan () -> IORef Bool -> Bool -> m () -> m ThreadId
sBroadcastBroken castThreshold svalThreshold checkRound tokens tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
    -- set the current bin_ptr[s_i] = False because main protocol will wait till one of them is True
    vCount <- newIORef 0
    receivedESTFrom <- newIORef $ (Map.empty :: Map PID ())
    let print s = do
                    liftIO $ putStrLn $ "[ SBCast " ++ show pid ++ ", " ++ show round ++ ", " ++ show bit ++ "] " ++ show s

    -- the SSID for the sub-session of fMulticats this instance of sBroadcast will use      
    let sidmycast :: SID = (show ("sbcast", pid, round, bit), show (pid, parties, ""))
    --liftIO $ putStrLn $ "\t\t\t\t[" ++ show pid ++ "] sbcast (" ++ show bit ++ ", " ++ show shouldBCast ++ ")"
    print ("should_bcast: " ++ show shouldBCast)

    let multicast (x, DeliverTokensWithMessage st) = do
              tk <- readIORef tokens
              let neededTokens = (length parties) * (st+1)
              writeIORef tokens (max 0 (tk-neededTokens))
              print (">>>>> Multicasting: ((" ++ show x ++ ", DeliverTokensWithmessage " ++ show st ++ "), SentTokens " ++ show (min tk neededTokens) ++ ")")
              
              writeChan p2f (sidmycast, (CoinCastP2F_cast (x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens)))
              readChan okChan
              print ("Waiting for OK for Multicast")

    if shouldBCast then do
        -- broadcast the proposed value
{- TOKENS: (N+1) N for users and 1 for ! -}
        multicast (EST round bit, DeliverTokensWithMessage 0)
    else
        return ()

    tid <- fork $ forever $ do
        -- assumed we're receiving from the correct session of fMulticast by the dispatcher
        -- in the main protocol body
        (from, m) <- readChan f2p

        case m of
            -- Receiving messages from other parties with TAG,S_VAL(v_i) where TAG is EST[r_i] where r_i is the round this sBroadcast is for
            CoinCastF2P_Deliver (EST r b) -> do
                -- Only consider messages received for the same `bit` and from other parties
                --r <- return round
                if (r == round) || (not checkRound) then do
                --if (r == round) then do
                  receivedFromPidS <- readIORef receivedESTFrom >>= return . (member from)

                  -- Only accept EST messages from new parties
                  if (b == bit) && (not receivedFromPidS) then do
                      -- bit should only be received on not broadcast
                      -- count how many we've received
                      modifyIORef vCount $ (+) 1
                      modifyIORef receivedESTFrom $ Map.insert from ()

                      v <- readIORef vCount
                      print ("vcount: " ++ show v)

                      if (v == castThreshold) then do
                          -- only broadcast EST round bit if we haven't before
                          if (not shouldBCast) then do
{- TOKENS: (N+1)   -}
                              multicast (EST round bit, DeliverTokensWithMessage 0)
                              pass
                          else do
                              --print ("shouldnt bcast")
                              pass
                      else if v == svalThreshold then do
                          -- if the second threshold is reached for this bit then set the svalue_i (i.e. the bin_ptr[bit]) to True
                          print ("svalue is True")
                          writeChan toMainChan ()  
                      else do 
                          --print ("not doing anything")
                          pass
                  else pass
                else pass
            _ -> error "Shouldn't be getting non EST messages"

    -- pass control back to the main protocol body
    return tid
        
--data ABABugs = ABABugs_Thresh ABAVariant SBcastVariant SBSVariant | ABABugs_BinPtrReset | ABABugs_OldRounds | ABABugs_AnyAUX

data ABAThreshold = ABASmall | ABALarge | ABACorrect deriving (Show, Eq) 
data ABARounds = ABARounds_Correct | ABARounds_Buggy deriving (Show, Eq)
data ABABinPtr = ABABinPtr_Reset | ABABinPtr_Persist deriving (Show, Eq)
data ABAAnyAux = ABAAnyAux_Any | ABAAnyAux_Correct   deriving (Show, Eq)
type ABABugs = (ABAThreshold, SBcastVariant, SBSVariant, ABARounds, ABABinPtr, ABAAnyAux)

data ABAF2P = ABAF2P_Out Bool | ABAF2P_Ok deriving (Show, Eq)

--protABABreak :: (MonadAsyncP m) => ABAThreshold -> SBcastVariant -> SBSVariant ->
--    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
--            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
--protABABreak abaVariant bcastVariant svalVariant (z2p, p2z) (f2p, p2f) = do
--  let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd ?sid 
--  let n = length parties
--
--  let thresh = case abaVariant of
--                ABASmall -> n-t-1
--                ABALarge -> n-t+1
--                ABACorrect -> n-t
--  (protABABroken thresh bcastVariant svalVariant (z2p, p2z) (f2p, p2f))
protABABreak :: (MonadAsyncP m) => ABABugs -> 
    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
protABABreak abaBugs (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd ?sid 
  let n = length parties

  let (abaVariant, sbcastVariant, sbsVariant, roundBug, binPtrBug, anyAuxBug) = abaBugs
  let thresh = case abaVariant of
                 ABASmall -> n-t-1
                 ABALarge -> n-t+1
                 ABACorrect -> n-t
  let checkRound = case roundBug of
                     ABARounds_Correct -> True
                     ABARounds_Buggy -> False
  let resetBinPtr = case binPtrBug of
                      ABABinPtr_Reset -> True
                      ABABinPtr_Persist -> False
  let acceptAnyAux = case anyAuxBug of
                       ABAAnyAux_Any -> True
                       ABAAnyAux_Correct -> False

  (protABABroken thresh sbcastVariant sbsVariant checkRound resetBinPtr acceptAnyAux (z2p, p2z) (f2p, p2f))

protABA :: (MonadAsyncP m) =>
    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
protABA (z2p, p2z) (f2p, p2f) = do
  (protABABreak (ABACorrect, SBcastCorrect, SBSCorrect, ABARounds_Correct, ABABinPtr_Persist, ABAAnyAux_Correct) (z2p, p2z) (f2p, p2f))

protABABroken :: (MonadAsyncP m) => Int -> SBcastVariant -> SBSVariant -> Bool -> Bool -> Bool ->
    Protocol ((ClockP2F Bool), CarryTokens Int) (ABAF2P, CarryTokens Int) 
            (SID, (CoinCastF2P ABACast, CarryTokens Int)) (SID, (CoinCastP2F ABACast, CarryTokens Int)) m
protABABroken thresh bcastVariant svalVariant checkRound resetBinPtr acceptAnyAux (z2p, p2z) (f2p, p2f) = do
    let xyz :: Int = thresh
    let sid = ?sid :: SID
    let pid = ?pid :: PID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd sid 
    let n = length parties

    let ro_sid r = (show ("sRO", r), show("-1", parties, "")) 
    let gprint s r = do
                    liftIO $ putStrLn $ "\ESC[32m [" ++ show pid ++ ", " ++ show r ++ "] " ++ show s ++ "\ESC[0m"
    let print s r = do
                    liftIO $ putStrLn $ "[" ++ show pid ++ ", " ++ show r ++ "] " ++ show s
    
    let mprint s r = do
                    liftIO $ putStrLn $ "\t\t[" ++ show pid ++ ", " ++ show r ++ "] " ++ show s

    let debug = False
    let dprint s r = do if debug then (print s r) else return ()

{- [TOKENS] -}
    tokens <- newIORef 0
    totSent <- newIORef 0
    receivedAUXFrom <- newIORef $ (Map.empty :: Map PID ())

    -- bin_ptrs hold the s_values for each bit, initially both False
    binPtrT <- newIORef False
    binPtrF <- newIORef False 
    auxT <- newIORef False
    auxF <- newIORef False

    -- Separate views that counts unique parties that have sent a TRUE aux message for each round
    viewRTrue <- newIORef (empty :: Map Int Int)
    viewRFalse <- newIORef (empty :: Map Int Int)
    view <- newIORef (empty :: Map Int Int)

    -- read message and route to either sBroadcast or to the main protocol
    -- EDIT: new channel
    sb2MainChan :: Chan () <- newChan 
    sb2MainChanT :: Chan () <- newChan
    sb2MainChanF :: Chan () <- newChan
    f2sbChanTReal :: Chan (PID, (CoinCastF2P ABACast)) <- newChan
    f2sbChanFReal :: Chan (PID, (CoinCastF2P ABACast)) <- newChan
    f2sbChanT <- newIORef f2sbChanTReal
    f2sbChanF <- newIORef f2sbChanFReal
    -- EDIT: don't need a different OK chan each time because Ok only happens on multicast
    --       old SBCast aren't multcasting anything because they aren't receiving any new messages 
    f2sbOKChan <- newChan

    tempTid <- fork $ return ()
    tempFid <- fork $ return ()
    sbTid <- newIORef tempTid
    sbFid <- newIORef tempFid
    
    viewReady <- newChan
    f2mainOK <- newChan

    outOfTokens <- newIORef False

    -- roundSValue used by the dispatcher to ignore future messages for a round once one of the s_values is already True
    -- TODO: this may be the wrong approach, with a channel that notfied of a True s_value you never have the case that both s_values are True because the channel makes in synchronous in that sense, maybe this is a conquence of UC that we need to discuss 
    f2p' <- newChan
    f2p'' <- newChan
    decided <- newIORef False
    decision <- newIORef False 

    -- Compute the ssid from the broadcast parameters
    -- Identify messages by sid, round, and bit of SBroadcast
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))

    -- get f2p input
    fork $ forever $ do
        (s, (m, SendTokens tks)) <- readChan f2p
        modifyIORef tokens $ (+) tks

        let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s

        case m of 
            CoinCastF2P_ro b ->
                writeChan f2p'' b
            _ -> do
                writeChan f2p' (s, m)

    nMinusTChan <- newChan
    binPtrRead <- newChan

    round <- newIORef 0
 
    messagesByPeers <- newIORef (Map.empty :: Map PID Bool)
 
    -- dispatcher from F to sBroadcast and main protocol body  
    -- and dispatcher between sBroadcast and main protocol body
    fork $ forever $ do
        oot <- readIORef outOfTokens
        (s, m) <- readChan f2p'
        isDecided <- readIORef decided
        -- EDIT keep going even if decided
        let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s
        let (sstring :: String, _pidS :: PID, _round :: Int, _bit :: Bool) = readNote "" $ fst s
        -- send to the right sBroadcast or the main protocol body based on ssid
        currRound <- readIORef round
        dprint ("getting something " ++ show m ++ " from " ++ show _pidS) currRound
        case m of 
            CoinCastF2P_Deliver (EST r b) -> do
                if b == True then do
                  f2TChan <- readIORef f2sbChanT
                  writeChan f2TChan (pidS, m)
                else do
                  f2FChan <- readIORef f2sbChanF
                  writeChan f2FChan (pidS, m)
            CoinCastF2P_Deliver (AUX r b) -> do
                receivedFromPidS <- readIORef receivedAUXFrom >>= return . (member pidS)
                if (not receivedFromPidS) then do
                  r' <- readIORef round
                  --r' <- return r
                  if r == r' || (not checkRound) then do
                  --if r==r' then do
                    modifyIORef view $ Map.insertWith (\_ old -> old+1) r 1
                    modifyIORef messagesByPeers $ Map.insert pidS b
                    numView <- readIORef view >>= return . (! r)
                    print ("num aux (" ++ show b ++ "): " ++ show numView ++ ", from " ++ show pidS) r
                    modifyIORef receivedAUXFrom $ Map.insert pidS ()
                  -- Determine whetherh view[r] is satisified for either of the bits

                    if b then writeIORef auxT True
                    else writeIORef auxF True
        
                    if (numView == thresh) then do
                      writeChan nMinusTChan ()
                    else ?pass
                  else do
                    ?pass

                else ?pass --return ()
            CoinCastF2P_OK -> do
                -- Deliver the OK message back from fMulticast when bcasting
                -- to either the sbcast or the main body
                if sstring == "sbcast" then writeChan f2sbOKChan ()
                else writeChan f2mainOK ()
            _ -> 
                writeChan viewReady ()

    {- There are two SBCasts at any time: one for T and one for F. Each have
       their own channel for notifying threshold received. We reset the binPtrs here.
       They have the same OK chan because it returns immediately, never
       asynchronously. Returns the ID of the SBCast thread. -} 
    let newSBCast r b shouldBroadcast = do
            newf2sbChan :: Chan (PID, (CoinCastF2P ABACast)) <- newChan
            if b then do
              dprint ("replacing T chan") r
              writeIORef f2sbChanT newf2sbChan
              writeIORef binPtrT False 
            else do
              dprint ("replacing F chan") r
              writeIORef f2sbChanF newf2sbChan
              writeIORef binPtrF False

            theChannelToGive <- if b then readIORef f2sbChanT else readIORef f2sbChanF
            sBroadcastBreak bcastVariant svalVariant checkRound tokens t pid parties r b theChannelToGive p2f f2sbOKChan (if b then sb2MainChanT else sb2MainChanF) (if b then binPtrT else binPtrF) shouldBroadcast ?pass
   
    -- Get a common coin from the random oracle 
    let commonCoinR r = do
        tk <- readIORef tokens
        if (tk >= 1) then do
          modifyIORef tokens $ (subtract 1)
          writeChan p2f (ro_sid r, (CoinCastP2F_ro r, SendTokens 1))
          b <- readChan f2p'' -- get OK back from fMulticast
          return (Just b)
        else return (Nothing)
    
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))
   
    -- Send a multicast for the Main thread and wait for OK 
    let multicast s (x, DeliverTokensWithMessage st) = do
              tk <- readIORef tokens
              let neededTokens = (length parties) * (st+1)
              writeIORef tokens (max 0 (tk-neededTokens))
              r <- readIORef round
              gprint (">>>>>>> MAIN Multicasting [" ++ show pid ++ "]: ((" ++ show x ++ ", DeliverTokensWithMessage " ++ show st ++ "), SendTokens " ++ show (min tk neededTokens) ++ ")") r
              modifyIORef totSent $ (+) (min tk neededTokens)  
              writeChan p2f (s, (CoinCastP2F_cast (x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens)))
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

    -- reacts to SBCast(T) 
    binPtrWaiting <- newChan
    fork $ forever $ do
      -- wait for SBCast to notify
      () <- readChan sb2MainChanT
      r <- readIORef round
      gprint ("got sb2MainChanT") r
      bpT <- readIORef binPtrT
      bpF <- readIORef binPtrF
      if bpT then error "binptr[T] = 1 but activated again"
      else if bpF then do
        -- ASSUME: is other binPtr is true, main thread isn't waiting
        writeIORef binPtrT True
        ?pass
      else do
        -- ASSUME: main thread waiting for channel write
        writeIORef binPtrT True
        writeChan binPtrWaiting True

    -- reacts to SBCast(F)
    -- see above for comments
    fork $ forever $ do
      () <- readChan sb2MainChanF 
      r <- readIORef round
      gprint ("got sb2MainChanF") r
      bpT <- readIORef binPtrT
      bpF <- readIORef binPtrF
      if bpF then error "binptr[F] = 1 but activated again"
      else if bpT then do
        mprint ("bpT already true, move on") r
        writeIORef binPtrF True
        ?pass
      else do
        writeIORef binPtrF True
        writeChan binPtrWaiting False

    nMinusTAux <- newIORef False
    -- reacts to AUX threshold
    fork $ forever $ do
      () <- readChan nMinusTChan
      bpT <- readIORef binPtrT
      bpF <- readIORef binPtrF
      if bpT || bpF then do
        -- ASSUME: some true => main thread waiting
        writeIORef nMinusTAux True
        writeChan viewReady ()
      else do -- ASSUME: received AUX before EST => main thread waiting on binPtr
        writeIORef nMinusTAux True
        ?pass

    modifyIORef tokens $ (+) tks
    case msg of
      ClockP2F_Pass -> error "shouldn't be passing anything"
      ClockP2F_Through v -> do
          r <- readIORef round
          tryBit <- newIORef (not v)
          s <- readIORef tryBit
          supportCoin <- newIORef False
          liftIO $ putStrLn $ "[" ++ show ?pid ++ "] input is " ++ show v
          newSBCast 1 s False 

          fork $ forever $ do
              if resetBinPtr then do
                writeIORef binPtrT False
                writeIORef binPtrF False
              else return () 
              writeIORef messagesByPeers (Map.empty)
              modifyIORef round $ (+) 1
              writeIORef receivedAUXFrom (Map.empty :: Map PID ())
              writeIORef auxT False
              writeIORef auxF False
              -- read what the current bit is from the last round
              -- and supportCoin
              s <- readIORef tryBit
              sc <- readIORef supportCoin
              r <- readIORef round

              -- isDecided is used ONLY to write output to Z
              isDecided <- readIORef decided

              mprint ("New round: " ++ show r) r
              mprint ("s_i: " ++ show s) r
              mprint ("supportCoin: " ++ show sc) r
              mprint ("SBCast (" ++ show (not s) ++ ", " ++ show (not sc) ++ ")") r
{- [Token]: triggerssibly two broacasts so 2n max? -}
              newSBCast r (not s) (not sc)
              -- wait for one of the processes to write to the main thread
              -- saying that they set binptr[b] = True
-- Here it makes sense to do the UC-required write operations 
-- namely, saying OK to Z
-- outputting the decision to Z
-- or ?passing if neither applies
              first <- readIORef firstIteration
              firstDec <- readIORef firstDecide
              
              b0 <- readIORef binPtrF
              b1 <- readIORef binPtrT
              mprint ("binptr[T]: " ++ show b1 ++ ", binptr[F]: " ++ show b0) r

              -- get which binPtr is set to True
              whichBinPtr <- if first then do
                -- ASSUME: if OKing to environment then neither binPtr is true
                writeChan p2z (ABAF2P_Ok, SendTokens 0)
                modifyIORef firstIteration $ not
                readChan binPtrWaiting        -- wait for activation
              else do
                -- if either set proceed without waiting
                if b0 then return False       
                else if b1 then return True
                else do   -- if neither, then pass and wait for nuff EST
                  ?pass
                  readChan binPtrWaiting  
                 
              -- ASSUME: only one should be true because

              -- set w for broadcast
              let w = if sc then s
                      else whichBinPtr
   
              let sidMain :: SID = (show ("maincast", pid, r, w), show (pid, parties, ""))
              multicast sidMain (AUX r w, DeliverTokensWithMessage 0)
              b0 <- readIORef binPtrF
              b1 <- readIORef binPtrT
              print ("B0: " ++ show b0 ++ ", B1: " ++ show b1) r
  
              if isDecided && firstDec then do
                gprint ("@@@@@@@@@@@Deciding") r
                dec <- readIORef decision
                modifyIORef firstDecide $ not
                writeChan p2z ((ABAF2P_Out dec), SendTokens 0)
                -- ASSUME at this point, ddn't wait for EST and bcast AUX
                --        so will definitely wait for viewReady channel because
                --        it can't have accepted any AUX messages for this round yet
                --        since it hasn't ceded control yet since it decided at the end
                --        of last round => it will wait for viewReady channel
                naux <- readIORef nMinusTAux
                if naux then do 
                  error "^^^^^^^^^^^^^^viewreturn immediate"
                else do
                  readChan viewReady
                  gprint "^^^^^^^^^^^^^^^^^^^^^view ready from chan" r 
              else do --return () -- ?pass  -- TODO: this is the issue
                naux <- readIORef nMinusTAux
                if naux then do 
                  gprint "^^^^^^^^^^^^^^viewreturn immediate" r
                  return ()
                else do
                  gprint "view ready from chan" r 
                  ?pass
                  readChan viewReady

              -- naux might have been satisfied while waiting above
              --       if reached here and true, we can move on to the coin
              --       otherwise wait for the process 
              --naux <- readIORef nMinusTAux
              --if naux then do 
              --  gprint "^^^^^^^^^^^^^^viewreturn immediate" r
              --  return ()
              --else do
              --  gprint "view ready from chan" r 
              --  ?pass
              --  readChan viewReady
              print "got viewReady" r
              writeIORef nMinusTAux False

              -- get strong common coin
              bres <- commonCoinR r
              case bres of
                Just b -> do
                  gprint ("Common coin: " ++ show b) r 

                  -- this coin flip becomes the next s_i
                  writeIORef tryBit b

                  ---- decide?
                  b0 <- readIORef binPtrF
                  b1 <- readIORef binPtrT
                  aT <- readIORef auxT
                  aF <- readIORef auxF
                  let trueReady = if acceptAnyAux then b1 else (aT && b1)
                  let falseReady = if acceptAnyAux then b0 else (aF && b0) 
                  --let trueReady = (aT && b1)
                  --let falseReady = (aF && b0)
                  -- we know something is done, now determine support_coin
                  -- important that we only consider binPtrs for which there 
                  -- is some AUX message (indicated by aT and aF)
                  print ("b0: " ++ show b0 ++ " b1: " ++ show b1) r
                  print ("aF: " ++ show aF ++ " aT: " ++ show aT) r
                  mfp <- readIORef messagesByPeers
                  gprint ("from peers: " ++ show mfp) r
                  writeIORef supportCoin =<< if falseReady && trueReady then return True
                                             else if falseReady && (b == False) then do
                                               -- decide False
                                               writeIORef decided True
                                               writeIORef decision b
                                               return True
                                            else if trueReady && (b == True) then do
                                               -- decide True
                                               writeIORef decided True
                                               writeIORef decision b
                                               return True
                                            else do
                                              dd <- readIORef decided
                                              return False
                                              -- ASSUME: a party that decided in r-1 never gets here

                  return ()
                Nothing -> error "can't call coin, no tokens"
    return () 

type ABATranscript = [Either
                        (SttCruptA2Z
                          (SID, (CoinCastF2P ABACast, CarryTokens Int))
                          (Either 
                            (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                            (SID, CoinCastF2A)))
                        (PID, (ABAF2P, CarryTokens Int))]

{- All parties are true. It only delivers messages for the first round so either:
    1. the coin flip = True and all decide 
    2. the coin flip = False and they all attempt True again
-}
testEnvABAHonestAllTrue 
    :: (MonadEnvironment m) =>
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
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
    (deliverer, deliverByPairs, getByPairs, getBySender, getByReceivers, getByFilter, getLeaks) <- envMapQueue z2a a2z clockChan lastOut pump valueFilter
   
    c <- envQueueSize z2a clockChan 1000 
    let gprint s = do liftIO $ putStrLn $ "\ESC[32m" ++ show s ++ "\ESC[0m"
    let gtprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[32m" ++ show s ++ "\ESC[0m"
    let yprint s = do liftIO $ putStrLn $ "\t\t\t\t\ESC[33m" ++ show s ++ "\ESC[0m"

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

    -- deliver (1, 1, T) to A,B,C
    c <- envQueueSize z2a clockChan 0
    estT <- getByFilter (1, 1, True)
    estToA <- getByReceivers [("Alice" :: PID)]
    estToB <- getByReceivers [("Bob" :: PID)]
    estToC <- getByReceivers [("Charlie" :: PID)]
    let estToABC = estToA ++ estToB ++ estToC
    estF <- getByFilter (1, 1, False)
    estToD <- getByReceivers ["Dave"]
    estToE <- getByReceivers ["Eve"]
    let estToDE = estToD ++ estToE
    let estTtoABC = intersect estToABC estT
    let estFtoDE = intersect estToDE estF
    gtprint ("Give A,B,C only EST(T), and D,E EST(F)")
    forMseq_ (deliverListAll (estTtoABC ++ estFtoDE)) $ \i -> deliverer [] i  
    yprint ("All should move bcasting AUX")

    let minimumIdx = (c - (length (estTtoABC ++ estFtoDE)))
    --gprint ("minimum index: " ++ show minimumIdx)

    let makeSBCastSid ps p r b = (show ("sbcast", p, r, b), show (p, ps, ""))
    let makeMainSid ps p r w = (show ("maincast", p, r, w), show (p, ps, ""))
    
    -- send 4 x AUX(T) to A
    auxT <- getByFilter (2, 1, True)
    auxToAAll <- getByReceivers ["Alice"]
    let auxToA = filter (\x -> x >= minimumIdx) (intersect auxToAAll auxT) 
    gtprint ("Send all AUX messages or A")
    forMseq_ (deliverListAll auxToA) $ \i -> deliverer [] i   
    gtprint ("Give AUX from crupt Bob to Alice")
    let franksid1 = makeMainSid parties "Frank" 1 True
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (franksid1, ((CoinCastA2F_Deliver "Alice" $ (AUX 1 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    () <- readChan pump
    yprint ("Alice should decide")

    -- give EST F to B,C to get binptr[F] = T
    --forMseq_ [1..2] $ \_ -> do
    estF <- getByFilter (1, 1, False)
    estToB <- getByReceivers [("Bob" :: PID)]
    estToC <- getByReceivers [("Charlie" :: PID)]
    let estFtoBC = intersect estF (estToB ++ estToC)
    gtprint "making bin_ptr[F] = true for B,C"
    forMseq_ (deliverListAll estFtoBC) $ \i -> deliverer [] i
    yprint ("B,C should return for binPtr[F]") 
    
    toB <- getByReceivers ["Bob"]
    toC <- getByReceivers ["Charlie"]
    let toBC = toB ++ toC
    auxs <- (getByFilter (2, 1,True)) >>= (\x -> getByFilter (2, 1, False) >>= \y -> return (x ++ y))
    let auxsToBC = intersect toBC auxs
    gtprint ("make B,C move forward")
    forMseq_ (deliverListAll auxsToBC) $ deliverer []
    yprint "D,E should have view{0,1} and return sc=true and move straight to bcast(AUX) in next round"
  
    -- give aux to deliver
    -- binptr for D,E is 0 and B,C have 0,1
    toD <- getByReceivers ["Dave"]
    toE <- getByReceivers ["Eve"]
    let toED = toD ++ toE
    auxs <- (getByFilter (2, 1,True)) >>= (\x -> getByFilter (2, 1, False) >>= \y -> return (x ++ y))
    let auxsToED = intersect toED auxs 
    gtprint "Give AUXs to D,E"
    forMseq_ (deliverListAll auxsToED) $ deliverer []
    yprint "D,E have view{0} so have sc=false if coin=true and they try F again next round so wait for EST messages"

    ----------- everyone at round 2 ----------------------

    toABC <- getByReceivers ["Alice", "Bob", "Charlie"]
    auxs <- ((getByFilter (2, 2,True)) >>= (\x -> getByFilter (2, 2,False) >>= \y -> return (x ++ y)))
    gtprint ("A,B,C all skip to AUX give then enough T/F")
    forMseq_ (deliverListAll (intersect toABC auxs)) $ deliverer []
    yprint ("each have num_aux=3")

    gtprint ("give crupt AUX to each so they move on")
    let fsid = (show ("maincast", "Frank", 2, True), show ("Frank", parties, ""))
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (fsid, ((CoinCastA2F_Deliver "Alice" $ (AUX 2 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    () <- readChan pump
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (fsid, ((CoinCastA2F_Deliver "Bob" $ (AUX 2 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0) 
    () <- readChan pump
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (fsid, ((CoinCastA2F_Deliver "Charlie" $ (AUX 2 True, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    () <- readChan pump
    yprint ("if coin=0 then supportCoin=False so they attempt s_i=0 next round")
     
    gtprint ("give crupt EST[F] to D,E so they move to bcast AUX(F)") 
    let fsid = (show ("sbcast", "Frank", 2, False), show ("Frank", parties, ""))
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (fsid, ((CoinCastA2F_Deliver "Dave" $ (EST 2 False, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    () <- readChan pump
    writeChan z2a $ ((SttCruptZ2A_A2F $ (Right $ (fsid, ((CoinCastA2F_Deliver "Eve" $ (EST 2 False, DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0)))), SendTokens 0)
    () <- readChan pump

    toDE <- getByReceivers ["Dave", "Eve"]
    ests <- getByFilter (1,2,False) 
    gtprint ("Give any EST(F) to D,E")
    forMseq_ (deliverListAll (intersect toDE ests)) $ deliverer []
    yprint ("They should move to bcast AUX(F) and wait")

    toDE <- getByReceivers ["Dave", "Eve"]
    auxs <- ((getByFilter (2,2,False)) >>= (\x -> getByFilter (2,2,True) >>= \y -> return (x ++ y)))
    gtprint ("Give D,E any AUX messages")
    forMseq_ (deliverListAll (intersect toDE auxs)) $ deliverer []
    yprint ("D,E, view={0}, if coin=0 => D,E, decide 0 => Decide different to ALICE")      

    tr <- readIORef transcript
    writeChan outp tr

testABAMinority = do
  --let prot () = protABABreak (ABASmall, SBcastSmall, SBSSmall, ABARounds_Correct, ABABinPtr_Persist, ABAAnyAux_Correct)
  let prot () = protABABreak (ABACorrect, SBcastCorrect, SBSCorrect, ABARounds_Correct, ABABinPtr_Persist, ABAAnyAux_Correct)
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
