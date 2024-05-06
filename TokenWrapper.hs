{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds
  #-}


module TokenWrapper where

import ProcessIO
import StaticCorruptions
import Multisession
import Async

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map, (!))
import qualified Data.Map.Strict as Map


data CarryTokens a = SendTokens a deriving (Show, Eq)
data TransferTokens a = DeliverTokensWithMessage a deriving (Show, Eq)


type MonadAdversaryToken m = (MonadAdversary m,
                              -- ?sendToken :: m () -> m (),
                              ?getToken :: m Int)

-- sendToken :: MonadAdversaryToken m => m () -> m ()
-- sendToken = ?sendToken

getToken :: MonadAdversaryToken m => m Int
getToken = ?getToken


-- TODO: should p2z have tokens too for dummy parties that forward tokens???
--type TokenEnvironment p2z z2p a2z z2a f2z z2f outz m = MonadEnvironment m => Chan SttCrupt_SidCrupt -> (Chan (PID, p2z), Chan ((PID, z2p), CarryTokens Int)) -> (Chan (a2z, CarryTokens Int), Chan (z2a, CarryTokens Int)) -> (Chan f2z, Chan z2f) -> Chan () -> Chan outz -> m ()
type TokenEnvironment p2z z2p a2z z2a f2z z2f outz m = MonadEnvironment m => Chan SttCrupt_SidCrupt -> (Chan (PID, p2z), Chan (PID, (z2p, CarryTokens Int))) -> (Chan (a2z, CarryTokens Int), Chan (z2a, CarryTokens Int)) -> (Chan f2z, Chan z2f) -> Chan () -> Chan outz -> m ()

--type TokenAsyncEnvironment p2z z2p a2z z2a f2z z2f outz m = TokenEnvironment p2z (ClockP2F z2p) 

-- TODO adversary not charge ANYTHING?????
--type TokenFunctionality p2f f2p a2f f2a z2f f2z m = MonadFunctionality m => (Chan ((PID, p2f), CarryTokens Int), Chan ((PID, f2p), CarryTokens Int)) -> (Chan a2f, Chan f2a) -> (Chan z2f, f2z) -> m ()
type TokenFunctionality p2f f2p a2f f2a z2f f2z m = MonadFunctionality m => (Chan (PID, (p2f, CarryTokens Int)), Chan (PID, (f2p, CarryTokens Int))) -> (Chan a2f, Chan f2a) -> (Chan z2f, Chan f2z) -> m ()


runTokenA :: MonadAdversary m =>
          (MonadAdversaryToken m => Adversary ((SttCruptZ2A z2a (Either (ClockA2F) (SID, (z2a2f, TransferTokens Int)))),
                                                CarryTokens Int)
                                              a2z p2a (ClockP2F (a2p, CarryTokens Int)) f2a (Either ClockA2F a2f) m)
          -> Adversary ((SttCruptZ2A z2a (Either (ClockA2F) (SID, (z2a2f, TransferTokens Int)))),
                       CarryTokens Int)
                       a2z p2a (ClockP2F (a2p, CarryTokens Int)) f2a (Either ClockA2F a2f) m
runTokenA a (z2a, a2z) (p2a, a2p) (f2a, a2f) = do

  tokens <- newIORef 0

  z2a' <- newChan
  a2f' <- newChan
  a2p' <- newChan

  fork $ forever $ do
    (mf, SendTokens a) <- readChan z2a
    if a>=0 then do
      tk <- readIORef tokens
      writeIORef tokens (tk+a)
    else
      error "sending negative tokens"
    case mf of
      (SttCruptZ2A_A2F (Right (_, (_, DeliverTokensWithMessage b)))) -> do
        if b>=0 then do
          tk <- readIORef tokens
          writeIORef tokens (tk+b)
          printAdv $ "simulator acquired " ++ (show b) ++ " tokens from corrupt party"
        else
          error "sending negative tokens"
      _ -> return()
    writeChan z2a' (mf, SendTokens a)

  fork $ forever $ do
    mf <- readChan a2f'
    case mf of
      Left (ClockA2F_Deliver _) -> do
        tk <- readIORef tokens
        if (tk-1) < 0 then
          error "not enough tokens"
        else
          writeIORef tokens (tk-1)
      Left (ClockA2F_Delay rounds) -> do
        if rounds > 0 then do
          tk <- readIORef tokens
          if (tk-rounds) < 0 then
            error "not enough tokens"
          else
            writeIORef tokens (tk-rounds)
        else
          return()
      _ -> return()
    writeChan a2f mf

  fork $ forever $ do
    mf <- readChan a2p'
    case mf of
      (_, (ClockP2F_Through (_, SendTokens k))) -> do
        if k >= 0 then do
          tk <- readIORef tokens
          if (tk-k) < 0 then
            error "not enough tokens"
          else
            writeIORef tokens (tk-k)
        else
          error "sending negative tokens"
        liftIO $ putStrLn $ "simulator sends " ++ (show k) ++ " tokens to ideal functionality"
      _ -> return()
    writeChan a2p mf

  let _getToken = do
        tk <- readIORef tokens
        return tk

  let ?getToken = _getToken in
    a (z2a', a2z) (p2a, a2p') (f2a, a2f')
  return ()

dummyAdversaryToken :: MonadAdversary m => Adversary ((SttCruptZ2A b d), CarryTokens Int)
                                                     --(SttCruptA2Z a (Either (ClockF2A (SID, (c, CarryTokens Int))) f2a))
                                                     (SttCruptA2Z a (Either (ClockF2A (SID, (c, CarryTokens Int))) f2a))
                                                     a b (Either (ClockF2A (SID, (c, CarryTokens Int))) f2a) d m
dummyAdversaryToken (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= \mf ->
      case mf of
        ((SttCruptZ2A_A2F b), SendTokens _)        -> writeChan a2f b
        ((SttCruptZ2A_A2P (pid, m)), SendTokens _) -> writeChan a2p (pid, m)
  fork $ forever $ readChan f2a >>= writeChan a2z . SttCruptA2Z_F2A
  fork $ forever $ readChan p2a >>= writeChan a2z . SttCruptA2Z_P2A
  return ()

idealProtocolToken :: MonadProtocol m => Protocol (ClockP2F a, CarryTokens Int) b b (ClockP2F (a, CarryTokens Int)) m
idealProtocolToken (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    mf <- readChan z2p
    --liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    case mf of
      (ClockP2F_Pass, SendTokens _)       -> writeChan p2f ClockP2F_Pass
      (ClockP2F_Through m, SendTokens tk) -> writeChan p2f (ClockP2F_Through (m, SendTokens tk))
  fork $ forever $ do
    m <- readChan f2p
    --liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  return ()


--partyWrapperTokens :: MonatITM m => SID -> Crupt -> Chan () -> (Chan ((PID, z2p), CarryTokens Int), Chan (PID, p2z)) -> (Chan ((PID, f2p), CarryTokens Int), Chan ((PID, p2f), CarryTokens Int)) -> (Chan (PID, p2f)V


--_bangFAsyncInstanceToken :: MonadFunctionalityAsync m => Chan ((SID, l), CarryTokens Int) -> Chan (Chan (), Chan ()) -> (forall m. MonadFunctionalityAsync m (l, CarryTokens Int) => Functionality p2f f2p a2f f2a Void Void m) ->  Functionality p2f f2p a2f f2a Void Void m
--_bangFAsyncInstanceToken _leak _eventually f = f
--  where
--    ?leak = \(l, t) -> writeChan _leak ((?sid, l), t)
--    ?eventually = \m -> do
--      cb :: Chan () <- newChan
--      ok :: Chan () <- newChan
--      writeChan _eventually (cb, ok)
--      fork $ readChan cb >> m
--      readChan ok
--
--
--bangFAsyncToken
--    :: MonadFunctionalityAsync m ((SID, l), CarryTokens Int) =>
--  :: MonadFunctionalityAsync m (SID, l) 
--       (forall m'. MonadFunctionalityAsync m' l => Functionality p2f f2p a2f f2a Void Void m') -> 
--       Functionality ((SID, p2f), CarryTokens Int) ((SID, f2p), CarryTokens Int) ((SID, a2f), CarryTokens Int) (SID, f2a) Void Void m 
--bangFAsyncToken f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
--    _leak <- newChan
--    _eventually <- newChan
--
--    fork $ forever $ do
--        (cb,ok) <- readChan _eventually
--        ?eventually $ do
--            writeChan cb ()
--        writeChan ok ()
--
--    fork $ forever $ do
--        l <- readChan _leak
--        leak l
--
--    bangFToken (_bangFAsyncInstanceToken _leak _eventually f) (p2f, f2p) (a2f, f2a) (z2f, f2z)
--
--bangFToken
--  :: MonadFunctionality m =>
--     (forall m'. MonadFunctionality m' => Functionality p2f f2p a2f f2a Void Void m') ->
--     Functionality ((SID, p2f), CarryTokens Int) ((SID, f2p), CarryTokens Int) 
--     ((SID, a2f), CarryTokens Int) (SID, f2a) Void Void m
--bangFToken f (p2f, f2p) (a2f, f2a) _ = do
--  -- Store a table that maps each SSID to a channel (f2p,a2p) used
--  -- to communicate with each subinstance of !f
--  p2ssid <- newIORef empty
--  a2ssid <- newIORef empty
--
--  tokens <- newIORef 0
--
--  let newSsid ssid = do
--        liftIO $ putStrLn $ "[" ++ show ?sid ++ "] Creating new subinstance with ssid: " ++ show ssid
--        --let newSsid' _2ssid f2_ tag = do
--        --      ff2_ <- newChan;
--        --      _2ff <- newChan;
--        --      fork $ forever $ do
--        --      -- m := (pid, m')
--        --        ((pid, m), SendTokens x) <- readChan ff2_
--        --        --liftIO $ putStrLn $ "!F wrapper f->_ received " ++ tag -- ++ " " ++ show m
--        --      -- writing ((ssid, (pid, m')), SendTokens x)
--        --        writeChan f2_ ((ssid, (pid, m)), SendTokens x)
--        --      modifyIORef _2ssid $ insert ssid _2ff
--        --      return (_2ff, ff2_)
--        f2p' <- wrapWrite (\(_, ((pid, m), tokens)) -> (pid, ((ssid, m), tokens))) f2p
--        ff2p :: Chan ((PID, f2p), CarryTokens Int)  <- newChan ;
--        p2ff :: Chan (PID, (p2f, CarryTokens Int))  <- newChan;
--        fork $ forever $ do
--            --((pidR, m), t) <- readChan ff2p
--            (m, t) <- readChan ff2p
--            --writeChan f2p' ((ssid, (pidR, m)), t)
--            --writeChan f2p' ((ssid, m), t)
--            writeChan f2p' (ssid, (m, t))
--        modifyIORef p2ssid $ insert ssid p2ff
--        --p <- newSsid' p2ssid f2p' "f2p"
--        let p = (p2ff, ff2p)
--        
--        ff2a :: Chan (f2a, CarryTokens Int) <- newChan;
--        a2ff :: Chan (a2f, CarryTokens Int) <- newChan;
--        fork $ forever $ do
--            m <- readChan ff2a
--            writeChan f2a (ssid, m)
--        modifyIORef a2ssid $ insert ssid a2ff
--        let a = (a2ff, ff2a)
--
--        --a <- newSsid' a2ssid f2a  "f2a"
--        fork $ let ?sid = (extendSID ?sid (fst ssid) (snd ssid)) in do
--          liftIO $ putStrLn $ "in forked instance: " ++ show ?sid
--          f p a (undefined, undefined)
--        return ()
--
--  let getSsid _2ssid ssid = do
--        b <- return . member ssid =<< readIORef _2ssid
--        if not b then newSsid ssid else return ()
--        readIORef _2ssid >>= return . (! ssid)
--
--  -- Route messages from parties to functionality
--  fork $ forever $ do
--    (pid, ((ssid, m), tks)) <- readChan p2f
--    if tks == 0 then error "multisession needs 1 token at least"
--    else do
--      tk <- readIORef tokens
--      writeIORef tokens (tk+1)
--      --liftIO $ putStrLn $ "!F wrapper p->f received " ++ show ssid
--      --getSsid p2ssid ssid >>= flip writeChan (pid, m)
--      getSsid p2ssid ssid >>= flip writeChan (pid, (m,tks-1))
--      
--
--  -- Route messages from adversary to functionality
--  fork $ forever $ do
--    ((ssid, m), tokens) <- readChan a2f
--    --liftIO $ putStrLn $ "!F wrapper a->f received " ++ show ssid
--    getSsid a2ssid ssid >>= flip writeChan (m, tokens)
--
--  return ()
 

