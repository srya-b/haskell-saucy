 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
 PartialTypeSignatures
  #-} 

module SBCast where

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

import TestTools (envReadOut)

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

upAndGet :: IORef a -> (a -> a) -> io a
upAndGet ref update = do
  modifyIORef a update
  readIORef a

type SBSP2F = (Bool, Bool)
data SBSF2P = SBSF2P_Out Bool | SBSF2P_Ok deriving (Show, Eq)

protSBCast :: (MonadAsyncP m) =>
  Protocol ((ClockP2F SBSP2F), CarryTokens Int) (SBSF2P, CarryTokens Int)
           (SID, (MulticastF2P Bool, CarryTokens Int)) (SID, ((Bool, TransferTokens Int), CarryTokens Int))
protSBCast (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, bit :: Bool, sssid :: String) = readNote "protACast" $ snd ?sid
  let n = length parties

  tokens <- newIORef 0

  {- TESTING MODS -}
  f2p' <- newChan
  z2p' <- newChan
  failed <- newIORef False

  -- Require means print the error then pass
  let require cond msg = 
        if not cond then do
          liftIO $ putStrLn $ "ERROR ERROR ERROR: " ++ msg
          ?pass
          readChan =<< newChan -- block without returning
        else return ()
 
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

  (recvC, multicastC, cOK) <- manyMulticast ?pid parties (f2p', p2f) --(f2p, p2f)
  
  let multicast (x, DeliverTokensWithMessage st) = do
        tk <- readIORef tokens
        let neededTokens = (length parties) * (st+1)
        writeIORef tokens (max 0 (tk-neededTokens))
        writeChan multicastC ((x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens))
        readChan cOK
  let recv = readChan recvC -- :: m (ACastMsg t)

  vCount <- newIORef 0
  receivedFrom <- newIORef $ Map.empty :: Map PID () 
  let received p = do readIORef receivedFrom >>= return . (member p)
  let addrecv p = do modifyIORef receivedFrom $ Map.insert p ()

  mf <- readChan z2p
  case mf of 
    ClockP2F_Pass -> ?pass
    ClockF2P_Through (b, should_bcast) ->
      if should_bcast then multicast (b, DeliverTokensWithMessage 0)
      else return ()

      fork $ forever $ do
        (from, b) <- readChan f2p
        case b of
          True => if b == bit and (not $ received from) then do
                    v <- upAndGet vCount $ (+) 1
                    addrecv from
                    if (v == t+1) then do
                      if (not should_bcast) then do
                      
          
