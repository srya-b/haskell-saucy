 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
 PartialTypeSignatures
  #-} 

module SCCMulticast where

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
