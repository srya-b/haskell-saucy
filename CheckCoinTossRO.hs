 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

module CheckCoinTossRO where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import CoinTossRO
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

--data CoinCmd a = CoinCmd_start PID | CoinCmd_flipcommit PID Int | CoinCmd_flipopen PId Int Bool | CoinCmd_flipbit PID Bool | CoinCmd_ro PID a deriving (Show, Eq, Read)
data CoinCmd a b = CoinCmd_start PID | CoinCmd_m PID a | CoinCmd_ro PID b deriving (Show, Eq, Read)
type CoinInput a b = CoinCmd a b
type CoinConfig = (SID, PID, PID, CruptList)

testEnvCoinCrupt :: (MonadEnvironment m) => PID -> PID -> Maybe PID ->
  Environment (CoinFlipF2P ProtFlip_Msg) (ClockP2F (CoinFlipP2F ProtFlip_Msg))
              (SttCruptA2Z (RoF2P ProtFlip_Msg) 
                           (Either (ClockF2A (PID, ProtFlip_Msg)) Void))
              (SttCruptZ2A (ClockP2F (RoP2F (Int, Bool) ProtFlip_Msg))
                           (Either ClockA2F Void))
              Void ClockZ2F CoinFlipTranscript m --(CoinConfig, [Either (CoinInput ProtFlip_Msg (Int, Bool)) AsyncInput], CoinFlipTranscript) m
testEnvCoinCrupt sender receiver crupt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidCoin", show(sender, receiver, ""))
  finalFlip <- newIORef False
  cmdList <- newIORef []
  case crupt of
    Just c -> do
      writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(c,())])
      (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
      () <- readChan pump 
      case () of
        _ | c == sender -> do
              -- start receiver
              writeChan z2p (receiver, ClockP2F_Through FlipP2F_start)
              () <- readChan pump
              modifyIORef cmdList (++ [Left $ CoinCmd_start receiver])

              -- create a commitment 
              b <- ?getBit
              nonce :: Int <- getNbits 120
              writeChan z2a $ (SttCruptZ2A_A2P (sender, ClockP2F_Through $ RoP2F_Ro (nonce, b)))
              () <- readChan pump
              modifyIORef cmdList (++ [Left $ CoinCmd_ro sender (nonce, b)])

              mh <- readIORef lastOut
              let Just (Left (SttCruptA2Z_P2A ("Alice", RoF2P_Ro h))) = mh

              writeChan z2a $ (SttCruptZ2A_A2P (sender, ClockP2F_Through $ RoP2F_m (ProtFlip_commit h)))
              () <- readChan pump
              modifyIORef cmdList (++ [Left $ CoinCmd_m sender (ProtFlip_commit h)])

              ---- deliver Alice's commitment
              writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
              () <- readChan pump
              modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

              -- deliver Bob's bit
              writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
              () <- readChan pump
              modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

              mb <- readIORef lastOut
              liftIO $ putStrLn $ "mb: " ++ show mb
              let Just (Left (SttCruptA2Z_P2A (sender, RoF2P_m (ProtFlip_bit b')))) = mb
              let resultFlip = (b && not b') || (not b && b')
              liftIO $ putStrLn $ "\nZ: resultflip: " ++ show resultFlip
              if resultFlip == True then do
                modifyIORef cmdList (++ [Left $ CoinCmd_m sender ProtFlip_abort]) 
                writeChan z2a $ SttCruptZ2A_A2P (sender, ClockP2F_Through $ RoP2F_m (ProtFlip_abort))
              else do
                modifyIORef cmdList (++ [Left $ CoinCmd_m sender (ProtFlip_open nonce b)])
                writeChan z2a $ SttCruptZ2A_A2P (sender, ClockP2F_Through $ RoP2F_m (ProtFlip_open nonce b))
              () <- readChan pump
          
              -- deliver this message
              liftIO $ putStrLn $ "\nZ: deliver the final message"
              writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
              () <- readChan pump
              modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

              l <- readIORef lastOut
              let Just (Right (receiver, FlipF2P_coin flip)) = l

              cl <- readIORef cmdList
              tr <- readIORef transcript
              --writeChan outp ((sid, sender, receiver, (Map.fromList [(c,())])), cl, tr)
              writeChan outp tr
        _ | c == receiver -> do
              writeChan z2p (sender, ClockP2F_Through FlipP2F_start)
              () <- readChan pump
              modifyIORef cmdList (++ [Left $ CoinCmd_start sender])

              -- deliver Alice's commitment
              writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
              () <- readChan pump
              modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])
              
              -- send Alice the same bit all the time
              writeChan z2a $ SttCruptZ2A_A2P (receiver, ClockP2F_Through $ RoP2F_m $ ProtFlip_bit True)
              () <- readChan pump
              modifyIORef cmdList (++ [Left $ CoinCmd_m receiver $ ProtFlip_bit True]) 

              -- deliver Bob's bit
              writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
              () <- readChan pump
              modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

              cl <- readIORef cmdList
              tr <- readIORef transcript
              --writeChan outp ((sid, sender, receiver, (Map.fromList [(c,())])), cl, tr)
              writeChan outp tr
    Nothing -> do
      writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
      (lastOut, transcript, clockChan, leakLimited) <- envReadOut p2z a2z
      () <- readChan pump 

      writeChan z2p (sender, ClockP2F_Through FlipP2F_start)
      () <- readChan pump
      modifyIORef cmdList (++ [Left $ CoinCmd_start sender])

      writeChan z2p (receiver, ClockP2F_Through FlipP2F_start)
      () <- readChan pump
      modifyIORef cmdList (++ [Left $ CoinCmd_start receiver])

      -- deliver Alice's commitment
      writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
      () <- readChan pump
      modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

      writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
      () <- readChan pump
      modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

      writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
      () <- readChan pump
      modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

      writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks
      () <- readChan pump
      modifyIORef cmdList (++ [Right $ (CmdDeliver 0, 0)])

      cl <- readIORef cmdList
      tr <- readIORef transcript
      --writeChan outp ((sid, sender, receiver, Map.empty), cl, tr)
      writeChan outp tr

firstFlip [] = error "no output found"
firstFlip (t:tr) = case t of
                     Right (pid, FlipF2P_coin b) -> b
                     _ -> firstFlip tr

prop_distribution = monadicIO $ do
  let prot () = protCoinFlipROUnfair
  let sender = "Alice" 
  let receiver = "Bob"

  mode <- generateM $ chooseInt (1,3)
  let crupt = case mode of
            1 -> Just sender
            2 -> Just receiver
            3 -> Nothing
  
  treal <- run $ runITMinIO 120 $ execUC
    (testEnvCoinCrupt sender receiver crupt)
    (runAsyncP $ protCoinFlipROUnfair)
    (runAsyncF $ fTwoWayAndRO)
    dummyAdversary

  tideal <- run $ runITMinIO 120 $ execUC 
    (testEnvCoinCrupt sender receiver crupt)
    idealProtocol
    (runAsyncF fCoinFlipUnfair)
    simFlip
   
  let freal = firstFlip treal 
  let fideal = firstFlip tideal

  monitor (collect ("real", freal))
  monitor (collect ("ideal", fideal)) 
