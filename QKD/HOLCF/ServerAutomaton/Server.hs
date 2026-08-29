{-# LANGUAGE StandaloneDeriving, DeriveGeneric, DeriveAnyClass, OverloadedStrings, ScopedTypeVariables #-}
module Main where

import qualified ServerAutomaton
import qualified Network.Socket as S
import qualified Network.Socket.ByteString as NSB
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.IntMap.Strict as IntMap

import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.Chan (Chan, newChan, readChan, writeChan)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Control.Exception (catch, SomeException)
import Control.Monad (forM_)

import GHC.Generics (Generic)
import Data.Aeson (ToJSON, FromJSON, encode, decode)

deriving instance Generic ServerAutomaton.Exec_msg
deriving instance ToJSON ServerAutomaton.Exec_msg
deriving instance FromJSON ServerAutomaton.Exec_msg

deriving instance Show ServerAutomaton.Exec_msg
deriving instance Show ServerAutomaton.Exec_action
deriving instance Show ServerAutomaton.Server_exec_state

-- Typ-Aliase für bessere Lesbarkeit
type ClientID = Integer
type ClientMap = IntMap.IntMap S.Socket
type ActionChan = Chan ServerAutomaton.Exec_action
-- OutputChan überträgt jetzt ein Tupel: An wen? Was?
type OutputChan = Chan (ClientID, ServerAutomaton.Exec_msg) 

main :: IO ()
main = do
    serverSocket <- S.socket S.AF_INET S.Stream S.defaultProtocol
    S.setSocketOption serverSocket S.ReuseAddr 1
    S.bind serverSocket (S.SockAddrInet 5000 0)
    S.listen serverSocket 5 -- Erlaube Warteschlange für mehrere Clients

    clientsRef <- newIORef IntMap.empty
    nextIdRef <- newIORef 1
    
    actionChan <- newChan
    outputChan <- newChan

    putStrLn "[System] Multi-Client Server startet auf Port 5000."

    _ <- forkIO $ acceptLoop serverSocket clientsRef nextIdRef actionChan
    _ <- forkIO $ timerLoop actionChan
    _ <- forkIO $ inputLoop actionChan
    _ <- forkIO $ outputLoop clientsRef outputChan

    automatonLoop actionChan outputChan ServerAutomaton.initial_server


-- ============================================================
-- Verbindung & Routing
-- ============================================================

acceptLoop :: S.Socket -> IORef ClientMap -> IORef ClientID -> ActionChan -> IO ()
acceptLoop serverSocket clientsRef nextIdRef actionChan = do
    (connection, addr) <- S.accept serverSocket
    
    -- Neue fortlaufende ID generieren
    cId <- atomicModifyIORef' nextIdRef (\n -> (n + 1, n))
    
    putStrLn $ "[System] Client " ++ show cId ++ " verbunden von " ++ show addr
    
    -- Socket im Adressbuch speichern (Umwandlung Integer -> Int für die Map)
    atomicModifyIORef' clientsRef (\m -> (IntMap.insert (fromIntegral cId) connection m, ()))

    -- Optional, falls du den `ClientJoined` Schritt in Isabelle einbaust:
    writeChan actionChan (ServerAutomaton.ClientJoined cId)

    -- Empfangsthread nur für diesen EINEN Client starten
    _ <- forkIO $ receiveLoop cId connection actionChan
    
    acceptLoop serverSocket clientsRef nextIdRef actionChan


receiveLoop :: ClientID -> S.Socket -> ActionChan -> IO ()
receiveLoop cId socket actionChan = do
    bytes <- catch (NSB.recv socket 1024) 
                   (\(_ :: SomeException) -> return BS.empty)
                   
    if BS.null bytes
    then putStrLn $ "[System] Verbindung zu Client " ++ show cId ++ " getrennt."
         -- Hier könntest du noch eine Disconnect-Action in den Automaten werfen 
         -- und den Client aus der clientsRef-Map löschen!
    else do
        mapM_ processLine (BS.lines bytes)
        receiveLoop cId socket actionChan
  where
    processLine line = 
        case decode (LBS.fromStrict line) of
            Just msg -> 
                -- Hier ist der Clou: Wir paaren die empfangene Nachricht
                -- mit der cId des Sockets!
                writeChan actionChan (ServerAutomaton.Receive cId msg)
            Nothing  -> 
                putStrLn $ "[System] Fehlerhaftes JSON von Client " ++ show cId


-- ============================================================
-- Loops & Automat
-- ============================================================
-- (timerLoop und inputLoop bleiben absolut identisch zu vorher)
timerLoop :: ActionChan -> IO ()
timerLoop actionChan = threadDelay 2000000 >> writeChan actionChan ServerAutomaton.UpdateCounter >> timerLoop actionChan

inputLoop :: ActionChan -> IO ()
inputLoop actionChan = getLine >> writeChan actionChan ServerAutomaton.UpdateCounter >> inputLoop actionChan


automatonLoop :: ActionChan -> OutputChan -> ServerAutomaton.Server_exec_state -> IO ()
automatonLoop actionChan outputChan state = do
    action <- readChan actionChan
    putStrLn $ "\n[Aktion]  Verarbeite: " ++ show action
    
    let (newState, routes) = ServerAutomaton.server_exec_step state action
    putStrLn $ "[Zustand] Neuer State: " ++ show newState
    
    -- routes ist jetzt vom Typ [(Integer, Exec_msg)]
    mapM_ (writeChan outputChan) routes
    
    automatonLoop actionChan outputChan newState


-- ============================================================
-- Gezieltes Senden (Routing)
-- ============================================================

outputLoop :: IORef ClientMap -> OutputChan -> IO ()
outputLoop clientsRef outputChan = do
    (targetId, message) <- readChan outputChan
    clients <- readIORef clientsRef
    
    case IntMap.lookup (fromIntegral targetId) clients of
        Nothing -> 
            putStrLn $ "[Senden]  FEHLER: Client " ++ show targetId ++ " nicht gefunden."
        Just socket -> do
            putStrLn $ "[Senden]  An Client " ++ show targetId ++ " -> " ++ show message
            let payload = LBS.toStrict (encode message) <> "\n"
            catch (NSB.sendAll socket payload) 
                  (\(_ :: SomeException) -> putStrLn $ "[Senden]  Sende-Fehler bei Client " ++ show targetId)
            
    outputLoop clientsRef outputChan