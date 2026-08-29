{-# LANGUAGE StandaloneDeriving, DeriveGeneric, DeriveAnyClass, OverloadedStrings, ScopedTypeVariables #-}
module Main where

import qualified ClientAutomaton
import qualified Network.Socket as S
import qualified Network.Socket.ByteString as NSB
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.IntMap.Strict as IntMap

import Control.Concurrent (forkIO)
import Control.Concurrent.Chan (Chan, newChan, readChan, writeChan)
import Data.IORef (IORef, newIORef, readIORef)
import Control.Exception (catch, SomeException)

import GHC.Generics (Generic)
import Data.Aeson (ToJSON, FromJSON, encode, decode)

-- 1. JSON für das Netzwerk
deriving instance Generic ClientAutomaton.Exec_msg
deriving instance ToJSON ClientAutomaton.Exec_msg
deriving instance FromJSON ClientAutomaton.Exec_msg

-- 2. Show für das Logging
deriving instance Show ClientAutomaton.Exec_msg
deriving instance Show ClientAutomaton.Exec_action
deriving instance Show ClientAutomaton.Client_exec_state

-- Typ-Aliase für Symmetrie zum Server
type ProcessID = Integer
type ProcessMap = IntMap.IntMap S.Socket
type ActionChan = Chan ClientAutomaton.Exec_action
-- OutputChan transportiert jetzt das Routing-Tupel (An wen? Was?)
type OutputChan = Chan (ProcessID, ClientAutomaton.Exec_msg)

main :: IO ()
main = do
    putStrLn "Bitte Server-Port eingeben (z.B. 5000):"
    portStr <- getLine
    let port = read portStr :: Int
    let serverId = fromIntegral port :: ProcessID

    socket <- S.socket S.AF_INET S.Stream S.defaultProtocol
    S.connect socket (S.SockAddrInet (fromIntegral port) (S.tupleToHostAddress (127, 0, 0, 1)))
    putStrLn $ "[System] Verbunden mit Server (ProcessID: " ++ show serverId ++ ")."

    -- Hashmap initialisieren (enthält momentan nur den einen Server)
    serversRef <- newIORef (IntMap.singleton port socket)

    actionChan <- newChan
    outputChan <- newChan

    _ <- forkIO $ inputLoop actionChan
    -- Wir übergeben dem receiveLoop die serverId, damit er weiß, von wem die Nachricht kommt
    _ <- forkIO $ receiveLoop serverId socket actionChan
    _ <- forkIO $ outputLoop serversRef outputChan

    -- Initialisierung des Automaten mit der Server-ID
    automatonLoop actionChan outputChan (ClientAutomaton.initial_client serverId)


inputLoop :: ActionChan -> IO ()
inputLoop actionChan = do
    _ <- getLine
    writeChan actionChan ClientAutomaton.PingServer
    inputLoop actionChan


receiveLoop :: ProcessID -> S.Socket -> ActionChan -> IO ()
receiveLoop senderId socket actionChan = do
    bytes <- catch (NSB.recv socket 1024) 
                   (\(_ :: SomeException) -> return BS.empty)
                   
    if BS.null bytes
    then error "[System] Verbindung geschlossen"
    else do
        mapM_ processLine (BS.lines bytes)
        receiveLoop senderId socket actionChan
  where
    processLine line = 
        case decode (LBS.fromStrict line) of
            -- Hier nutzen wir nun die echte Sender-ID für die Automaten-Aktion
            Just msg -> writeChan actionChan (ClientAutomaton.Receive senderId msg)
            Nothing  -> putStrLn "[System] Fehlerhafte JSON-Nachricht ignoriert."


automatonLoop :: ActionChan -> OutputChan -> ClientAutomaton.Client_exec_state -> IO ()
automatonLoop actionChan outputChan state = do
    action <- readChan actionChan
    putStrLn $ "\n[Aktion]  Verarbeite: " ++ show action
    
    -- Der Automaten-Schritt liefert nun eine Liste von Tupeln (ProcessID, Exec_msg)
    let (newState, routes) = ClientAutomaton.client_exec_step state action
    putStrLn $ "[Zustand] Neuer State: " ++ show newState
    
    -- routes ist bereits [(ProcessID, Exec_msg)], was perfekt zu unserem OutputChan passt
    mapM_ (writeChan outputChan) routes
    
    automatonLoop actionChan outputChan newState


outputLoop :: IORef ProcessMap -> OutputChan -> IO ()
outputLoop serversRef outputChan = do
    (targetId, message) <- readChan outputChan
    servers <- readIORef serversRef
    
    case IntMap.lookup (fromIntegral targetId) servers of
        Nothing -> 
            putStrLn $ "[Senden]  FEHLER: Prozess " ++ show targetId ++ " nicht gefunden."
        Just socket -> do
            putStrLn $ "[Senden]  An Prozess " ++ show targetId ++ " -> " ++ show message
            let payload = LBS.toStrict (encode message) <> "\n"
            catch (NSB.sendAll socket payload) 
                  (\(_ :: SomeException) -> putStrLn $ "[Senden]  Sende-Fehler an Prozess " ++ show targetId)
            
    outputLoop serversRef outputChan