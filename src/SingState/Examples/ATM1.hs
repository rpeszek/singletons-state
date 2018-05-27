
{-# LANGUAGE TemplateHaskell
      , KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
      , TypeInType 
      , TypeOperators 
      , TypeFamilies
      , StandaloneDeriving
      , UndecidableInstances 
      , ScopedTypeVariables
      , MultiParamTypeClasses
      -- , FlexibleContexts
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  SingState.Examples.ATM1
-- Copyright   :  (C) 2018 Robert Peszek
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Robert Peszek
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Example of ATM prototocol
-- To run evaluate 
-- > runSM atm 
-- in ghci
-----------------------------------------------------------------------------
module SingState.Examples.ATM1 where

import SingState.Control.StateMachine 
import Data.Kind (Type)
import Data.Singletons.TH
import Data.Promotion.TH
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Function
import SingState.Examples.Data.Vect
import SingState.Examples.Data.Nat
import Unsafe.Coerce -- needed in binding DSL to IO
import Control.Exception
import Data.Proxy
 
{- to keep everything singleton I need singleton Unit too-}
$(singletons [d|
 data ATMState = Ready | CardInserted | Session
 data PINCheck = CorrectPIN | IncorrectPIN
 data Unit = MkUnit

 |])
 
$(promote [d|
 checkPin :: PINCheck -> ATMState
 checkPin CorrectPIN = Session
 checkPin IncorrectPIN = CardInserted

 |])
 
{- simplified one char numeric pin -}
type PIN = Nat
 
readPIN :: IO (SomeSing PIN)
readPIN = readNat 
 
readNat :: IO (SomeSing Nat)
readNat = do x <- getLine
             let mxi = readMaybe x :: Maybe Integer 
             case mxi of
                Nothing -> do 
                  putStrLn $"Invalid entry " ++ show x ++ " try again"
                  readNat
                Just xi -> do
                  let xn = integerToNat xi
                  return $ withSomeSing xn SomeSing 
 
readMaybe :: Read a => String -> Maybe a
readMaybe s = case reads s of
                 [(val, "")] -> Just val
                 _           -> Nothing
 
testPIN = SS (SS SZ)
 
data HasCard (s :: ATMState) where
     HasCI      :: HasCard CardInserted
     HasSession :: HasCard Session

data ATMCmd (s :: ATMState) (f :: k ~> ATMState) (res :: k) where
     InsertCard :: ATMCmd 'Ready     (ConstSym1 'CardInserted)  'MkUnit
     {- Idris can use auto-implicit here -}
     EjectCard  :: HasCard state ->
                   ATMCmd  state     (ConstSym1 'Ready) 'MkUnit
     GetPIN     :: ATMCmd  'CardInserted (ConstSym1 'CardInserted) (p :: PIN)
     CheckPIN   :: forall (p :: PIN) (check :: PINCheck) . 
                   Sing p -> ATMCmd 'CardInserted CheckPinSym0 check    
     GetAmount  :: ATMCmd state (ConstSym1 state) (n :: Nat)
     Dispense   :: SNat n -> ATMCmd 'Session (ConstSym1 'Session)  'MkUnit
     Message    :: String -> ATMCmd state (ConstSym1 state)  'MkUnit
 
     -- TypePure   :: res -> ATMCmd state (ConstSym1 state) res
     Pure       :: forall (res :: k) (state_fn :: k ~> ATMState). 
                   Sing res -> ATMCmd (state_fn @@ res) state_fn res
     {- note this has to be cross-kind! -}
     Bind      :: forall (a :: k1) (b :: k2) (state1b :: ATMState) (state1e_fn :: k1 ~> ATMState) (state2e_fn :: k2 ~> ATMState).
                   ATMCmd state1b state1e_fn a ->
                   (Sing a -> ATMCmd (state1e_fn @@ a) state2e_fn b) ->
                   ATMCmd state1b state2e_fn b 


instance SmPure ATMCmd where
  smPure = Pure

instance SmBind IdSym0 ATMCmd ATMCmd where
   smBind _ = Bind 

insertEject :: ATMCmd Ready (ConstSym1 Ready) 'MkUnit
insertEject =  InsertCard >>> EjectCard HasCI 

atm :: ATMCmd Ready (ConstSym1 Ready) 'MkUnit
atm =  InsertCard >>> GetPIN >>>=
       (\ pin -> Message "Checking Card" >>>
                 CheckPIN pin) >>>=
       (\ pinOK -> case pinOK of
          SCorrectPIN -> GetAmount >>>= (\ cash -> 
              Dispense cash >>> 
              EjectCard HasSession >>> 
              Message "Please remove your card and cash"
           )
          SIncorrectPIN -> EjectCard HasCI >>>
                           Message "Incorrect PIN. Please remove your card and cash"
        )


instance SmGo ATMCmd IO where
  runSM = runATM

ioUnit :: IO (SomeSing Unit) 
ioUnit = return $ SomeSing SMkUnit

runATM :: forall (res :: k) instate outstate_fn. ATMCmd instate outstate_fn res -> IO (SomeSing k)
runATM InsertCard = do putStrLn "Please insert your card (press enter)"
                       x <- getLine
                       ioUnit
runATM (EjectCard _) = 
                do putStrLn "Card ejected"
                   ioUnit
runATM GetPIN = 
                do putStr "Enter PIN: "
                   readPIN
runATM (CheckPIN pin) = 
                if fromSing pin == fromSing testPIN
                then return $ SomeSing SCorrectPIN
                else return $ SomeSing SIncorrectPIN
runATM GetAmount = 
                do putStr "How much would you like? "
                   readNat
runATM (Dispense amount) = 
                do putStrLn ("Here is " ++ show amount)
                   ioUnit
runATM (Message msg) = 
                do putStrLn msg
                   ioUnit
runATM (Pure res) = return $ SomeSing res

runATM (x `Bind` f) = 
                do ax <- runATM x 
                   case ax of
                     SomeSing sax -> runATM (f $ unsafeCoerce sax)
