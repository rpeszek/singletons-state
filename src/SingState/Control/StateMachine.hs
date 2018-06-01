{-# LANGUAGE KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
      , TypeInType 
      , TypeOperators 
      , TypeFamilies
      -- , UndecidableInstances 
      , ScopedTypeVariables
      -- , TypeFamilyDependencies
      , ConstraintKinds
      , MultiParamTypeClasses
      -- , FlexibleInstances
      , FlexibleContexts
      , TypeApplications
      , AllowAmbiguousTypes
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  SingState.Control.ParametrizedMonad
-- Copyright   :  (C) 2018 Robert Peszek
-- License     :  (see the file LICENSE)
-- Maintainer  :  Robert Peszek
-- Stability   :  experimental
-- Portability :  non-portable
--
-- `Indexed Monad` abstraction for dependently typed state machines.
-- This approach mimics 'monad-param' library approach
-- 'Control.Monad.Parameterized' that binds across potentially 
-- different monads.
-- Here state machine is parametrized by inital state and a type level
-- function that defines end state in terms of the current payload/result 
-- type.  States are expected to belong to a dedicated kind 'ks', but 
-- binding can happen between different state machines with different 
-- state kinds. 
--------------------------------------------------------------------

module SingState.Control.StateMachine where

import Data.Kind (Type)
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Function

----------------------------------------------------------------------
---- Main definitions ------------------------------------------------
----------------------------------------------------------------------

-- | Type sigature of a state machine dsl
-- 'ks' kind contains states
-- 'kr' kind contains return/payload types
-- Example
-- @
-- $(singletons [d|
--  data MyState = On | Off
--  |])
-- data MyDsl (start_state :: MyState) (end_state_fn :: kr ~> MyState) (payload :: kr) where
-- @
-- 'end_state_fn' can be viewed as defining the end state based on the 'payload'
type SM_sig ks kr = (ks -> (kr ~> ks) -> kr -> Type)

-- type ST_tran_sig ks1 ks2 = (ks1 ~> ks2)

class SmMap (m :: SM_sig ks kr) where
  smMap :: (Sing a -> Sing b) -> m s f a -> m s f b

-- | Monadic 'return' with 'a' is replaced with 'Sing a'
class SmPure (m :: SM_sig ks kr) where 
   smPure :: Sing a -> m (state_fn @@ a) state_fn a

-- | A more explicit way to create state
class InitState (s :: ks) (sf :: kr ~> ks) (m :: SM_sig ks kr) where
    smInit :: Sing a -> m s sf a

-- | This approach is similar to one found in 'monad-param' 'Control.Monad.Parameterized'
-- allows to combine computations from 2 different state machines 'm1' and 'm2' 
-- with different state kinds 'ks1' and 'ks2'
-- 'tr' is a type level transform that maps states used by 'm1' and 'm2'.
class SmBind (tr :: ks1 ~> ks2) (m1 :: SM_sig ks1 kr1) (m2 :: SM_sig ks2 kr2) where 
   -- | equivalent of monadic '>>='
   smBind :: Sing tr -> m1 state1b state1e_fn a -> (Sing a -> m2 (tr @@ (state1e_fn @@ a)) state2e_fn b) -> m2 (tr @@ state1b) state2e_fn b
   -- | equivalent of monadic '>>'
   smNext :: Sing tr -> m1 state1b state1e_fn a -> m2 (tr @@ (state1e_fn @@ a)) state2e_fn b -> m2 (tr @@ state1b) state2e_fn b
   smNext tr m k = smBind tr m (\ _ -> k) 

-- | unfortunatelly, join does not come for free from 'smBind' 
-- this is because 'm (statee_fn @@ a) statee_fn2 a' has kind 'Type' 
-- and 'Sing (x :: Type)' is defined as 'TypeRep x'.
-- This breaks the monadic laws and could be blamed on Haskell not being dependently 
-- typed.
-- DSL should be able to define helper constructor for Join.
class SmJoin (m :: SM_sig ks Type) where
   smJoin :: m stateb statee_fn (m (statee_fn @@ a) statee_fn2 a) -> m stateb statee_fn2 a

-- | Interpreter of state machine dsl. 
-- This approach ingores start and end state and does not assume anything 
-- about them.
class SmGo (m :: SM_sig ks kr) n where 
    runSM :: m state state_fn a -> n (SomeSing kr)

-- class GetState(m :: SM_sig ks kr)  where
--     startState :: m state state_fn a -> Sing state

----------------------------------------------------------------------
---- State homogenious version ---------------------------------------
----------------------------------------------------------------------

-- | Homogenious version of bind where kind defining possible states 
-- does not change 
type HSmBind m1 m2 = SmBind IdSym0 m1 m2

-- | Equivalent to monadic '>>='  
(>>>=) :: HSmBind m1 m2 =>
     m1 state1b state1e_fn a
     -> (Sing a -> m2 (state1e_fn @@ a) state2e_fn b)
     -> m2 state1b state2e_fn b
(>>>=) = smBind (singFun1 @IdSym0 sId)

-- | Equivalent to monadic '>>' 
(>>>) :: HSmBind m1 m2 =>
     m1 state1b state1e_fn a
     -> m2 (Apply state1e_fn a) state2e_fn b -> m2 state1b state2e_fn b
(>>>) = smNext (singFun1 @IdSym0 sId)

----------------------------------------------------------------------
---- Completely homogenious version ----------------------------------
----------------------------------------------------------------------

type HHSmBind m = SmBind IdSym0 m m

----------------------------------------------------------------------
---- Monadic methods -------------------------------------------------
----------------------------------------------------------------------

-- | Interstingly, SmMap does not follow from @(SmPure m, HHSmBind m)@ contraints
-- using a standard 'bind pure' implementation.
-- This code shows why.   
smLift :: (InitState (sf @@ a) sf m, HHSmBind m) => (Sing (a :: kr) -> Sing (b :: kr)) -> m s sf a -> m s sf b  
smLift f m = m >>>= (smInit . f )

-- | Represents a list of state machines sharing the same return kind 'kr'
-- that can be executed in monad 'n'.
-- Each element in the list needs to match states with previous and next element
data SmQueue n kr (s :: ks) (ms :: [Type]) where 
   SmNil :: SmQueue n kr s '[]
   SmCons :: SmGo m n => 
             m stateb statee_fn (a :: kr) -> 
             SmQueue n kr (statee_fn @@ a) ms -> 
             SmQueue n kr stateb ((m stateb statee_fn a) ': ms)

-- TODO smFold

-- | Computes a list of results from the chain (could be usefull for tracing etc).
runSmSequence :: (Monad n) => SmQueue n kr s ms -> n [SomeSing kr] 
runSmSequence SmNil  = return []
runSmSequence (SmCons m smQueue) = (:) <$> runSM m <*> runSmSequence smQueue
