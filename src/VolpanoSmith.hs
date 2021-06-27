{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VolpanoSmith where

import GHC.TypeLits (Nat, type (<=))
import GHC.TypeLits.Extra (Max, Min)
import Data.Kind (Type)
import Data.Data (type (:~:)(Refl))

--------------------------------------------------------------------------------
-- Basic language without Information-Flow Security enforcement
--------------------------------------------------------------------------------

newtype Variable0 = Variable0 String

infixr 6 :+.
data Exp0 where
  EInt0 :: Int -> Exp0
  EVar0 :: Variable0 -> Exp0
  (:+.) :: Exp0 -> Exp0 -> Exp0

infixl 5 :=.
infixl 4 :>>.
data Cmd0 where
  (:=.)  :: Variable0 -> Exp0 -> Cmd0
  (:>>.) :: Cmd0 -> Cmd0 -> Cmd0
  ITE0   :: Exp0 -> Cmd0 -> Cmd0 -> Cmd0
  While0 :: Exp0 -> Cmd0 -> Cmd0

type Program0 = Cmd0

simpleProgram :: Program0
simpleProgram =
  x :=. EInt0 42 :>>.
  ITE0 (EVar0 x)
    (While0 (EVar0 y) $
      y :=. EVar0 y :+. EInt0 (-1) :>>.
      x :=. EVar0 x :+. EInt0 1)
    (y :=. EInt0 24)
  where
  x = Variable0 "x"
  y = Variable0 "y"

--------------------------------------------------------------------------------
-- Privacy enforcing programs
--------------------------------------------------------------------------------

type Level = Nat

newtype Variable (l :: Level) = Variable String

infixr 6 :+
data Exp (level :: Level) where
  EInt  :: Int -> Exp 0
  EVar  :: Variable level -> Exp level
  (:+) :: Exp level1 -> Exp level2 -> Exp (Max level1 level2)

infixl 5 :=
infixl 4 :>>
data Cmd (level :: Level) where
  (:=)  :: (le <= lx) => Variable lx -> Exp le -> Cmd lx
  (:>>) :: Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
  ITE   :: (lb <= Min l1 l2) => Exp lb -> Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
  While :: (lb <= l) => Exp lb -> Cmd l -> Cmd l

data Program (cmd :: Level -> Type) = forall l. Program (cmd l)

--------------------------------------------------------------------------------
-- Example programs
--------------------------------------------------------------------------------

public :: Variable 0
public = Variable "public"

private :: Variable 999
private = Variable "private"

compoundPrivateExp :: Exp 999
compoundPrivateExp = EVar public :+ EVar private

simpleAssignmentOK :: Program Cmd
simpleAssignmentOK = Program $
  private := EVar public

  {-
simpleAssignmentKO :: Program Cmd
simpleAssignmentKO = Program $
  public := EVar private
  -}

tempAssignmentOK :: Program Cmd
tempAssignmentOK = Program $
  temp := EVar public :>>
  private := EVar temp
  where
  temp = Variable @5 "temp"

implicitPublicFlowOK :: Program Cmd
implicitPublicFlowOK = Program $
  ITE (EVar public)
    (public := EInt 42)
    (private := EVar public)

  {-
implicitPrivateFlowKO :: Program Cmd
implicitPrivateFlowKO = Program $
  ITE (EVar private)
    (public := EInt 42)
    (private := EVar public)
  -}

  {-
implicitPrivateFlowOKKO :: Program Cmd
implicitPrivateFlowOKKO = Program $
  ITE (EVar private)
    (public := EInt 42)
    (public := EInt 42)
  -}

implicitPrivateFlowOK :: Program Cmd
implicitPrivateFlowOK = Program $
  ITE (EVar private)
    (private := EInt 42)
    (private := EVar public)

lemmaMax0 :: Max level 0 :~: level
lemmaMax0 = Refl

adder :: forall level. Int -> Variable level -> Cmd level
adder i var | Refl <- lemmaMax0 @level = var := EVar var :+ EInt i

inc, dec :: Variable level -> Cmd level
inc = adder 1
dec = adder (-1)

halveOK :: Program Cmd
halveOK = Program $
  finished := EInt 0 :>>
  public := EInt 42 :>>
  While (EVar pubCounter)
    (dec pubCounter :>>
     dec pubCounter :>>
     inc public) :>>
  inc finished
  where
  finished = Variable @0 "finished"
  pubCounter = Variable @0 "pubCounter"

halveCovertKO :: Program Cmd
halveCovertKO = Program $
  finished := EInt 0 :>>
  private := EInt 42 :>>
  While (EVar privCounter)
    (dec privCounter :>>
     dec privCounter :>>
     inc private) :>>
  inc finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"

--------------------------------------------------------------------------------
-- Termination-sensitive privacy enforcing programs
--------------------------------------------------------------------------------

infixl 5 :==
infixl 4 :>>>
data Cmd' (level :: Level) where
  Skip'  :: Cmd' level
  (:==)  :: (le <= lx) => Variable lx -> Exp le -> Cmd' lx
  (:>>>) :: Cmd' l1 -> Cmd' l2 -> Cmd' (Min l1 l2)
  ITE'   :: (lb <= Min l1 l2) => Exp lb -> Cmd' l1 -> Cmd' l2 -> Cmd' (Min l1 l2)
  While' :: Exp 0 -> Cmd' l -> Cmd' l

adder' :: forall level. Int -> Variable level -> Cmd' level
adder' i var | Refl <- lemmaMax0 @level = var :== EVar var :+ EInt i

inc', dec' :: Variable level -> Cmd' level
inc' = adder' 1
dec' = adder' (-1)

halveOK' :: Program Cmd'
halveOK' = Program $
  finished :== EInt 0 :>>>
  private :== EInt 0 :>>>
  While' (EVar pubCounter)
    (dec' pubCounter :>>>
     dec' pubCounter :>>>
     inc' private) :>>>
  inc' finished
  where
  finished = Variable @0 "finished"
  pubCounter = Variable @0 "pubCounter"

  {-
halveCovertKO' :: Program Cmd'
halveCovertKO' = Program $
  finished :== EInt 0 :>>>
  private :== EInt 0 :>>>
  While' (EVar privCounter)
    (dec' privCounter :>>>
     dec' privCounter :>>>
     inc' private) :>>>
  inc' finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"
  -}

  {-
halveCovertOKKO :: Program Cmd'
halveCovertOKKO = Program $
  privCounter :== EInt 42 :>>>
  finished :== EInt 0 :>>>
  private :== EInt 0 :>>>
  While' (EVar privCounter)
    (dec' privCounter :>>>
     dec' privCounter :>>>
     inc' private) :>>>
  inc' finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"
  -}
