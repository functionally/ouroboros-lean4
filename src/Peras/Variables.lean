
import Mathlib.Data.Set.Defs


namespace Peras.Variables


def Slot : Type := Nat
deriving Repr, DecidableEq, BEq, Ord, Add, Sub, Mul, Div


def Round : Type := Nat
deriving Repr, DecidableEq, BEq, Ord, Add, Sub, Mul, Div


class IsBlock (bl : Type) where
  genesis : bl
  make : bl
  eq : DecidableEq bl

instance [IsBlock bl] : Inhabited bl where
  default := IsBlock.genesis


class IsChain (ch : Type) where
  genesis : ch
--extend [IsBlock bl] : bl → ch → ch
--eq : DecidableEq ch

instance [IsChain ch] : Inhabited ch where
  default := IsChain.genesis


class IsVote (vo : Type) where
  make : vo
  eq : DecidableEq vo


class IsCert (ce : Type) where
  genesis : ce
  make : ce
  eq : DecidableEq ce

instance [IsCert ce] : Inhabited ce where
  default := IsCert.genesis


structure State where
  Block : Type
  Chain : Type
  Vote : Type
  Cert : Type
  instChain : IsChain Chain
  chainPref : Chain
  chains : Set Chain
  votes : Set Vote
  certPrime : Cert
  certStar : Cert

def initial (st : State) : Prop :=
  st.chainPref = @IsChain.genesis st.Chain st.instChain


class IsState (Ch St : Type) where
  instChain : St → IsChain Ch
  chainPref : St → Ch

def is_initial [IsState Ch St] (st : St) : Prop :=
  IsState.chainPref st = @IsChain.genesis Ch (IsState.instChain st)


class IsState' (Ch St : Type) where
  instChain : St → IsChain Ch
  chainPref : St → Ch

def is_initial' [IsState' Ch St] [IsChain Ch] (st : St) : Prop :=
  IsState'.chainPref st = (IsChain.genesis : Ch)


class IsState'' (Ch St : Type) [IsChain Ch] where
  chainPref : St → Ch

def is_initial'' [IsChain Ch] [IsState'' Ch St] (st : St) : Prop :=
  IsState''.chainPref st = (IsChain.genesis : Ch)


variable {Ch : Type}
[IsChain Ch]

class IsState''' (St : Type) where
  chainPref : St → Ch

#check @IsState'''

def is_initial''' [@IsState''' Ch St] (st : St) : Prop :=
  IsState'''.chainPref st = (IsChain.genesis : Ch)

#check is_initial'''


inductive Chain where
| gen : Chain
| mk : Nat → Chain
| oth : Chain

instance iChain : IsChain Chain where
  genesis := Chain.gen

structure State' where
  only : Chain

instance iState : @IsState''' Chain State' where
  chainPref st := st.only

example : @is_initial''' Chain iChain State' iState ⟨ Chain.gen ⟩ := by
  rfl

example : @is_initial''' Chain iChain State' iState ⟨ Chain.oth ⟩ := by
  rfl


end Peras.Variables
