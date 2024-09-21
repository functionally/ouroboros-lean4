
import Mathlib.Data.Set.Defs


namespace Peras.Variables


def Slot : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div


def Round : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div


variable {Party : Type}
[DecidableEq Party]


variable {BlockHash : Type}
[instInhabitedBlockHash : Inhabited BlockHash]
[DecidableEq BlockHash]

def genesisBlockHash : BlockHash :=
  Inhabited.default


class IsBlock (Block : Type) where
  create : Slot → Party → BlockHash → Block
  slot : Block → Slot
  creator : Block → Party
  parent : Block → BlockHash
  hash : Block → BlockHash
  create_creator : ∀ sl pa bh, creator (create sl pa bh) = pa
  create_slot : ∀ sl pa bh, slot (create sl pa bh) = sl
  create_parent : ∀ sl pa bh, parent (create sl pa bh) = bh
  not_genesis_hash : ¬ hash block = genesisBlockHash

variable {Block : Type}
[instBlock : @IsBlock Party BlockHash instInhabitedBlockHash Block]


class IsChain (Chain : Type) where
  genesis : Chain
  tipSlot : Chain → Slot
  tipHash : Chain → BlockHash
  extend (bl : Block) (ch : Chain) : tipSlot ch < instBlock.slot bl ∧ tipHash ch = instBlock.parent bl → Chain
  expand (ch : Chain) : ¬ ch = genesis → Block × Chain
  eq : DecidableEq Chain
  extend_not_genesis : ∀ bl ch h, ¬ extend bl ch h = genesis
  extend_expand : ∀ bl ch h, expand (extend bl ch h) (by apply extend_not_genesis) = ⟨ bl , ch ⟩

variable {Chain : Type}
[instChain : @IsChain Party BlockHash instInhabitedBlockHash Block instBlock Chain]


class IsVote (Vote : Type) where
  make : Vote
  eq : DecidableEq Vote

variable {Vote : Type}


class IsCert (Cert : Type) where
  genesis : Cert
  make : Cert
  eq : DecidableEq Cert


class IsState (State : Type) where
  chainPref : Chain
  chains : Set Chain
  votes : Set Vote
  certPrime : Cert
  certStar : Cert


end Peras.Variables
