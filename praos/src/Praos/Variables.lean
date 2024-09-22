
import Mathlib.Data.Set.Defs


namespace Praos.Variables


def Slot : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div

instance {i : Nat} : OfNat Slot i := instOfNatNat i


variable {Party : Type}
[DecidableEq Party]


class IsSortition (Sortition : Type) where
  isLeader : Slot → Party → Prop

variable {Sortition : Type}
[instSortition : @IsSortition Party Sortition]


variable {BlockHash : Type}
[instInhabitedBlockHash : Inhabited BlockHash]
[DecidableEq BlockHash]

def genesisBlockHash : BlockHash :=
  Inhabited.default


class IsBlock (Block : Type) where
  create (sl : Slot) (pa : Party) : instSortition.isLeader sl pa → BlockHash → Block
  slot : Block → Slot
  creator : Block → Party
  parent : Block → BlockHash
  hash : Block → BlockHash
  create_slot : ∀ sl pa bh so, slot (create sl pa so bh) = sl
  create_creator : ∀ sl pa bh so, creator (create sl pa so bh) = pa
  create_parent : ∀ sl pa bh so, parent (create sl pa so bh) = bh
  not_genesis_hash : ∀ bl, ¬ hash bl = genesisBlockHash

variable {Block : Type}
[instBlock : @IsBlock Party Sortition instSortition BlockHash instInhabitedBlockHash Block]


class IsChain (Chain : Type) where
  genesis : Chain
  tipSlot : Chain → Slot
  tipHash : Chain → BlockHash
  extend (bl : Block) (ch : Chain) : tipSlot ch < instBlock.slot bl ∧ tipHash ch = instBlock.parent bl → Chain
  expand (ch : Chain) : ¬ ch = genesis → Block × Chain
  eq : DecidableEq Chain
  genesis_slot : tipSlot genesis = 0
  genesis_hash : tipHash genesis = genesisBlockHash
  extend_not_genesis : ∀ bl ch h, ¬ extend bl ch h = genesis
  extend_expand : ∀ bl ch h, expand (extend bl ch h) (by apply extend_not_genesis) = ⟨bl , ch⟩

variable {Chain : Type}
[instChain : @IsChain Party Sortition instSortition BlockHash instInhabitedBlockHash Block instBlock Chain]


class IsState (State : Type) where
  chainPref : Chain
  chains : Set Chain


end Praos.Variables
