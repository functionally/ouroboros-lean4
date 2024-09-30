
import Mathlib.Data.Set.Defs


namespace Praos.Variables


def Slot : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div

instance {i : Nat} : OfNat Slot i := instOfNatNat i


variable {Party : Type}
[DecidableEq Party]


class IsSortition (Sortition : Type) where
  isLeader : Sortition → Slot → Party → Prop

variable {Sortition : Type}
[instSortition : @IsSortition Party Sortition]


variable {BlockHash : Type}
[instInhabitedBlockHash : Inhabited BlockHash]
[DecidableEq BlockHash]

def genesisBlockHash : BlockHash :=
  Inhabited.default


class IsBlock (so : Sortition) (Block : Type) where
  create : Slot → Party → BlockHash → Block
  slot : Block → Slot
  creator : Block → Party
  parent : Block → BlockHash
  hash : Block → BlockHash
  valid : ∀ bl, instSortition.isLeader so (slot bl) (creator bl)
  create_slot : ∀ sl pa bh, slot (create sl pa bh) = sl
  create_creator : ∀ sl pa bh, creator (create sl pa bh) = pa
  create_parent : ∀ sl pa bh, parent (create sl pa bh) = bh
  not_genesis_hash : ∀ bl, ¬ hash bl = genesisBlockHash

variable {so : Sortition}

variable {Block : Type}
[instBlock : @IsBlock Party Sortition instSortition BlockHash instInhabitedBlockHash so Block]


class IsChain (Chain : Type) where
  genesis : Chain
  tipSlot : Chain → Slot
  tipHash : Chain → BlockHash
  extend : Block → Chain → Chain
  expand (ch : Chain) : ¬ ch = genesis → Block × Chain
  eq : DecidableEq Chain
  valid (bl : Block) (ch : Chain) : tipSlot ch < instBlock.slot bl ∧ tipHash ch = instBlock.parent bl
  genesis_slot : tipSlot genesis = 0
  genesis_hash : tipHash genesis = genesisBlockHash
  extend_not_genesis : ∀ bl ch, ¬ extend bl ch = genesis
  extend_expand : ∀ bl ch, expand (extend bl ch) (by apply extend_not_genesis) = ⟨bl , ch⟩

variable {Chain : Type}
[instChain : @IsChain Party Sortition instSortition BlockHash instInhabitedBlockHash so Block instBlock Chain]


class IsState (State : Type) where
  chainPref : Chain
  chains : Set Chain


end Praos.Variables
