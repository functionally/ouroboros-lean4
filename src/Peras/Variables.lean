
import Mathlib.Data.Set.Defs


namespace Peras.Variables


def Slot : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div

instance {i : Nat} : OfNat Slot i := instOfNatNat i


def Round : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div


variable {Party : Type}
[DecidableEq Party]


class IsSortition (Sortition : Type) where
  isLeader : Slot → Party → Prop
  isVoter : Round → Party → Prop

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


class IsVote (Vote : Type) where
  create (ro : Round) (pa : Party) : instSortition.isVoter ro pa → BlockHash → Vote
  round : Vote → Round
  creator : Vote → Party
  block : Vote → BlockHash
  eq : DecidableEq Vote
  create_round : ∀ ro pa bh so, round (create ro pa so bh) = ro
  create_creator : ∀ ro pa bh so, creator (create ro pa so bh) = pa
  create_block : ∀ ro pa bh so, block (create ro pa so bh) = bh

variable {Vote : Type}
[instVote : @IsVote Party Sortition instSortition BlockHash Vote]


class IsCert (Cert : Type) where
  genesis : Cert
  create : Round → BlockHash → Cert
  round : Cert → Round
  block : Cert → BlockHash
  eq : DecidableEq Cert
  create_round : ∀ ro bh, round (create ro bh) = ro
  create_block : ∀ ro bh, block (create ro bh) = bh

variable {Cert : Type}
[instCert : IsCert Cert]


class IsState (State : Type) where
  chainPref : Chain
  chains : Set Chain
  votes : Set Vote
  certPrime : Cert
  certStar : Cert


end Peras.Variables
