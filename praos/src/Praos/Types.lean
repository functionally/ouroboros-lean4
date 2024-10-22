
import Std.Data.HashMap

open Std


namespace Praos.Types


def Slot : Type := Nat
deriving Repr, DecidableEq, BEq, LT, Add, Sub, Mul, Div, Hashable

instance {i : Nat} : OfNat Slot i := instOfNatNat i


def Party : Type := Nat
deriving Repr, DecidableEq, Hashable


def BlockHash : Type := UInt64
deriving Repr, DecidableEq, BEq, Hashable

def genesisBlockHash : BlockHash :=
  UInt64.ofNat $ UInt64.size - 1

instance : Inhabited BlockHash where
  default := genesisBlockHash


structure Tx where
  id : UInt64
  size : Nat
deriving Repr, DecidableEq, BEq, Hashable


def Body := List Tx
deriving Repr, DecidableEq, BEq, Hashable


-- FIXME: Replace with a cryptographic hash function.
def hashBlock : Slot → Party → BlockHash → Body → BlockHash
| sl , cr, pb, bo => hash $ Prod.mk (Prod.mk sl cr) (Prod.mk pb bo)


abbrev Sortition := Slot → Party → Prop


inductive Block where
| genesis : Block
| extend : Slot → Party → BlockHash → Body → BlockHash → Block
deriving Repr, DecidableEq

instance : Inhabited Block where
  default := Block.genesis

namespace Block

  def slot : Block → Slot
  | genesis => 0
  | extend sl _ _ _ _ => sl

  def creator (bl : Block) (_ : ¬ bl = genesis) : Party :=
    match bl with
    | genesis => by contradiction
    | extend _ cr _ _ _ => cr

  def parent (bl : Block) (_ : ¬ bl = genesis) : BlockHash :=
    match bl with
    | genesis => by contradiction
    | extend _ _ ph _ _ => ph

  def body (bl : Block) (_ : ¬ bl = genesis) : Body :=
    match bl with
    | genesis => by contradiction
    | extend _ _ _ bo _ => bo

  def hash : Block → BlockHash
  | genesis => Inhabited.default
  | extend _ _ _ _ ha => ha

  def valid (sortition : Sortition) (pb : Block) (bl : Block) (h : ¬ bl = genesis) : Prop :=
      slot pb < slot bl
    ∧ hash pb = parent bl h
    ∧ hash bl = hashBlock (slot bl) (creator bl h) (parent bl h) (body bl h)
    ∧ sortition (slot bl) (creator bl h)

end Block


inductive Chain where
| genesis : Chain
| extend : Block → Chain → Chain
deriving Repr, DecidableEq

instance : Inhabited Chain where
  default := Chain.genesis

namespace Chain

  def tip : Chain → Block
  | genesis => Block.genesis
  | extend bl _ => bl

  def weight : Chain → Nat
  | genesis => 0
  | extend _ ch => 1 + weight ch

  def valid (sortition : Sortition): Chain → Prop
  | genesis => True
  | extend bl ch => let pb := ch.tip
                    have h : ¬ bl = Block.genesis := by
                      sorry
                    Block.valid sortition pb bl h ∧ valid sortition ch

end Chain


end Praos.Types
