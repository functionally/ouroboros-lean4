
import Hoare
import Std.Data.HashMap

open Hoare (HoareM)
open Std


namespace Praos.Spec


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


structure BlockTree where
  blocks : HashMap BlockHash (Block × Nat)

instance : Inhabited BlockTree where
  default := {
    blocks := HashMap.empty.insert genesisBlockHash ⟨Block.genesis, 0⟩
  }

namespace BlockTree

  def insert (bt : BlockTree) (bl : Block) : BlockTree :=
    if bt.blocks.contains bl.hash
      then bt
      else match bl with
           | Block.genesis => Inhabited.default
           | bl'@h₀:(Block.extend _ _ _ _ _) =>
                    have h : bl' ≠ Block.genesis := by
                      rw [h₀]
                      apply Block.noConfusion
                    let ph := bl'.parent h
                    let pw := match bt.blocks.find? ph with
                              | none => 0
                              | some ⟨_, w⟩ => w
           {
             bt with
               blocks := bt.blocks.insert bl.hash ⟨bl, pw + 1⟩
           }

  def maxWeight : BlockTree → Nat :=
    HashMap.fold (fun acc _ ↦ max acc ∘ Prod.snd) 0 ∘ BlockTree.blocks

  def maxTips (bt : BlockTree) : List BlockHash :=
    let w := maxWeight bt
    bt.blocks.fold (fun acc _ v ↦ if v.snd = w then v.fst.hash :: acc else acc) []

end BlockTree


structure Context where
  clock : Slot
  blockTree : BlockTree
  mempool : HashMap Tx Unit

instance : Inhabited Context where
  default :=
    {
      clock := 0
    , blockTree := Inhabited.default
    , mempool := Inhabited.default
    }

namespace Context

  def tick (cx : Context) : Context :=
    {cx with clock := cx.clock + 1}

  def receive (cx : Context) (bl : Block) : Context :=
    {cx with blockTree := cx.blockTree.insert bl}

  def submit (cx : Context) (tx : Tx) : Context :=
    {cx with mempool := cx.mempool.insert tx ()}

  def maxWeight : Context → Nat :=
    BlockTree.maxWeight ∘ Context.blockTree

  def maxTips : Context → List BlockHash :=
    BlockTree.maxTips ∘ Context.blockTree

end Context


structure Observation where
  clock : Slot
  tip : BlockHash
deriving Repr, DecidableEq


class IsNode (Node : Type) where
  init : Node
  tick : Node → Option Block × Node
  receive : Block → Node → Node
  submit : Tx → Node → Node
  observe : Node → Observation


inductive Action where
| Tick : Action
| Receive : Block → Action
| Submit : Tx → Action
deriving Repr, DecidableEq, BEq


abbrev State (Node : Type) := Context × Node


def Ticked (Node : Type) [IsNode Node] : Hoare.Post (State Node) (Option Block)
| _, _, ⟨cx, no⟩ =>
    let ob := IsNode.observe no
    let noClock := ob.clock
    let cxClock := cx.clock
    cxClock = noClock

def ticked (Node : Type) [IsNode Node] : HoareM HoareM.Always (Option Block) (Ticked Node) :=
  {
    run := fun ⟨cx, no⟩ ↦
      let cx' := cx.tick
      let ⟨out, no'⟩ := IsNode.tick no
      ⟨out, ⟨Option.elim out cx' cx'.receive, no'⟩⟩
  , valid := sorry
  }

#check ticked

instance : Decidable (HoareM.Always ()) where

#check HoareM.Always ()

def z : Hoare.Pre Unit := HoareM.Always
#check z
#eval decide z

structure HoareM' {σ : Type} (p : Hoare.Pre σ) (α : Type) (q : Hoare.Post σ α) where
  run : σ → α × σ
  valid : ∀ s : σ, match run s with | ⟨x, s'⟩ => decide (p s) → decide (q s x s')


end Praos.Spec
