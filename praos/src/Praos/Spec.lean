
import Std.Data.HashMap

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
      else if h : bl = Block.genesis
             then Inhabited.default
             else let ph := bl.parent h
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


def Output : Action → Type
| Action.Tick => Option Block
| Action.Receive _ => Unit
| Action.Submit _ => Unit


abbrev State (Node : Type) := Context × Node


structure HoareDec (σ α : Type) where
  pre : σ → Bool
  run : σ → α × σ
  post : σ → α → σ → Bool

namespace HoareDec

  def valid {σ α : Type} (h : HoareDec σ α) (s : σ) : Bool :=
    let ⟨x, s'⟩ := h.run s
    h.pre s → h.post s x s'

  structure Result (σ α : Type) where
    output : Option α
    state : σ
    validity : Bool

  def step {σ α : Type} (h : HoareDec σ α) (s : σ) : Result σ α :=
    let ⟨x, s'⟩ := h.run s
    if h.pre s
      then ⟨some x, s', h.post s x s'⟩
      else ⟨none, s, true⟩

end HoareDec


def ticked (Node : Type) [IsNode Node] : HoareDec (State Node) (Option Block) :=
  {
    pre := fun _ ↦ true
  , run := fun ⟨cx, no⟩ ↦
      let cx' := cx.tick
      let ⟨out, no'⟩ := IsNode.tick no
      ⟨out, ⟨Option.elim out cx' cx'.receive, no'⟩⟩
  , post := fun _ _ ⟨cx', no'⟩ ↦
      let ob := IsNode.observe no'
      let noClock := ob.clock
      let cxClock := cx'.clock
      cxClock = noClock
  }

def act (Node : Type) [IsNode Node] (a : Action) : HoareDec (State Node) (Output a) :=
  match a with
  | Action.Tick => ticked Node
  | Action.Receive _ =>
      {
        pre := fun _ => true
      , run := fun st => ⟨(), st⟩
      , post := fun _ _ _ => true
      }
  | Action.Submit _ =>
      {
        pre := fun _ => true
      , run := fun st => ⟨(), st⟩
      , post := fun _ _ _ => true
      }


structure NodeEx where
  clock : Slot
deriving Repr

instance : IsNode NodeEx where
  init := ⟨0⟩
  tick no := ⟨none, ⟨no.clock + 1⟩⟩
  receive _ := id
  submit _ := id
  observe no := ⟨ no.clock , genesisBlockHash ⟩


def st0 : State NodeEx := ⟨Inhabited.default, IsNode.init⟩
#eval st0.snd

def ticked' := act NodeEx Action.Tick

def step1 := ticked'.step st0
def st1 := step1.state
#eval step1.output
#eval st1.snd
#eval step1.validity


end Praos.Spec
