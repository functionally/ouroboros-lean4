import Praos.Variables

open Praos.Variables


namespace Praos.Impl


structure PartyImpl where
  pid : Nat
deriving Repr, DecidableEq


structure SortitionImpl where
  schedule : List (Slot × PartyImpl)

instance instSortitionImpl : @IsSortition PartyImpl SortitionImpl where
  isLeader so sl pa := so.schedule.elem ⟨sl, pa⟩

variable {so : SortitionImpl}


structure BlockHashImpl where
  val : Option (Nat × Nat)
deriving Repr, Inhabited, DecidableEq


structure BlockImpl where
  slot : Slot
  creator : PartyImpl
  parent : BlockHashImpl
  valid : instSortitionImpl.isLeader so slot creator
deriving Repr

private def hashBlock : @BlockImpl so → BlockHashImpl
| ⟨sl, pa, _, _⟩ => BlockHashImpl.mk $ some ⟨sl, pa.pid⟩

instance instBlockImpl (so : SortitionImpl) : @IsBlock PartyImpl SortitionImpl instSortitionImpl BlockHashImpl instInhabitedBlockHashImpl so BlockImpl where
  create sl pa bh :=
    have h : IsSortition.isLeader so sl pa := by
      simp [IsSortition.isLeader]
      sorry
    BlockImpl.mk sl pa bh h
  slot := BlockImpl.slot
  creator := BlockImpl.creator
  parent := BlockImpl.parent
  hash := hashBlock
  valid := BlockImpl.valid
  create_creator := by simp [BlockImpl.mk]
  create_slot := by simp [BlockImpl.mk]
  create_parent := by simp [BlockImpl.mk]
  not_genesis_hash := by simp [hashBlock, genesisBlockHash, Inhabited.default]

namespace Example

  def pax := PartyImpl.mk 1
  def sox := SortitionImpl.mk [⟨1, pax⟩]
  def bhx := BlockHashImpl.mk none

  theorem h : instSortitionImpl.isLeader sox 1 pax := by
    simp [IsSortition.isLeader, List.elem]
    have _ : (1, pax) == (1, pax) := by rfl
    simp [*]
  #check h

  def blx : @BlockImpl sox := (instBlockImpl sox).create 1 pax bhx
  #eval blx

end Example


end Praos.Impl
