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


structure BlockHashImpl where
  val : Option (Nat × Nat)
deriving Repr, Inhabited, DecidableEq


structure BlockImpl where
  slot : Slot
  creator : PartyImpl
  parent : BlockHashImpl
deriving Repr

private def hashBlock : BlockImpl → BlockHashImpl
| ⟨sl, pa, _⟩ => BlockHashImpl.mk $ some ⟨sl, pa.pid⟩

instance instBlockImpl (so : SortitionImpl) : @IsBlock PartyImpl SortitionImpl instSortitionImpl BlockHashImpl instInhabitedBlockHashImpl so BlockImpl where
  create sl pa _ bh := BlockImpl.mk sl pa bh
  slot := BlockImpl.slot
  creator := BlockImpl.creator
  parent := BlockImpl.parent
  hash := hashBlock
  create_creator := by simp [BlockImpl.mk]
  create_slot := by simp [BlockImpl.mk]
  create_parent := by simp [BlockImpl.mk]
  not_genesis_hash := by simp [hashBlock, genesisBlockHash, Inhabited.default]

namespace Example

  def pax := PartyImpl.mk 1
  def sox := SortitionImpl.mk [⟨1, pax⟩]
  def bhx := BlockHashImpl.mk none

  theorem lex : instSortitionImpl.isLeader sox 1 pax := by
    simp [IsSortition.isLeader, List.elem]
    have _ : (1, pax) == (1, pax) := by rfl
    simp [*]
  #print lex

  def blx : BlockImpl := (instBlockImpl sox).create 1 pax lex bhx

end Example


end Praos.Impl
