import Peras.Variables

open Peras.Variables


namespace Peras.Impl


structure PartyImpl where
  pid : Nat
deriving DecidableEq


structure BlockHashImpl where
  val : Option (Nat × Nat)
deriving Inhabited, DecidableEq


structure BlockImpl where
  slot : Slot
  creator : PartyImpl
  parent : BlockHashImpl

private def hashBlock : BlockImpl → BlockHashImpl
| ⟨sl, pa, _⟩ => BlockHashImpl.mk $ some ⟨sl, pa.pid⟩

instance : @IsBlock PartyImpl BlockHashImpl _ BlockImpl where
  create := BlockImpl.mk
  slot := BlockImpl.slot
  creator := BlockImpl.creator
  parent := BlockImpl.parent
  hash := hashBlock
  create_creator := by simp [BlockImpl.mk]
  create_slot := by simp [BlockImpl.mk]
  create_parent := by simp [BlockImpl.mk]
  not_genesis_hash := by simp [hashBlock, genesisBlockHash, Inhabited.default]


end Peras.Impl
