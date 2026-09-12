import SquareCompressionFour
import ProductCompressionEnergy

namespace Princess.SquareCompressionFour
open Princess.ProductCompression Princess.LadderCardinality Princess.FiniteSubsetProfiles

def pairWeight (pair : Fin 3) (v : Room) : Nat :=
  if pair.val = 0 then x v + 2*y v else if pair.val = 1 then x v + 3*y v else 2*x v + 3*y v

def weightedBits (pair : Fin 3) (mask : Nat) : Nat :=
  ((List.finRange 16).map (fun v => if mask.testBit v.val then pairWeight pair v else 0)).sum

def energyCheck (dir : Bool) (mask : Nat) : Bool := decide (∀ pair : Fin 3,
  weightedBits pair (cBits dir mask) ≤ weightedBits pair mask ∧
  (weightedBits pair (cBits dir mask) = weightedBits pair mask → cBits dir mask = mask))

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem energy_batch_false_false_0 : checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 0 = true := by
  decide +kernel

theorem energy_batch_false_false_1 : checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 4 = true := by
  decide +kernel

theorem energy_batch_false_false_2 : checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 1 = true := by
  decide +kernel

theorem energy_batch_false_false_3 : checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 5 = true := by
  decide +kernel

theorem energy_checked_false_false : checkSubsets (energyCheck false) (rooms false) 0 = true := by
  change ((checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 0 && checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 4) && (checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 1 && checkSubsets (energyCheck false) [5, 7, 8, 10, 13, 15] 5)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨energy_batch_false_false_0,energy_batch_false_false_1⟩,⟨energy_batch_false_false_2,energy_batch_false_false_3⟩⟩

theorem energy_batch_false_true_0 : checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 0 = true := by
  decide +kernel

theorem energy_batch_false_true_1 : checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 8 = true := by
  decide +kernel

theorem energy_batch_false_true_2 : checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 2 = true := by
  decide +kernel

theorem energy_batch_false_true_3 : checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 10 = true := by
  decide +kernel

theorem energy_checked_false_true : checkSubsets (energyCheck false) (rooms true) 0 = true := by
  change ((checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 0 && checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 8) && (checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 2 && checkSubsets (energyCheck false) [4, 6, 9, 11, 12, 14] 10)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨energy_batch_false_true_0,energy_batch_false_true_1⟩,⟨energy_batch_false_true_2,energy_batch_false_true_3⟩⟩

theorem energy_batch_true_false_0 : checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 0 = true := by
  decide +kernel

theorem energy_batch_true_false_1 : checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 4 = true := by
  decide +kernel

theorem energy_batch_true_false_2 : checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 1 = true := by
  decide +kernel

theorem energy_batch_true_false_3 : checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 5 = true := by
  decide +kernel

theorem energy_checked_true_false : checkSubsets (energyCheck true) (rooms false) 0 = true := by
  change ((checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 0 && checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 4) && (checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 1 && checkSubsets (energyCheck true) [5, 7, 8, 10, 13, 15] 5)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨energy_batch_true_false_0,energy_batch_true_false_1⟩,⟨energy_batch_true_false_2,energy_batch_true_false_3⟩⟩

theorem energy_batch_true_true_0 : checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 0 = true := by
  decide +kernel

theorem energy_batch_true_true_1 : checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 8 = true := by
  decide +kernel

theorem energy_batch_true_true_2 : checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 2 = true := by
  decide +kernel

theorem energy_batch_true_true_3 : checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 10 = true := by
  decide +kernel

theorem energy_checked_true_true : checkSubsets (energyCheck true) (rooms true) 0 = true := by
  change ((checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 0 && checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 8) && (checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 2 && checkSubsets (energyCheck true) [4, 6, 9, 11, 12, 14] 10)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨energy_batch_true_true_0,energy_batch_true_true_1⟩,⟨energy_batch_true_true_2,energy_batch_true_true_3⟩⟩

theorem energy_checked : ∀ dir p : Bool, checkSubsets (energyCheck dir) (rooms p) 0 = true := by
  intro dir p
  cases dir <;> cases p
  · exact energy_checked_false_false
  · exact energy_checked_false_true
  · exact energy_checked_true_false
  · exact energy_checked_true_true

end Princess.SquareCompressionFour
