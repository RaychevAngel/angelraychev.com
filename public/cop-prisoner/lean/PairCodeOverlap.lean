import PairCodeConstruction
import ProtectedParameters
import CircleGuardedConstruction

/-! A short sufficient overlap chain for all orders at least seventy-nine.
Above 895 the pair-code parameter is simply floor(n/28). The remaining
orders use a kernel-checked arithmetic table, not graph or game data. -/
namespace Delivery.PairCodeOverlap
open FiniteGame Extremal

def base (n k : Nat) : Nat := (4*k-2)*n-2*k*(2*k+1)
def protectedTop (n : Nat) : Nat := n*((n+6)/7-1)

def smallParameter (n : Nat) : Nat :=
  ((List.range 34).find? fun k => decide (6≤k ∧ 2*k≤n ∧ n≤k*(k-3))).getD 0

def circleParameter (n : Nat) : Nat :=
  ([7,11,15,19].find? fun h => decide (Nat.Coprime n h)).getD 0

def Overlap (n k h : Nat) : Prop :=
  6≤k ∧ 2*k≤n ∧ n≤k*(k-3) ∧
  (base n k≤protectedTop n ∨
    (5*n≤protectedTop n ∧ 7≤h ∧ h%4=3 ∧ 2*h+2≤n ∧ Nat.Coprime n h ∧
      base n k≤n*CircleGuardedConstruction.degree n h))

instance (n k h : Nat) : Decidable (Overlap n k h) := inferInstanceAs
  (Decidable (6≤k ∧ 2*k≤n ∧ n≤k*(k-3) ∧
  (base n k≤protectedTop n ∨
    (5*n≤protectedTop n ∧ 7≤h ∧ h%4=3 ∧ 2*h+2≤n ∧ Nat.Coprime n h ∧
      base n k≤n*CircleGuardedConstruction.degree n h))))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finite_overlap (j : Fin 817) :
    Overlap (j.val+79) (smallParameter (j.val+79)) (circleParameter (j.val+79)) := by
  revert j
  decide +kernel

theorem large_overlap {n : Nat} (large : 896≤n) :
    Overlap n (n/28) 0 := by
  let k := n/28
  have hk : 32≤k := by omega
  have near : n≤28*k+27 := by omega
  have first : n≤32*(k-3) := by omega
  have capacity : n≤k*(k-3) :=
    Nat.le_trans first (Nat.mul_le_mul_right (k-3) hk)
  have small : 2*k≤n := by omega
  have deg : 4*k-2≤(n+6)/7-1 := by omega
  have bound : base n k≤protectedTop n := by
    exact Nat.le_trans (Nat.sub_le _ _) (by
      simpa only [protectedTop,Nat.mul_comm] using Nat.mul_le_mul_left n deg)
  exact ⟨by omega,small,capacity,Or.inl bound⟩

theorem maximum_of_overlap {n k h m : Nat} (large : 25≤n)
    (overlap : Overlap n k h) (low : 3*n≤m) (high : m≤n*(n-3)) :
    IsMaximum n m (n*(n-1)-m) := by
  obtain ⟨hk,order,capacity,join⟩ := overlap
  by_cases hp : m≤protectedTop n
  · exact ProtectedParameters.maximum large low hp
  · by_cases hb : base n k≤m
    · exact PairCodeConstruction.maximum hk order capacity hb high
    · rcases join with direct | ⟨start,hh,residue,room,coprime,finish⟩
      · omega
      · exact CircleGuardedConstruction.maximum hh residue room coprime (by omega) (by omega)

/-- Explicit pair codes and circle envelopes together attain every missing pair
throughout the full interval from three arrows per vertex to the dense boundary. -/
theorem maximum {n m : Nat} (large : 79≤n) (low : 3*n≤m) (high : m≤n*(n-3)) :
    IsMaximum n m (n*(n-1)-m) := by
  by_cases hn : 896≤n
  · exact maximum_of_overlap (by omega) (large_overlap hn) low high
  · have h := finite_overlap ⟨n-79,by omega⟩
    have eq : n-79+79=n := by omega
    simp only [eq] at h
    exact maximum_of_overlap (by omega) h low high

#print axioms finite_overlap
#print axioms maximum
end Delivery.PairCodeOverlap
