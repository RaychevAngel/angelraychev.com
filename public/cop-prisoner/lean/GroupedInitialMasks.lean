import GroupedArena

/-! Linear-size initial/collision mask checks. A common valid-cop mask
and one excluded collision position replace a quadratic table of pairs. -/
namespace Delivery.GroupedInitialMasks
open GroupedArena

theorem has_full {n : Nat} (c : Fin n) : Has (2^n-1) c := by
  simp only [Has,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact c.isLt

theorem has_xor_power_of_ne {n : Nat} (mask : Nat) (p c : Fin n)
    (different : c≠p) : Has (mask ^^^ 2^p.val) c ↔ Has mask c := by
  have values : p.val≠c.val := by
    intro same
    exact different (Fin.ext same.symm)
  simp only [Has,Nat.testBit_xor,Nat.testBit_two_pow_of_ne values,Bool.xor_false]

theorem collision_coverage {R : Type} {n : Nat} (present : R → Prop)
    (position : R → Fin n) (masks : R → Nat)
    (rows : ∀ r, (present r → Has (masks r) (position r)) ∧
      (¬present r → masks r=2^n-1)) :
    ∀ r c, (¬present r ∨ position r=c) → Has (masks r) c := by
  intro r c collision
  by_cases inside : present r
  · rcases collision with absent|same
    · exact False.elim (absent inside)
    · rw [←same]
      exact (rows r).1 inside
  · rw [(rows r).2 inside]
    exact has_full c

theorem required_coverage {R : Type} {n : Nat} (present : R → Prop)
    (valid : Fin n → Prop) (position : R → Fin n)
    (validMask : Nat) (masks : R → Nat)
    (valid_bits : ∀ c, valid c → Has validMask c)
    (rows : ∀ r, present r → masks r=validMask ^^^ 2^(position r).val) :
    ∀ r c, present r → valid c → ¬(¬present r ∨ position r=c) →
      Has (masks r) c := by
  intro r c inside permitted noncollision
  rw [rows r inside]
  apply (has_xor_power_of_ne validMask (position r) c ?_).mpr
  · exact valid_bits c permitted
  · intro same
    exact noncollision (Or.inr same.symm)

#print axioms collision_coverage
#print axioms required_coverage
end Delivery.GroupedInitialMasks
