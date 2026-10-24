import Std

/-! Cyclic shifts and two-element containment obstructions for the dense
two-type construction. The offsets and period are arbitrary natural numbers;
all small-spacing hypotheses are stated explicitly. -/
namespace Delivery.CyclicArithmetic

def shift {k : Nat} (i : Fin k) (d : Nat) : Fin k :=
  ⟨(i.val + d) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩

@[simp] theorem shift_zero {k : Nat} (i : Fin k) : shift i 0 = i := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt i.isLt]

theorem shift_add {k : Nat} (i : Fin k) (d e : Nat) :
    shift (shift i d) e = shift i (d + e) := by
  apply Fin.ext
  simp only [shift, Nat.mod_add_mod, Nat.add_assoc]

@[simp] theorem shift_period {k : Nat} (i : Fin k) : shift i k = i := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt i.isLt]

theorem shift_injective {k d : Nat} {i j : Fin k}
    (same : shift i d = shift j d) : i = j := by
  have h := congrArg Fin.val same
  change (i.val + d) % k = (j.val + d) % k at h
  rw [Nat.add_mod_eq_sub, Nat.add_mod_eq_sub, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] at h
  have hi := i.isLt
  have hj := j.isLt
  have hd := Nat.mod_lt d (show 0 < k by have := i.isLt; omega)
  apply Fin.ext
  by_cases wi : i.val + d % k < k <;> by_cases wj : j.val + d % k < k <;>
    simp only [wi,wj,if_true,if_false] at h <;> omega

theorem shift_eq_iff {k : Nat} (i : Fin k) (d e : Nat) :
    shift i d = shift i e ↔ d % k = e % k := by
  constructor
  · intro same
    have h := congrArg Fin.val same
    change (i.val + d) % k = (i.val + e) % k at h
    rw [Nat.add_mod_eq_sub, Nat.add_mod_eq_sub, Nat.mod_eq_of_lt i.isLt] at h
    have hi := i.isLt
    have hd := Nat.mod_lt d (show 0 < k by have := i.isLt; omega)
    have he := Nat.mod_lt e (show 0 < k by have := i.isLt; omega)
    by_cases wd : i.val + d % k < k <;> by_cases we : i.val + e % k < k <;>
      simp only [wd,we,if_true,if_false] at h <;> omega
  · intro same
    apply Fin.ext
    change (i.val + d) % k = (i.val + e) % k
    calc
      _ = (i.val % k + d % k) % k := Nat.add_mod _ _ _
      _ = (i.val % k + e % k) % k := by rw [same]
      _ = _ := (Nat.add_mod _ _ _).symm

theorem shift_ne_self {k d : Nat} (i : Fin k) (positive : 0 < d) (small : d < k) :
    shift i d ≠ i := by
  intro same
  have h := (shift_eq_iff i d 0).mp (same.trans (shift_zero i).symm)
  rw [Nat.mod_eq_of_lt small] at h
  simp only [Nat.zero_mod] at h
  omega

def prev {k : Nat} (i : Fin k) : Fin k := shift i (k - 1)

@[simp] theorem shift_prev {k : Nat} (i : Fin k) : shift (prev i) 1 = i := by
  have hk : 0 < k := by have := i.isLt; omega
  unfold prev
  rw [shift_add, show k - 1 + 1 = k by omega, shift_period]

@[simp] theorem prev_shift {k : Nat} (i : Fin k) : prev (shift i 1) = i := by
  have hk : 0 < k := by have := i.isLt; omega
  unfold prev
  rw [shift_add, show 1 + (k - 1) = k by omega, shift_period]

/-- Distinct offsets separated by less than one period have distinct images. -/
theorem shift_ne_of_lt_gap {k a b : Nat} (i : Fin k)
    (ordered : a < b) (gap : b < a + k) : shift i a ≠ shift i b := by
  intro same
  have sum : a + (b - a) = b := by omega
  apply shift_ne_self (shift i a) (d := b - a) (by omega) (by omega)
  rw [shift_add,sum]
  exact same.symm

/-- Two equally spaced ordered pairs cannot contain one another with
reversed order when twice their spacing is less than the period. -/
theorem pair_subset_same {k d : Nat} (i j : Fin k)
    (positive : 0 < d) (small : 2 * d < k)
    (first : i = j ∨ i = shift j d)
    (second : shift i d = j ∨ shift i d = shift j d) : i = j := by
  rcases first with same | swapped
  · exact same
  · rcases second with back | aligned
    · have loop : shift j (d + d) = j := by
        rw [← shift_add, ← swapped]
        exact back
      exact False.elim (shift_ne_self j (d := d + d) (by omega) (by omega) loop)
    · exact shift_injective aligned

/-- Pairs with distinct positive spacings cannot contain one another
when the sum of the spacings is less than the period. -/
theorem pair_subset_mixed {k d e : Nat} (i j : Fin k)
    (hd : 0 < d) (he : 0 < e) (different : d ≠ e) (small : d + e < k)
    (first : i = j ∨ i = shift j e)
    (second : shift i d = j ∨ shift i d = shift j e) : False := by
  rcases first with same | swapped
  · subst i
    rcases second with loop | aligned
    · exact shift_ne_self j hd (by omega) loop
    · have offsets := (shift_eq_iff j d e).mp aligned
      rw [Nat.mod_eq_of_lt (show d < k by omega),
        Nat.mod_eq_of_lt (show e < k by omega)] at offsets
      exact different offsets
  · rcases second with back | aligned
    · have loop : shift j (e + d) = j := by
        rw [← shift_add, ← swapped]
        exact back
      exact shift_ne_self j (d := e + d) (by omega) (by omega) loop
    · exact shift_ne_self i hd (by omega) (aligned.trans swapped.symm)

#print axioms shift_injective
#print axioms shift_eq_iff
#print axioms shift_ne_of_lt_gap
#print axioms pair_subset_same
#print axioms pair_subset_mixed
end Delivery.CyclicArithmetic
