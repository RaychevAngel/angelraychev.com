import CyclicArithmetic

/-! Geometry of a bounded window on a cyclic column set. These lemmas supply
the ordinary modular-arithmetic premises of a local-arena projection; they
do not assert a graph simulation or certify any local strategy. -/
namespace Delivery.CyclicWindow
open CyclicArithmetic

def Inside {k : Nat} (base : Fin k) (w : Nat) (x : Fin k) : Prop :=
  ∃ u : Nat, u ≤ w ∧ shift base u = x

theorem inside_unique {k w u v : Nat} (base : Fin k)
    (hu : u ≤ w) (hv : v ≤ w) (small : w < k)
    (same : shift base u = shift base v) : u = v := by
  have h := (shift_eq_iff base u v).mp same
  simpa only [Nat.mod_eq_of_lt (show u < k by omega),
    Nat.mod_eq_of_lt (show v < k by omega)] using h

theorem forward_internal {k w J u v d : Nat} (base : Fin k)
    (hu : u ≤ w) (hv : v ≤ w) (hd : d ≤ J) (small : w + J < k)
    (move : shift (shift base u) d = shift base v) : u + d = v := by
  rw [shift_add] at move
  have h := (shift_eq_iff base (u + d) v).mp move
  simpa only [Nat.mod_eq_of_lt (show u + d < k by omega),
    Nat.mod_eq_of_lt (show v < k by omega)] using h

theorem backward_internal {k w J u v d : Nat} (base : Fin k)
    (hu : u ≤ w) (hv : v ≤ w) (hd : d ≤ J) (small : w + J < k)
    (move : shift base u = shift (shift base v) d) : u = v + d :=
  (forward_internal base hv hu hd small move.symm).symm

theorem outside_forward_entry {k w v d : Nat} (base c : Fin k)
    (outside : ¬ Inside base w c) (hv : v ≤ w)
    (move : shift c d = shift base v) : v < d := by
  by_cases h : v < d
  · exact h
  · have sum : v - d + d = v := by omega
    have same : shift (shift base (v - d)) d = shift c d := by
      rw [shift_add, sum, move]
    exact False.elim (outside ⟨v - d, by omega, shift_injective same⟩)

theorem outside_backward_entry {k w v d : Nat} (base c : Fin k)
    (outside : ¬ Inside base w c)
    (move : c = shift (shift base v) d) : w < v + d := by
  by_cases h : w < v + d
  · exact h
  · apply False.elim
    apply outside
    refine ⟨v + d, by omega, ?_⟩
    rw [← shift_add]
    exact move.symm

/-- A displacement of at most `J` columns in either direction, including
waiting. This is only a geometric envelope of a graph's legal moves. -/
def ShortMove {k : Nat} (J : Nat) (c c' : Fin k) : Prop :=
  ∃ d : Nat, d ≤ J ∧ (c' = shift c d ∨ c = shift c' d)

theorem outside_entries {k w J v : Nat} (base c : Fin k)
    (outside : ¬ Inside base w c) (hv : v ≤ w)
    (move : ShortMove J c (shift base v)) : v < J ∨ w < v + J := by
  rcases move with ⟨d, hd, forward | backward⟩
  · have h := outside_forward_entry base c outside hv forward.symm
    exact Or.inl (by omega)
  · have h := outside_backward_entry base c outside backward
    exact Or.inr (by omega)

theorem internal_short {k w J u v : Nat} (base : Fin k)
    (hu : u ≤ w) (hv : v ≤ w) (small : w + J < k)
    (move : ShortMove J (shift base u) (shift base v)) :
    ∃ d : Nat, d ≤ J ∧ (v = u + d ∨ u = v + d) := by
  rcases move with ⟨d, hd, forward | backward⟩
  · exact ⟨d, hd, Or.inl (forward_internal base hu hv hd small forward.symm).symm⟩
  · exact ⟨d, hd, Or.inr (backward_internal base hu hv hd small backward)⟩

/-- For radius six and jump bound two, outside cop entries lie in the
four boundary columns: offsets `0,1,11,12`, or columns `-6,-5,5,6`. -/
theorem radius_six_entries {k v : Nat} (base c : Fin k)
    (outside : ¬ Inside base 12 c) (hv : v ≤ 12)
    (move : ShortMove 2 c (shift base v)) :
    v = 0 ∨ v = 1 ∨ v = 11 ∨ v = 12 := by
  have h := outside_entries base c outside hv move
  omega

#print axioms internal_short
#print axioms radius_six_entries
end Delivery.CyclicWindow
