import Std

/-! Pure arithmetic for five rows, odd length, and three probes per round.
The exact arbitrary-support neighborhood bounds and compatible prefix orders
are ordinary theorems in research/odd-rectangle-isoperimetry.md. They are NOT
formalized by this module; this is not a full five-row Lean formalization. -/
namespace Princess.FiveRowOddRankArithmetic

/-- z=0 is the larger parity class, z=1 the smaller parity class. -/
def profile (h r z : Nat) : Nat :=
  if r = 0 then 0 else
  if z = 0 then
    if h ≤ r then h else r + if r = 1 ∨ h-3 ≤ r then 1 else 2
  else r + if r = h then 1 else if r ≤ 2 ∨ h-2 ≤ r then 2 else 3

def value (h b z : Nat) : Nat :=
  if b = 0 then 0 else if b ≤ 2 then 1 else if b ≤ 5 then b - 2
  else min (2*b+z-8) (b+h+z-10)

def Valid (h b z : Nat) : Prop :=
  z ≤ 1 ∧ b ≤ h+1-z ∧ (b = 0 ∨ 3-z ≤ b)

set_option maxHeartbeats 4000000 in
theorem potential_step (h b z p : Nat) (hh : 12 ≤ h)
    (valid : Valid h b z) (hp : p ≤ 3) :
    value h b z ≤ value h (profile h (b-p) z) (1-z) +
      if 2 ≤ p then 1 else 0 := by
  obtain ⟨hz, hb, hsmall⟩ := valid
  have zcases : z = 0 ∨ z = 1 := by omega
  rcases zcases with rfl | rfl
  all_goals
    simp only [profile, Nat.reduceEqDiff, if_true, if_false]
    split <;> (try split) <;> (try split) <;> (try split)
    all_goals
      simp only [value, Nat.min_def]
      split <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> (try split) <;> omega

set_option maxHeartbeats 1000000 in
theorem value_monotone (h a b z : Nat) (hh : 12 ≤ h)
    (hz : z ≤ 1) (hab : a ≤ b) : value h a z ≤ value h b z := by
  simp only [value, Nat.min_def]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem value_initial_large (h : Nat) (hh : 12 ≤ h) :
    value h (h+1) 0 = 2*h-9 := by
  simp only [value, Nat.min_def]
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem value_initial_small (h : Nat) (hh : 12 ≤ h) :
    value h h 1 = 2*h-9 := by
  simp only [value, Nat.min_def]
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem value_zero (h z : Nat) : value h 0 z = 0 := by simp [value]

end Princess.FiveRowOddRankArithmetic
#print axioms Princess.FiveRowOddRankArithmetic.potential_step
#print axioms Princess.FiveRowOddRankArithmetic.value_monotone
