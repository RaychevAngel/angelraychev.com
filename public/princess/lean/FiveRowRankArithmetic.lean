import Std

/-! Pure arithmetic potential for the five-row, three-probe lower argument.
The geometric hypotheses in Transition are NOT discharged by this module;
research/five-row-investigation.md supplies an ordinary symbolic-certificate
argument. This file must not be advertised as a full five-row formalization. -/
namespace Princess.FiveRowRankArithmetic

def value (h b z : Nat) : Nat :=
  if b = 0 then 0 else if b ≤ 2 then 1 else if b ≤ 5 then b - 2
  else min (2*b+z-8) (b+h-10)

def Valid (h b z : Nat) : Prop :=
  b ≤ h ∧ (b = 0 ∨ 2 ≤ b) ∧ z ≤ 1 ∧ (z = 1 → 6 ≤ b ∧ b ≤ h-3)

def Transition (h b z p b' z' : Nat) : Prop :=
  (b ≤ p ∧ b' = 0 ∧ z' = 0) ∨
  (p = 0 ∧ b = h ∧ b' = h ∧ z' = 0) ∨
  (1 ≤ b-p ∧ (b-p = 1 ∨ b-p = h-2 ∨ b-p = h-1) ∧
    b' = b-p+1 ∧ z' = 0) ∨
  (1 ≤ b-p ∧ b-p+2 ≤ h ∧ b' = b-p+2 ∧
    z' = (if 4 ≤ b-p ∧ b-p ≤ h-5 then 1 else 0) ∧
    ¬ (z = 1 ∧ 3 ≤ b-p ∧ b-p ≤ h-5)) ∨
  (1 ≤ b-p ∧ b-p+3 ≤ b' ∧ z' = 0)

set_option maxHeartbeats 2000000 in
theorem potential_step (h b z p b' z' : Nat) (hh : 15 ≤ h)
    (valid : Valid h b z) (hp : p ≤ 3) (trans : Transition h b z p b' z') :
    value h b z ≤ value h b' z' + if 2 ≤ p then 1 else 0 := by
  obtain ⟨bh, bsmall, zsmall, marked⟩ := valid
  rcases trans with ⟨hc, hb, hz⟩ | ⟨hc, hb, hnext, hz⟩ |
    ⟨hr, hcase, hb, hz⟩ | ⟨hr, hcap, hb, hz, hguard⟩ | ⟨hr, hb, hz⟩
  all_goals try (split at hz)
  all_goals
    simp only [value, Nat.min_def]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> omega

theorem value_initial (h : Nat) (hh : 15 ≤ h) : value h h 0 = 2*h-10 := by
  simp only [value, Nat.min_def]
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem value_zero (h : Nat) : value h 0 0 = 0 := by simp [value]

end Princess.FiveRowRankArithmetic
#print axioms Princess.FiveRowRankArithmetic.potential_step
#print axioms Princess.FiveRowRankArithmetic.value_initial
