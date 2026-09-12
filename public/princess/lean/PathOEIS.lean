import Std

/-!
Arithmetic comparison with Kamenetsky's 2018 path conjectures.
This verifies equivalence of formulas, NOT the room-game path theorem.
Sources: OEIS A301337 (19 March 2018), A301426 (21 March 2018).
-/

namespace Princess.PathOEIS

def twoProbeFormula (n : Nat) : Nat :=
  (2 * n - 2) / 3 + if n % 3 = 0 ∧ n % 2 = 1 then 1 else 0

def threeProbeFormula (n : Nat) : Nat :=
  (2 * n) / 5 + if n % 5 = 4 then 1 else 0

def conjecture2018Two (n : Nat) : Nat :=
  if n % 6 = 0 then n / 6 * 4 - 1
  else if n % 6 = 1 ∨ n % 6 = 2 then n / 6 * 4
  else n / 6 * 4 + 2

def conjecture2018Three (n : Nat) : Nat :=
  if n % 5 = 3 then (n - 3) / 5 * 2 + 1
  else (n - 4) / 5 * 2 + 2

theorem two_probe_equivalence (n : Nat) (hn : 3 ≤ n) :
    twoProbeFormula n = conjecture2018Two n := by
  unfold twoProbeFormula conjecture2018Two
  by_cases h3 : n % 3 = 0
  · by_cases h2 : n % 2 = 1
    · simp only [h3, h2, and_self, if_true]
      all_goals repeat first | split | omega
    · simp only [h2, and_false, if_false]
      all_goals repeat first | split | omega
  · simp only [h3, false_and, if_false]
    all_goals repeat first | split | omega
    have hr : n % 6 = 4 ∨ n % 6 = 5 := by omega
    rcases hr with hr | hr <;> omega

theorem three_probe_equivalence (n : Nat) (hn : 3 ≤ n) :
    threeProbeFormula n = conjecture2018Three n := by
  by_cases hsmall : n = 3
  · subst n
    decide
  have hn4 : 4 ≤ n := by omega
  have hr : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hr with hr | hr | hr | hr | hr
  all_goals simp [threeProbeFormula, conjecture2018Three, hr]
  all_goals omega

/-- The literal `m=2` specialization of PathUpperArithmetic.correctedCeiling.
The condition `n≥3` is its nontrivial-board hypothesis `m<n`. -/
theorem two_probe_corrected_ceiling (n : Nat) (hn : 3 ≤ n) :
    ((2 * n - 4 + 3 - 1) / 3 +
      if (n - 2 - 1) % 3 = 0 ∧ ¬ (n % 2 = 0 ∧ 2 % 2 = 0)
      then 1 else 0) = twoProbeFormula n := by
  unfold twoProbeFormula
  have hnum : 2 * n - 4 + 3 - 1 = 2 * n - 2 := by omega
  rw [hnum]
  have hcond : ((n - 2 - 1) % 3 = 0 ∧ ¬ (n % 2 = 0 ∧ 2 % 2 = 0)) ↔
      (n % 3 = 0 ∧ n % 2 = 1) := by omega
  split <;> split <;> omega

/-- The literal `m=3` specialization, on the required domain `n>3`. -/
theorem three_probe_corrected_ceiling (n : Nat) (hn : 4 ≤ n) :
    ((2 * n - 4 + 5 - 1) / 5 +
      if (n - 3 - 1) % 5 = 0 ∧ ¬ (n % 2 = 0 ∧ 3 % 2 = 0)
      then 1 else 0) = threeProbeFormula n := by
  unfold threeProbeFormula
  have hnum : 2 * n - 4 + 5 - 1 = 2 * n := by omega
  rw [hnum]
  have hcond : ((n - 3 - 1) % 5 = 0 ∧ ¬ (n % 2 = 0 ∧ 3 % 2 = 0)) ↔
      n % 5 = 4 := by omega
  split <;> split <;> omega

end Princess.PathOEIS

#print axioms Princess.PathOEIS.two_probe_equivalence
#print axioms Princess.PathOEIS.three_probe_equivalence
#print axioms Princess.PathOEIS.two_probe_corrected_ceiling
#print axioms Princess.PathOEIS.three_probe_corrected_ceiling
