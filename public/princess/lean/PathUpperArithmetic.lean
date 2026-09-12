import Std

/-!
Arithmetic portion of the reconstructed path upper bound.

These theorems normalize the sweep's quotient/remainder turn count. They do
not assert that any probe schedule catches a target: the graph-theoretic
sweep invariant must still be formalized and connected to BeliefSemantics.
Only Std is imported. There are no admitted theorems or added axioms.
-/

namespace Princess.PathUpperArithmetic

def ceilDiv (a d : Nat) : Nat := (a + d - 1) / d

def bothEven (n m : Nat) : Prop := n % 2 = 0 ∧ m % 2 = 0

instance (n m : Nat) : Decidable (bothEven n m) := inferInstanceAs (Decidable (_ ∧ _))

/-- The base ceiling has only two possibilities in a positive residue block. -/
theorem residue_base_ceiling (m d r : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ceilDiv (2 * r) d = if r ≤ m - 1 then 1 else 2 := by
  unfold ceilDiv
  split
  · apply Nat.div_eq_of_lt_le <;> omega
  · apply Nat.div_eq_of_lt_le <;> omega

/-- Number of remaining sweep blocks after a shared turn on an even path. -/
theorem even_transition_ceiling (m d r : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d - 2) :
    ceilDiv (r + 2 * (r / 2 + 1)) d =
      if r ≤ m - 2 ∨ (r = m - 1 ∧ m % 2 = 0) then 1 else 2 := by
  unfold ceilDiv
  split
  · apply Nat.div_eq_of_lt_le <;> omega
  · apply Nat.div_eq_of_lt_le <;> omega

/-- Both odd-path transition parity cases simplify to this same ceiling. -/
theorem odd_transition_ceiling (m d r : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d - 2) :
    ceilDiv (2 * r + 2) d = if r ≤ m - 2 then 1 else 2 := by
  unfold ceilDiv
  split
  · apply Nat.div_eq_of_lt_le <;> omega
  · apply Nat.div_eq_of_lt_le <;> omega

/-- Add back the completed pairs of sweep rounds. -/
theorem base_ceiling_blocks (n m d q r : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : n = q * d + r + 2) :
    ceilDiv (2 * n - 4) d = 2 * q + (if r ≤ m - 1 then 1 else 2) := by
  have hdpos : 0 < d := by omega
  have hnum : 2 * n - 4 + d - 1 = (2 * r + d - 1) + (2 * q) * d := by
    rw [Nat.mul_assoc]
    omega
  unfold ceilDiv
  rw [hnum, Nat.add_mul_div_right _ _ hdpos]
  have hbase := residue_base_ceiling m d r hm hd hr hrd
  unfold ceilDiv at hbase
  rw [hbase]
  omega

/-- In positive residue coordinates, the exceptional congruence is r=m-1. -/
theorem exceptional_residue (n m d q r : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : n = q * d + r + 2) (hnm : m < n) :
    (n - m - 1) % d = 0 ↔ r = m - 1 := by
  have hdpos : 0 < d := by omega
  by_cases hge : m - 1 ≤ r
  · have hnum : n - m - 1 = q * d + (r + 1 - m) := by omega
    have hlt : r + 1 - m < d := by omega
    rw [hnum, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_eq_of_lt hlt]
    simp only [Nat.mod_eq_of_lt hlt]
    omega
  · cases q with
    | zero => simp only [Nat.zero_mul, Nat.zero_add] at hn; omega
    | succ q =>
      have hn' : n = q * d + d + r + 2 := by
        simpa [Nat.succ_mul] using hn
      have hnum : n - m - 1 = q * d + (r + d + 1 - m) := by omega
      have hlt : r + d + 1 - m < d := by omega
      rw [hnum, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
        Nat.mod_eq_of_lt hlt]
      simp only [Nat.mod_eq_of_lt hlt]
      omega

/-- The strategy's case count in terms of q=e-1 and the positive residue. -/
def sweepCount (n m q r : Nat) : Nat :=
  if r ≤ m - 2 ∨ (r = m - 1 ∧ bothEven n m) then 2 * q + 1 else 2 * q + 2

/-- The historical ceiling formula, with its exceptional correction. -/
def correctedCeiling (n m : Nat) : Nat :=
  ceilDiv (2 * n - 4) (2 * m - 1) +
    if (n - m - 1) % (2 * m - 1) = 0 ∧ ¬ bothEven n m then 1 else 0

/-- Exact agreement of the sweep count with the stated formula (arithmetic only). -/
theorem sweepCount_eq_correctedCeiling (n m d q r : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : n = q * d + r + 2) (hnm : m < n) :
    sweepCount n m q r = correctedCeiling n m := by
  have hd' : 2 * m - 1 = d := by omega
  have hbase := base_ceiling_blocks n m d q r hm hd hr hrd hn
  have hex := exceptional_residue n m d q r hm hd hr hrd hn hnm
  unfold sweepCount correctedCeiling
  rw [hd', hbase]
  simp only [hex]
  by_cases he : bothEven n m
  · simp [he]
    split <;> split <;> omega
  · simp [he]
    split <;> split <;> split <;> omega

/-- Canonical positive remainder coordinates exist for every nontrivial board. -/
theorem canonical_parameters (n m : Nat) (hm : 2 ≤ m) (hnm : m < n) :
    let d := 2 * m - 1
    let q := (n - 3) / d
    let r := (n - 3) % d + 1
    1 ≤ r ∧ r ≤ d ∧ n = q * d + r + 2 := by
  dsimp
  have hd : 0 < 2 * m - 1 := by omega
  have hmod := Nat.mod_lt (n - 3) hd
  have hdiv := Nat.div_add_mod (n - 3) (2 * m - 1)
  rw [Nat.mul_comm] at hdiv
  omega

/-- No auxiliary quotient or residue hypotheses are needed in this final identity. -/
theorem canonical_sweepCount_eq_correctedCeiling (n m : Nat)
    (hm : 2 ≤ m) (hnm : m < n) :
    sweepCount n m ((n - 3) / (2 * m - 1)) ((n - 3) % (2 * m - 1) + 1) =
      correctedCeiling n m := by
  obtain ⟨hr, hrd, hn⟩ := canonical_parameters n m hm hnm
  apply sweepCount_eq_correctedCeiling n m (2 * m - 1)
    ((n - 3) / (2 * m - 1)) ((n - 3) % (2 * m - 1) + 1) hm
  · omega
  · exact hr
  · exact hrd
  · exact hn
  · exact hnm

/-- The same sweep case count reduces to 2n-4 for one probe (n>=3). -/
theorem single_probe_sweepCount (n : Nat) (hn : 3 ≤ n) :
    sweepCount n 1 (n - 3) 1 = 2 * n - 4 := by
  simp [sweepCount]
  omega

#print axioms canonical_sweepCount_eq_correctedCeiling
#print axioms single_probe_sweepCount

#print axioms sweepCount_eq_correctedCeiling
#print axioms even_transition_ceiling
#print axioms odd_transition_ceiling

end Princess.PathUpperArithmetic
