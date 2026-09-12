import PathUpperArithmetic

/-! Pure affine-rank lower bounds for the path game. The potential counts the
minimum ammunition needed by a single cohort under the fixed daily budget.
Physical domination is a separate theorem supplied by PathLowerGeometry.
No axioms or admitted proofs are added. -/

namespace Princess.PathRankLower

def step (cap u p : Nat) : Nat :=
  if u / 2 ≤ p then 0 else min cap (u - 2 * p + 1)

def counter (cap : Nat) (p : Nat → Nat) : Nat → Nat
  | 0 => cap
  | t + 1 => step cap (counter cap p t) (p t)

/-- Minimum-ammunition potential; affine movement costs one rank unit. -/
def ammunition (m u : Nat) : Nat := (u + (u - 3) / (2 * m - 1)) / 2

theorem step_zero (cap p : Nat) : step cap 0 p = 0 := by simp [step]

theorem step_le (cap u p : Nat) : step cap u p ≤ cap := by
  unfold step
  split
  · omega
  · exact Nat.min_le_left _ _

theorem step_mono {cap u v p : Nat} (huv : u ≤ v) :
    step cap u p ≤ step cap v p := by
  unfold step
  split
  · omega
  · split
    · omega
    · simp only [Nat.min_def]
      split <;> split <;> omega

theorem counter_le (cap : Nat) (p : Nat → Nat) (t : Nat) : counter cap p t ≤ cap := by
  cases t with
  | zero => simp [counter]
  | succ t => exact step_le _ _ _

theorem ammunition_zero (m : Nat) : ammunition m 0 = 0 := by simp [ammunition]

theorem ammunition_mono {m u v : Nat} (huv : u ≤ v) :
    ammunition m u ≤ ammunition m v := by
  have hsub : u - 3 ≤ v - 3 := by omega
  have hquot : (u - 3) / (2 * m - 1) ≤ (v - 3) / (2 * m - 1) :=
    Nat.div_le_div_right hsub
  unfold ammunition
  apply Nat.div_le_div_right
  omega

/-- Every actual allocation pays for at most its size in ammunition potential. -/
theorem ammunition_step {cap m u p : Nat}
    (hm : 1 ≤ m) (hu : u ≤ cap) (hp : p ≤ m) :
    ammunition m u ≤ p + ammunition m (step cap u p) := by
  have hd : 0 < 2 * m - 1 := by omega
  by_cases hdone : u / 2 ≤ p
  · have hsmall : u - 3 < 2 * m - 1 := by omega
    have hquot : (u - 3) / (2 * m - 1) = 0 := Nat.div_eq_of_lt hsmall
    rw [show step cap u p = 0 by simp [step, hdone], ammunition_zero]
    simp only [ammunition, hquot, Nat.add_zero]
    exact hdone
  · by_cases hp0 : p = 0
    · subst p
      have hstate : u ≤ step cap u 0 := by
        simp only [step, hdone, if_false]
        exact Nat.le_min.mpr ⟨hu, by omega⟩
      simpa using ammunition_mono (m := m) hstate
    · have hp1 : 1 ≤ p := by omega
      have hs : u - 2 * p + 1 ≤ cap := by omega
      have hstep : step cap u p = u - 2 * p + 1 := by
        simp only [step, hdone, if_false, Nat.min_eq_right hs]
      have hnum : u - 3 ≤ (u - 2 * p + 1 - 3) + (2 * m - 1) := by omega
      have hquot := Nat.div_le_div_right (c := 2 * m - 1) hnum
      rw [Nat.add_div_right _ hd] at hquot
      rw [hstep]
      unfold ammunition
      omega

/-- Potential lower bound for every shared-budget two-counter schedule. -/
theorem ammunition_schedule (cap m : Nat) (p q : Nat → Nat)
    (hm : 1 ≤ m) (budget : ∀ t, p t + q t ≤ m) (t : Nat) :
    2 * ammunition m cap ≤ ammunition m (counter cap p t) +
      ammunition m (counter cap q t) + t * m := by
  induction t with
  | zero => simp [counter]; omega
  | succ t ih =>
      have hbudget := budget t
      have hl := ammunition_step hm (counter_le cap p t) (show p t ≤ m by omega)
      have hr := ammunition_step hm (counter_le cap q t) (show q t ≤ m by omega)
      change 2 * ammunition m cap ≤
        ammunition m (step cap (counter cap p t) (p t)) +
        ammunition m (step cap (counter cap q t) (q t)) + (t + 1) * m
      rw [Nat.succ_mul t m]
      omega

theorem captured_ammunition (cap m : Nat) (p q : Nat → Nat)
    (hm : 1 ≤ m) (budget : ∀ t, p t + q t ≤ m) (t : Nat)
    (left : counter cap p t = 0) (right : counter cap q t = 0) :
    2 * ammunition m cap ≤ t * m := by
  have h := ammunition_schedule cap m p q hm budget t
  simp only [left, right, ammunition_zero, Nat.zero_add] at h
  exact h

/-- Positive remainder coordinates make the potential an elementary integer. -/
theorem ammunition_residue (n m d q r : Nat) (hm : 1 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : n = q * d + r + 2) :
    ammunition m n = q * m + (r + 2) / 2 := by
  have hdpos : 0 < d := by omega
  have hD : 2 * m - 1 = d := by omega
  have hnum : n - 3 = (r - 1) + q * d := by omega
  have hquot : (n - 3) / d = q := by
    rw [hnum, Nat.add_mul_div_right _ _ hdpos, Nat.div_eq_of_lt (show r - 1 < d by omega)]
    omega
  have hprod : q * d + q = 2 * (q * m) := by
    have h := congrArg (fun x => q * x) hd
    simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm q 2 m] using h
  have hsum : n + q = (r + 2) + (q * m) * 2 := by omega
  unfold ammunition
  rw [hD, hquot, hsum, Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
  omega

/-- The residue lower count for the constant-capacity rank game. -/
def lowerCount (m q r : Nat) : Nat :=
  if r ≤ m - 2 ∨ (r = m - 1 ∧ m % 2 = 0) then 2 * q + 1 else 2 * q + 2

theorem residue_lower (n m d q r t : Nat) (hm : 2 ≤ m)
    (hd : d + 1 = 2 * m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : n = q * d + r + 2)
    (hcap : 2 * ammunition m n ≤ t * m) : lowerCount m q r ≤ t := by
  rw [ammunition_residue n m d q r (by omega) hd hr hrd hn] at hcap
  have hmpos : 0 < m := by omega
  have hbase : 2 * q + 1 ≤ t := by
    by_cases h : 2 * q + 1 ≤ t
    · exact h
    have ht : t ≤ 2 * q := by omega
    have hmul := Nat.mul_le_mul_right m ht
    have heq : (2 * q) * m = 2 * (q * m) := Nat.mul_assoc 2 q m
    rw [heq] at hmul
    omega
  unfold lowerCount
  split
  · exact hbase
  · rename_i hcase
    by_cases h : 2 * q + 2 ≤ t
    · exact h
    have ht : t = 2 * q + 1 := by omega
    have heq : (2 * q + 1) * m = 2 * (q * m) + m := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    rw [ht, heq] at hcap
    omega

/-- Even-path arithmetic: this lower count is the prepared upper formula. -/
theorem lowerCount_eq_sweepCount (n m q r : Nat) (heven : n % 2 = 0) :
    lowerCount m q r = PathUpperArithmetic.sweepCount n m q r := by
  simp only [lowerCount, PathUpperArithmetic.sweepCount,
    PathUpperArithmetic.bothEven, heven, true_and]


/-- Cardinality/rank comparison along any physical process with this lower transition. -/
theorem counter_dominated (cap : Nat) (p b : Nat → Nat)
    (initial : cap ≤ b 0)
    (transition : ∀ t, step cap (b t) (p t) ≤ b (t + 1)) (t : Nat) :
    counter cap p t ≤ b t := by
  induction t with
  | zero => exact initial
  | succ t ih => exact Nat.le_trans (step_mono ih) (transition t)

theorem captured_positive (cap : Nat) (p : Nat → Nat) (t : Nat)
    (hcap : 1 ≤ cap) (captured : counter cap p t = 0) : 1 ≤ t := by
  cases t with
  | zero => simp only [counter] at captured; omega
  | succ t => omega

theorem captured_one_probe (n : Nat) (p q : Nat → Nat) (t : Nat)
    (hn : 3 ≤ n) (budget : ∀ t, p t + q t ≤ 1)
    (left : counter n p t = 0) (right : counter n q t = 0) :
    2 * n - 4 ≤ t := by
  have h := captured_ammunition n 1 p q (by decide) budget t left right
  have heq : ammunition 1 n = n - 2 := by
    simp only [ammunition, Nat.mul_one, Nat.reduceSub, Nat.div_one]
    omega
  rw [heq] at h
  omega

theorem captured_single_edge (p q : Nat → Nat) (t : Nat)
    (budget : ∀ t, p t + q t ≤ 1)
    (left : counter 2 p t = 0) (right : counter 2 q t = 0) : 2 ≤ t := by
  have h := captured_ammunition 2 1 p q (by decide) budget t left right
  have heq : ammunition 1 2 = 1 := by decide
  rw [heq] at h
  omega

/-- Exact prepared formula as a lower bound for every even-path rank schedule. -/
theorem captured_even_formula (n m : Nat) (p q : Nat → Nat) (t : Nat)
    (hm : 2 ≤ m) (hnm : m < n) (heven : n % 2 = 0)
    (budget : ∀ t, p t + q t ≤ m)
    (left : counter n p t = 0) (right : counter n q t = 0) :
    PathUpperArithmetic.correctedCeiling n m ≤ t := by
  obtain ⟨hr, hrd, hn⟩ := PathUpperArithmetic.canonical_parameters n m hm hnm
  have hc := captured_ammunition n m p q (by omega) budget t left right
  have hl := residue_lower n m (2 * m - 1)
    ((n - 3) / (2 * m - 1)) ((n - 3) % (2 * m - 1) + 1) t
    hm (by omega) hr hrd hn hc
  rw [lowerCount_eq_sweepCount n m _ _ heven,
    PathUpperArithmetic.canonical_sweepCount_eq_correctedCeiling n m hm hnm] at hl
  exact hl

end Princess.PathRankLower

#print axioms Princess.PathRankLower.ammunition_step
#print axioms Princess.PathRankLower.captured_ammunition
#print axioms Princess.PathRankLower.residue_lower

#print axioms Princess.PathRankLower.captured_even_formula
#print axioms Princess.PathRankLower.captured_one_probe
