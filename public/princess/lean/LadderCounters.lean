import Std

/-!
Exact two-counter optimum for the two-row princess graph.

This file proves lower bounds, the equality obstruction, attaining schedules,
and the full quotient/remainder optimum, including its ceiling-form identity.
LadderGeometry and LadderCardinality prove the actual graph and finite-count
bridges. LadderGame assembles these results into the complete classification
for arbitrary physical-room probe sequences and actual avoiding trajectories.
-/

namespace Princess.Ladder

/-- The next suffix length after `p` probes in a path of `n` columns. -/
def next (n b p : Nat) : Nat :=
  if b ≤ p then 0 else min n (b - p + 1)

/-- A cohort of length zero or one carries zero weight. -/
def weight (b : Nat) : Nat := b - 1

theorem next_zero (n p : Nat) : next n 0 p = 0 := by
  simp [next]

theorem next_le (n b p : Nat) : next n b p ≤ n := by
  unfold next
  split
  · omega
  · exact Nat.min_le_left _ _

theorem next_mono {n b c p : Nat} (h : b ≤ c) :
    next n b p ≤ next n c p := by
  unfold next
  split
  · omega
  · split
    · omega
    · simp only [Nat.min_def]
      split <;> split <;> omega

theorem weight_mono {b c : Nat} (h : b ≤ c) : weight b ≤ weight c := by
  unfold weight
  omega

/-- An unprobed bounded cohort cannot shrink. -/
theorem next_no_probes {n b : Nat} (hb : b ≤ n) : b ≤ next n b 0 := by
  unfold next
  split
  · omega
  · exact Nat.le_min.mpr ⟨hb, by omega⟩

/-- One cohort can lose at most `p-1` units of weight under positive probing. -/
theorem weight_probe {n b p : Nat} (hb : b ≤ n) (hp : 1 ≤ p) :
    weight b ≤ weight (next n b p) + p - 1 := by
  unfold next weight
  split
  · omega
  · simp only [Nat.min_def]
    split <;> omega

/-- A weaker estimate valid even when no probe is allocated. -/
theorem weight_probe_weak {n b p : Nat} (hb : b ≤ n) :
    weight b ≤ weight (next n b p) + p := by
  by_cases hp : p = 0
  · subst p
    simpa using weight_mono (next_no_probes hb)
  · have := weight_probe hb (show 1 ≤ p by omega)
    omega

/-- The combined weight decreases by at most `m-1` in one valid round. -/
theorem weight_round {n b c p q m : Nat}
    (hb : b ≤ n) (hc : c ≤ n) (hm : 2 ≤ m) (hbudget : p + q ≤ m) :
    weight b + weight c ≤
      weight (next n b p) + weight (next n c q) + (m - 1) := by
  by_cases hp : p = 0
  · subst p
    have hleft := weight_mono (next_no_probes hb)
    by_cases hq : q = 0
    · subst q
      have hright := weight_mono (next_no_probes hc)
      omega
    · have hright := weight_probe hc (show 1 ≤ q by omega)
      omega
  · have hleft := weight_probe hb (show 1 ≤ p by omega)
    have hright := weight_probe_weak (p := q) hc
    omega

/-- One suffix-length counter driven by a daily probe allocation. -/
def counter (n : Nat) (p : Nat → Nat) : Nat → Nat
  | 0 => n
  | t + 1 => next n (counter n p t) (p t)

theorem counter_le (n : Nat) (p : Nat → Nat) (t : Nat) :
    counter n p t ≤ n := by
  cases t with
  | zero => simp [counter]
  | succ t => exact next_le n (counter n p t) (p t)

/-- Suffix counters are dominated by any cardinality process satisfying the
one-cohort neighborhood lower bound. The room-graph premise is explicit. -/
theorem counter_dominated (n : Nat) (p b : Nat → Nat)
    (initial : n ≤ b 0)
    (transition : ∀ t, next n (b t) (p t) ≤ b (t + 1)) (t : Nat) :
    counter n p t ≤ b t := by
  induction t with
  | zero => exact initial
  | succ t ih =>
      exact Nat.le_trans (next_mono ih) (transition t)

/-- The accumulated potential bound for every finite valid counter schedule. -/
theorem weight_schedule (n m : Nat) (p q : Nat → Nat)
    (hm : 2 ≤ m) (budget : ∀ t, p t + q t ≤ m) (t : Nat) :
    weight n + weight n ≤
      weight (counter n p t) + weight (counter n q t) + t * (m - 1) := by
  induction t with
  | zero => simp [counter]
  | succ t ih =>
      have hr := weight_round (counter_le n p t) (counter_le n q t) hm (budget t)
      have hmul : (t + 1) * (m - 1) = t * (m - 1) + (m - 1) :=
        Nat.succ_mul t (m - 1)
      change weight n + weight n ≤
        weight (next n (counter n p t) (p t)) +
        weight (next n (counter n q t) (q t)) + (t + 1) * (m - 1)
      omega

/-- A completed two-counter schedule needs at least the indicated capacity.
This is equivalent to the ceiling lower bound when `m≥2`, without division. -/
theorem capture_lower_bound (n m : Nat) (p q : Nat → Nat)
    (hm : 2 ≤ m) (budget : ∀ t, p t + q t ≤ m) (t : Nat)
    (leftCaptured : counter n p t = 0) (rightCaptured : counter n q t = 0) :
    2 * (n - 1) ≤ t * (m - 1) := by
  have h := weight_schedule n m p q hm budget t
  simp only [leftCaptured, rightCaptured, weight] at h
  omega

/-- With at most one probe, a full cohort on a path of at least two columns
remains full. This is the counter-model feasibility obstruction. -/
theorem full_one_probe {n p : Nat} (hn : 2 ≤ n) (hp : p ≤ 1) :
    next n n p = n := by
  unfold next
  split
  · omega
  · simp only [Nat.min_def]
    split <;> omega

theorem one_probe_persists (n : Nat) (p : Nat → Nat)
    (hn : 2 ≤ n) (budget : ∀ t, p t ≤ 1) (t : Nat) :
    counter n p t = n := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change next n (counter n p t) (p t) = n
      rw [ih]
      exact full_one_probe hn (budget t)

theorem one_probe_impossible (n : Nat) (p q : Nat → Nat)
    (hn : 2 ≤ n) (budget : ∀ t, p t + q t ≤ 1) (t : Nat) :
    ¬ (counter n p t = 0 ∧ counter n q t = 0) := by
  have h := one_probe_persists n p hn (fun t => by have := budget t; omega) t
  omega

theorem counter_congr_prefix (n : Nat) (p q : Nat → Nat) (t : Nat)
    (agree : ∀ i, i < t → p i = q i) : counter n p t = counter n q t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have earlier := ih (fun i hi => agree i (by omega))
      simp only [counter, earlier, agree t (by omega)]

theorem counter_stays_zero (n : Nat) (p : Nat → Nat) (k : Nat)
    (captured : counter n p k = 0) (t : Nat) : counter n p (k + t) = 0 := by
  induction t with
  | zero => simpa using captured
  | succ t ih =>
      change next n (counter n p (k + t)) (p (k + t)) = 0
      rw [ih, next_zero]

/-- A suffix of initial length `n≥2` is cleared by `n−1` two-probe rounds. -/
theorem two_probe_sweep (n t : Nat) (hn : 2 ≤ n) :
    counter n (fun _ => 2) t = if n ≤ t + 1 then 0 else n - t := by
  induction t with
  | zero =>
      simp only [counter]
      split <;> omega
  | succ t ih =>
      simp only [counter, ih, next]
      split <;> split
      all_goals try simp only [Nat.min_def]
      all_goals repeat first | split | omega

theorem counter_no_probes (n t : Nat) : counter n (fun _ => 0) t = n := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [counter, ih, next]
      split
      · omega
      · simp only [Nat.min_def]
        split <;> omega

theorem counter_restart (n : Nat) (p : Nat → Nat) (k : Nat)
    (full : counter n p k = n) (t : Nat) :
    counter n p (k + t) = counter n (fun i => p (k + i)) t := by
  induction t with
  | zero => simpa [counter] using full
  | succ t ih =>
      change next n (counter n p (k + t)) (p (k + t)) =
        next n (counter n (fun i => p (k + i)) t) (p (k + t))
      rw [ih]

def leftSweep (n t : Nat) : Nat := if t < n - 1 then 2 else 0

def rightSweep (n t : Nat) : Nat := if t < n - 1 then 0 else 2

theorem sweep_budget (n t : Nat) : leftSweep n t + rightSweep n t = 2 := by
  unfold leftSweep rightSweep
  split <;> omega

theorem left_sweep_captured (n : Nat) (hn : 2 ≤ n) :
    counter n (leftSweep n) (n - 1) = 0 := by
  have agree : counter n (leftSweep n) (n - 1) =
      counter n (fun _ => 2) (n - 1) := by
    apply counter_congr_prefix
    intro i hi
    simp only [leftSweep, if_pos hi]
  rw [agree, two_probe_sweep n (n - 1) hn]
  split <;> omega

theorem right_sweep_initially_full (n : Nat) :
    counter n (rightSweep n) (n - 1) = n := by
  have agree : counter n (rightSweep n) (n - 1) =
      counter n (fun _ => 0) (n - 1) := by
    apply counter_congr_prefix
    intro i hi
    simp only [rightSweep, if_pos hi]
  rw [agree, counter_no_probes]

/-- The explicit sequential sweeps clear both counters in `2(n−1)` rounds. -/
theorem two_probe_upper_bound (n : Nat) (hn : 2 ≤ n) :
    counter n (leftSweep n) (2 * (n - 1)) = 0 ∧
      counter n (rightSweep n) (2 * (n - 1)) = 0 := by
  have duration : 2 * (n - 1) = (n - 1) + (n - 1) := by omega
  rw [duration]
  constructor
  · exact counter_stays_zero n (leftSweep n) (n - 1) (left_sweep_captured n hn) (n - 1)
  · rw [counter_restart n (rightSweep n) (n - 1) (right_sweep_initially_full n)]
    have agree : counter n (fun i => rightSweep n (n - 1 + i)) (n - 1) =
        counter n (fun _ => 2) (n - 1) := by
      apply counter_congr_prefix
      intro i hi
      have outside : ¬ n - 1 + i < n - 1 := by omega
      simp only [rightSweep, if_neg outside]
    rw [agree, two_probe_sweep n (n - 1) hn]
    split <;> omega

/-- The exact optimum for two probes, within the formally defined counter model.
The first conjunct supplies a valid attaining schedule; the second rules out
all shorter schedules. Connecting these counters to room beliefs is separate. -/
theorem two_probe_optimal (n : Nat) (hn : 2 ≤ n) :
    (∃ p q : Nat → Nat, (∀ t, p t + q t ≤ 2) ∧
      counter n p (2 * (n - 1)) = 0 ∧ counter n q (2 * (n - 1)) = 0) ∧
    (∀ p q : Nat → Nat, (∀ t, p t + q t ≤ 2) → ∀ t,
      counter n p t = 0 → counter n q t = 0 → 2 * (n - 1) ≤ t) := by
  constructor
  · refine ⟨leftSweep n, rightSweep n, ?_, two_probe_upper_bound n hn⟩
    intro t
    exact Nat.le_of_eq (sweep_budget n t)
  · intro p q budget t hp hq
    have h := capture_lower_bound n 2 p q (by omega) budget t hp hq
    simpa using h

/-- Equality in the combined potential bound forces one whole decrement onto
one cohort; the other cohort's weight is unchanged. -/
theorem tight_round_weights {n b c p q m : Nat}
    (hb : b ≤ n) (hc : c ≤ n) (hm : 2 ≤ m) (budget : p + q ≤ m)
    (tight : weight b + weight c =
      weight (next n b p) + weight (next n c q) + (m - 1)) :
    (weight b = weight (next n b p) + (m - 1) ∧
      weight c = weight (next n c q)) ∨
    (weight b = weight (next n b p) ∧
      weight c = weight (next n c q) + (m - 1)) := by
  by_cases hp : p = 0
  · have hl := weight_mono (next_no_probes hb)
    by_cases hq : q = 0
    · have hr := weight_mono (next_no_probes hc)
      subst p
      subst q
      omega
    · have hr := weight_probe hc (show 1 ≤ q by omega)
      subst p
      right
      exact ⟨by omega, by omega⟩
  · have hl := weight_probe hb (show 1 ≤ p by omega)
    by_cases hq : q = 0
    · have hr := weight_mono (next_no_probes hc)
      subst q
      left
      exact ⟨by omega, by omega⟩
    · have hr := weight_probe hc (show 1 ≤ q by omega)
      omega

/-- A finite valid counter strategy, with arbitrary initial counter values. -/
inductive Clears (n m : Nat) : Nat → Nat → Nat → Prop
  | done : Clears n m 0 0 0
  | step {b c p q t} : p + q ≤ m →
      Clears n m (next n b p) (next n c q) t → Clears n m b c (t + 1)

theorem clears_weight_bound {n m b c t : Nat} (hm : 2 ≤ m)
    (run : Clears n m b c t) (hb : b ≤ n) (hc : c ≤ n) :
    weight b + weight c ≤ t * (m - 1) := by
  induction run with
  | done => simp [weight]
  | @step b c p q t budget rest ih =>
      have suffix := ih (next_le n b p) (next_le n c q)
      have round := weight_round hb hc hm budget
      rw [Nat.succ_mul]
      omega

/-- If the elementary capacity bound is attained exactly, each cohort's
initial weight is divisible by `m-1`. This is the equality obstruction. -/
theorem tight_clears_divisible {n m b c t : Nat} (hm : 2 ≤ m)
    (run : Clears n m b c t) (hb : b ≤ n) (hc : c ≤ n)
    (tight : weight b + weight c = t * (m - 1)) :
    (m - 1) ∣ weight b ∧ (m - 1) ∣ weight c := by
  induction run with
  | done => simp [weight]
  | @step b c p q t budget rest ih =>
      have suffix := clears_weight_bound hm rest (next_le n b p) (next_le n c q)
      have round := weight_round hb hc hm budget
      rw [Nat.succ_mul] at tight
      have nextTight : weight (next n b p) + weight (next n c q) = t * (m - 1) := by
        omega
      have roundTight : weight b + weight c =
          weight (next n b p) + weight (next n c q) + (m - 1) := by omega
      have divisors := ih (next_le n b p) (next_le n c q) nextTight
      rcases tight_round_weights hb hc hm budget roundTight with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [hl, hr]
        exact ⟨Nat.dvd_add divisors.1 (Nat.dvd_refl _), divisors.2⟩
      · rw [hl, hr]
        exact ⟨divisors.1, Nat.dvd_add divisors.2 (Nat.dvd_refl _)⟩

/-- Any captured tail of a functional counter schedule is a finite `Clears` run. -/
theorem counter_tail_clears (n m : Nat) (p q : Nat → Nat)
    (budget : ∀ t, p t + q t ≤ m) (k t : Nat)
    (leftCaptured : counter n p (k + t) = 0)
    (rightCaptured : counter n q (k + t) = 0) :
    Clears n m (counter n p k) (counter n q k) t := by
  induction t generalizing k with
  | zero =>
      have hp : counter n p k = 0 := by simpa using leftCaptured
      have hq : counter n q k = 0 := by simpa using rightCaptured
      rw [hp, hq]
      exact Clears.done
  | succ t ih =>
      have time : (k + 1) + t = k + (t + 1) := by omega
      have hp : counter n p ((k + 1) + t) = 0 := by rw [time]; exact leftCaptured
      have hq : counter n q ((k + 1) + t) = 0 := by rw [time]; exact rightCaptured
      exact Clears.step (budget k) (ih (k + 1) hp hq)

/-- Attaining the basic lower bound requires divisibility of each cohort's
weight. Together with the ceiling lower bound this gives the extra-turn case. -/
theorem capture_equality_divisible (n m : Nat) (p q : Nat → Nat)
    (hm : 2 ≤ m) (budget : ∀ t, p t + q t ≤ m) (t : Nat)
    (leftCaptured : counter n p t = 0) (rightCaptured : counter n q t = 0)
    (tight : 2 * (n - 1) = t * (m - 1)) : (m - 1) ∣ (n - 1) := by
  have run := counter_tail_clears n m p q budget 0 t
    (by simpa using leftCaptured) (by simpa using rightCaptured)
  have weights : weight n + weight n = t * (m - 1) := by
    unfold weight
    omega
  have h := tight_clears_divisible hm run (by simp [counter]) (by simp [counter]) weights
  exact h.1

/-- If `m-1` does not divide `n-1`, any successful schedule has strictly more
capacity than `2(n-1)`. When the ordinary ceiling is an equality, one extra
round is therefore necessary. -/
theorem capture_strict_when_nondivisible (n m : Nat) (p q : Nat → Nat)
    (hm : 2 ≤ m) (budget : ∀ t, p t + q t ≤ m) (t : Nat)
    (leftCaptured : counter n p t = 0) (rightCaptured : counter n q t = 0)
    (nondivisible : ¬ (m - 1) ∣ (n - 1)) :
    2 * (n - 1) < t * (m - 1) := by
  have lower := capture_lower_bound n m p q hm budget t leftCaptured rightCaptured
  have unequal : 2 * (n - 1) ≠ t * (m - 1) := by
    intro h
    exact nondivisible (capture_equality_divisible n m p q hm budget t leftCaptured rightCaptured h)
  omega

theorem next_eq_zero_iff {n b p : Nat} (hn : 1 ≤ n) :
    next n b p = 0 ↔ b ≤ p := by
  unfold next
  split
  · omega
  · simp only [Nat.min_def]
    split <;> omega

/-- A round starting with two nonempty proper cohorts cannot attain the
per-round potential bound. This supplies the obstruction to switching sweeps. -/
theorem partial_round_strict {n b c p q m : Nat}
    (hb : 0 < b ∧ b < n) (hc : 0 < c ∧ c < n)
    (hm : 2 ≤ m) (budget : p + q ≤ m) :
    weight b + weight c + 1 ≤
      weight (next n b p) + weight (next n c q) + (m - 1) := by
  unfold next weight
  split <;> split
  all_goals try simp only [Nat.min_def]
  all_goals repeat first | omega | split

/-- At an equality round that eliminates the left cohort, the right cohort
must still be full and all probes finish the left cohort. -/
theorem tight_left_elimination {n b c p q m : Nat}
    (hb : 0 < b ∧ b ≤ n) (hc : 0 < c ∧ c ≤ n)
    (hm : 2 ≤ m) (budget : p + q ≤ m)
    (leftGone : next n b p = 0) (rightLives : 0 < next n c q)
    (tight : weight b + weight c =
      weight (next n b p) + weight (next n c q) + (m - 1)) :
    c = n ∧ b = m ∧ p = m ∧ q = 0 := by
  have hn : 1 ≤ n := by omega
  have hbp := (next_eq_zero_iff hn).mp leftGone
  have hcq : ¬ c ≤ q := by
    intro h
    have gone := (next_eq_zero_iff hn).mpr h
    omega
  have rightNext : next n c q = min n (c - q + 1) := by
    simp only [next, if_neg hcq]
  rw [leftGone, rightNext] at tight
  unfold weight at tight
  by_cases hcap : n ≤ c - q + 1
  · rw [Nat.min_eq_left hcap] at tight
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rw [Nat.min_eq_right (show c - q + 1 ≤ n by omega)] at tight
    omega

theorem clears_swap {n m b c t : Nat} (run : Clears n m b c t) :
    Clears n m c b t := by
  induction run with
  | done => exact Clears.done
  | step budget rest ih =>
      exact Clears.step (by omega) ih

theorem next_full_zero (n : Nat) : next n n 0 = n := by
  exact Nat.le_antisymm (next_le n n 0) (next_no_probes (Nat.le_refl n))

/-- A single remaining suffix clears within any positive number of rounds
whose sweep capacity is at least its length minus one. -/
theorem single_left_capacity {n m b t : Nat} (hm : 2 ≤ m) (hb : b ≤ n)
    (ht : 1 ≤ t) (capacity : b ≤ t * (m - 1) + 1) : Clears n m b 0 t := by
  induction t generalizing b with
  | zero => omega
  | succ t ih =>
      cases t with
      | zero =>
          have hbm : b ≤ m := by omega
          have gone : next n b m = 0 := by simp only [next, if_pos hbm]
          apply Clears.step (p := m) (q := 0) (by omega)
          rw [gone, next_zero]
          exact Clears.done
      | succ t =>
          have cap : next n b m ≤ (t + 1) * (m - 1) + 1 := by
            have expand : (t + 1 + 1) * (m - 1) = (t + 1) * (m - 1) + (m - 1) :=
              Nat.succ_mul (t + 1) (m - 1)
            change b ≤ (t + 1 + 1) * (m - 1) + 1 at capacity
            unfold next
            split
            · omega
            · have bound := Nat.min_le_right n (b - m + 1)
              omega
          exact Clears.step (p := m) (q := 0) (by omega)
            (ih (next_le n b m) (by omega) cap)

/-- Prepend full-budget left sweeps while the other cohort is fixed. -/
theorem prepend_left_sweeps (n m a c q t : Nat) (hm : 2 ≤ m) (ha : 2 ≤ a)
    (bound : q * (m - 1) + a ≤ n) (fixed : next n c 0 = c)
    (finish : Clears n m a c t) :
    Clears n m (q * (m - 1) + a) c (q + t) := by
  induction q with
  | zero => simpa using finish
  | succ q ih =>
      have expand : (q + 1) * (m - 1) = q * (m - 1) + (m - 1) :=
        Nat.succ_mul q (m - 1)
      change (q + 1) * (m - 1) + a ≤ n at bound
      have bound' : q * (m - 1) + a ≤ n := by omega
      have stepValue : next n ((q + 1) * (m - 1) + a) m = q * (m - 1) + a := by
        unfold next
        split
        · omega
        · simp only [Nat.min_def]
          split <;> omega
      have duration : (q + 1) + t = (q + t) + 1 := by omega
      rw [duration]
      apply Clears.step (p := m) (q := 0) (by omega)
      rw [stepValue, fixed]
      exact ih bound'

def quotientTurns (q s M : Nat) : Nat :=
  if s = 0 then 2 * q else if 2 * s < M then 2 * q + 1 else 2 * q + 2

/-- The shared-transition construction in quotient/remainder coordinates. -/
theorem quotient_upper {n m q s : Nat} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (decomp : n = q * (m - 1) + s + 1) (hs : s < m - 1) :
    Clears n m n n (quotientTurns q s (m - 1)) := by
  by_cases hzero : s = 0
  · subst s
    cases q with
    | zero => simp at decomp; omega
    | succ q =>
        change n = (q + 1) * (m - 1) + 0 + 1 at decomp
        have expand : (q + 1) * (m - 1) = q * (m - 1) + (m - 1) :=
          Nat.succ_mul q (m - 1)
        have suffix : Clears n m 0 n (q + 1) :=
          clears_swap (single_left_capacity hm (Nat.le_refl n) (by omega) (by omega))
        have finish : Clears n m m n (q + 2) := by
          apply Clears.step (p := m) (q := 0) (by omega)
          have gone : next n m m = 0 := by simp only [next, Nat.le_refl, ↓reduceIte]
          rw [gone, next_full_zero]
          exact suffix
        have begin : q * (m - 1) + m = n := by omega
        have all := prepend_left_sweeps n m m n q (q + 2) hm hm
          (by omega) (next_full_zero n) finish
        rw [begin] at all
        have duration : q + (q + 2) = quotientTurns (q + 1) 0 (m - 1) := by
          simp only [quotientTurns, ↓reduceIte]
          omega
        rw [duration] at all
        exact all
  · by_cases hsmall : 2 * s < m - 1
    · cases q with
      | zero =>
          have first : s + 1 = n := by omega
          have spare : n ≤ m - 1 - s := by omega
          have endLeft : next n n (s + 1) = 0 := by simp [next, first]
          have endRight : next n n (m - 1 - s) = 0 := by simp [next, spare]
          simp only [quotientTurns, if_neg hzero, if_pos hsmall, Nat.mul_zero, Nat.zero_add]
          apply Clears.step (p := s + 1) (q := m - 1 - s) (by omega)
          rw [endLeft, endRight]
          exact Clears.done
      | succ q =>
          change n = (q + 1) * (m - 1) + s + 1 at decomp
          have cap : next n n (m - 1 - s) ≤ (q + 1) * (m - 1) + 1 := by
            unfold next
            split
            · omega
            · have bound := Nat.min_le_right n (n - (m - 1 - s) + 1)
              omega
          have suffix : Clears n m 0 (next n n (m - 1 - s)) (q + 1) :=
            clears_swap (single_left_capacity hm (next_le _ _ _) (by omega) cap)
          have finish : Clears n m (s + 1) n (q + 2) := by
            apply Clears.step (p := s + 1) (q := m - 1 - s) (by omega)
            simpa only [next, Nat.le_refl, ↓reduceIte] using suffix
          have begin : (q + 1) * (m - 1) + (s + 1) = n := by omega
          have all := prepend_left_sweeps n m (s + 1) n (q + 1) (q + 2) hm
            (by omega) (by omega) (next_full_zero n) finish
          rw [begin] at all
          have duration : (q + 1) + (q + 2) = quotientTurns (q + 1) s (m - 1) := by
            simp only [quotientTurns, if_neg hzero, if_pos hsmall]
            omega
          rw [duration] at all
          exact all
    · have expand : (q + 1) * (m - 1) = q * (m - 1) + (m - 1) :=
        Nat.succ_mul q (m - 1)
      have cap : next n n (m - 1 - s) ≤ (q + 1) * (m - 1) + 1 := by
        unfold next
        split
        · omega
        · have bound := Nat.min_le_right n (n - (m - 1 - s) + 1)
          omega
      have suffix : Clears n m 0 (next n n (m - 1 - s)) (q + 1) :=
        clears_swap (single_left_capacity hm (next_le _ _ _) (by omega) cap)
      have finish : Clears n m (s + 1) n (q + 2) := by
        apply Clears.step (p := s + 1) (q := m - 1 - s) (by omega)
        simpa only [next, Nat.le_refl, ↓reduceIte] using suffix
      have begin : q * (m - 1) + (s + 1) = n := by omega
      have all := prepend_left_sweeps n m (s + 1) n q (q + 2) hm
        (by omega) (by omega) (next_full_zero n) finish
      rw [begin] at all
      have duration : q + (q + 2) = quotientTurns q s (m - 1) := by
        simp only [quotientTurns, if_neg hzero, if_neg hsmall]
        omega
      rw [duration] at all
      exact all

/-- The quotient/remainder upper bound is optimal among all finite counter runs. -/
theorem quotient_lower {n m q s t : Nat} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (decomp : n = q * (m - 1) + s + 1) (hs : s < m - 1)
    (run : Clears n m n n t) : quotientTurns q s (m - 1) ≤ t := by
  have bound := clears_weight_bound hm run (Nat.le_refl n) (Nat.le_refl n)
  have lower : 2 * (n - 1) ≤ t * (m - 1) := by unfold weight at bound; omega
  have Mpos : 0 < m - 1 := by omega
  by_cases hzero : s = 0
  · simp only [quotientTurns, if_pos hzero]
    have mulBound : (2 * q) * (m - 1) ≤ t * (m - 1) := by
      rw [Nat.mul_assoc]
      omega
    exact Nat.le_of_mul_le_mul_right mulBound Mpos
  · have modEq : (n - 1) % (m - 1) = s := by
      have hN : n - 1 = q * (m - 1) + s := by omega
      rw [hN, Nat.mul_add_mod_of_lt hs]
    have nondivisible : ¬ (m - 1) ∣ (n - 1) := by
      intro h
      have hzeroMod := Nat.mod_eq_zero_of_dvd h
      omega
    have strict : 2 * (n - 1) < t * (m - 1) := by
      have unequal : 2 * (n - 1) ≠ t * (m - 1) := by
        intro heq
        have weights : weight n + weight n = t * (m - 1) := by unfold weight; omega
        exact nondivisible (tight_clears_divisible hm run (Nat.le_refl n) (Nat.le_refl n) weights).1
      omega
    by_cases hsmall : 2 * s < m - 1
    · simp only [quotientTurns, if_neg hzero, if_pos hsmall]
      have mulStrict : (2 * q) * (m - 1) < t * (m - 1) := by
        rw [Nat.mul_assoc]
        omega
      have h := (Nat.mul_lt_mul_right Mpos).mp mulStrict
      omega
    · simp only [quotientTurns, if_neg hzero, if_neg hsmall]
      have expand : (2 * q + 1) * (m - 1) = 2 * (q * (m - 1)) + (m - 1) := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
      have mulStrict : (2 * q + 1) * (m - 1) < t * (m - 1) := by
        rw [expand]
        omega
      have h := (Nat.mul_lt_mul_right Mpos).mp mulStrict
      omega

/-- Executable optimum for n≥2 and m≥2, expressed without a ceiling function. -/
def optimalTurns (n m : Nat) : Nat :=
  quotientTurns ((n - 1) / (m - 1)) ((n - 1) % (m - 1)) (m - 1)

/-- Complete finite-counter classification for every n≥2 and m≥2.
The attaining `Clears` proof is built from explicit allowed probe allocations.
This theorem has no graph-semantic premise and makes no assertion about a
room graph until the separate geometric reduction is formalized. -/
theorem counter_classification (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    Clears n m n n (optimalTurns n m) ∧
      ∀ t, Clears n m n n t → optimalTurns n m ≤ t := by
  have hdiv := Nat.div_add_mod' (n - 1) (m - 1)
  have decomp : n = ((n - 1) / (m - 1)) * (m - 1) + ((n - 1) % (m - 1)) + 1 := by
    omega
  have hs : (n - 1) % (m - 1) < m - 1 := Nat.mod_lt _ (by omega)
  constructor
  · exact quotient_upper hn hm decomp hs
  · intro t run
    exact quotient_lower hn hm decomp hs run

/-- One probe cannot clear the finite counter process when n≥2. -/
theorem one_probe_no_clears (n t : Nat) (hn : 2 ≤ n) :
    ¬ Clears n 1 n n t := by
  induction t with
  | zero =>
      intro run
      cases run
      omega
  | succ t ih =>
      intro run
      cases run with
      | @step b c p q t budget rest =>
          have hp : p ≤ 1 := by omega
          have hq : q ≤ 1 := by omega
          rw [full_one_probe hn hp, full_one_probe hn hq] at rest
          exact ih rest

theorem quotient_ceiling (q s M : Nat) (hM : 0 < M) (hs : s < M) :
    quotientTurns q s M = (2 * (q * M + s) + M - 1) / M +
      (if 2 * s = M then 1 else 0) := by
  have e0 : (2 * q) * M = 2 * (q * M) := Nat.mul_assoc 2 q M
  have e1 : (2 * q + 1) * M = 2 * (q * M) + M := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  have e2 : (2 * q + 2) * M = 2 * (q * M) + 2 * M := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have e2b : (2 * q + 1 + 1) * M = 2 * (q * M) + 2 * M := by
    have h : 2 * q + 1 + 1 = 2 * q + 2 := by omega
    rw [h, e2]
  have e3 : (2 * q + 2 + 1) * M = 2 * (q * M) + 3 * M := by
    rw [Nat.add_mul, e2, Nat.one_mul]
    omega
  by_cases zero : s = 0
  · have division : (2 * (q * M + s) + M - 1) / M = 2 * q :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have nohalf : ¬ 2 * s = M := by omega
    simp only [quotientTurns, if_pos zero, if_neg nohalf, division, Nat.add_zero]
  · by_cases small : 2 * s < M
    · have division : (2 * (q * M + s) + M - 1) / M = 2 * q + 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      have nohalf : ¬ 2 * s = M := by omega
      simp only [quotientTurns, if_neg zero, if_pos small, if_neg nohalf, division, Nat.add_zero]
    · by_cases half : 2 * s = M
      · have division : (2 * (q * M + s) + M - 1) / M = 2 * q + 1 :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        simp only [quotientTurns, if_neg zero, if_neg small, if_pos half, division]
      · have division : (2 * (q * M + s) + M - 1) / M = 2 * q + 2 :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        simp only [quotientTurns, if_neg zero, if_neg small, if_neg half, division, Nat.add_zero]

/-- Equality with the ceiling-plus-half-residue expression in the ordinary proof. -/
theorem optimalTurns_ceiling (n m : Nat) (hm : 2 ≤ m) :
    optimalTurns n m = (2 * (n - 1) + (m - 1) - 1) / (m - 1) +
      (if (m - 1) % 2 = 0 ∧ (n - 1) % (m - 1) = (m - 1) / 2 then 1 else 0) := by
  have hM : 0 < m - 1 := by omega
  have hs := Nat.mod_lt (n - 1) hM
  have division := Nat.div_add_mod' (n - 1) (m - 1)
  have formula := quotient_ceiling ((n - 1) / (m - 1)) ((n - 1) % (m - 1)) (m - 1) hM hs
  have half : 2 * ((n - 1) % (m - 1)) = m - 1 ↔
      (m - 1) % 2 = 0 ∧ (n - 1) % (m - 1) = (m - 1) / 2 := by omega
  unfold optimalTurns
  rw [formula, division]
  simp only [half]

end Princess.Ladder

#print axioms Princess.Ladder.next_mono
#print axioms Princess.Ladder.weight_round
#print axioms Princess.Ladder.counter_dominated
#print axioms Princess.Ladder.capture_lower_bound
#print axioms Princess.Ladder.one_probe_impossible
#print axioms Princess.Ladder.two_probe_optimal
#print axioms Princess.Ladder.partial_round_strict
#print axioms Princess.Ladder.tight_left_elimination
#print axioms Princess.Ladder.tight_clears_divisible
#print axioms Princess.Ladder.capture_strict_when_nondivisible
#print axioms Princess.Ladder.quotient_upper
#print axioms Princess.Ladder.counter_classification
#print axioms Princess.Ladder.one_probe_no_clears
#print axioms Princess.Ladder.optimalTurns_ceiling
