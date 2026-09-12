import PathRankLower

/-! The remaining odd-path equality obstruction. The proof uses actual finite
counter traces, their last full states before first capture, and interval probe
sums. It does not assume monotone inspections or disjoint active intervals. -/

namespace Princess.PathOddRankLower

open Princess.PathRankLower

def phaseCap (n phase t : Nat) : Nat := n + if (phase + t) % 2 = 0 then 1 else 0

def phaseCounter (n phase : Nat) (p : Nat → Nat) : Nat → Nat
  | 0 => phaseCap n phase 0
  | t + 1 => step (phaseCap n phase (t + 1)) (phaseCounter n phase p t) (p t)

theorem phaseCap_lower (n phase t : Nat) : n ≤ phaseCap n phase t := by
  unfold phaseCap; split <;> omega

theorem phaseCounter_le (n phase : Nat) (p : Nat → Nat) (t : Nat) :
    phaseCounter n phase p t ≤ phaseCap n phase t := by
  cases t with
  | zero => simp [phaseCounter]
  | succ t => exact step_le _ _ _

def sumFrom (p : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumFrom p a k + p (a + k)

theorem sumFrom_concat (p : Nat → Nat) (a b c : Nat) :
    sumFrom p a (b + c) = sumFrom p a b + sumFrom p (a + b) c := by
  induction c with
  | zero => simp [sumFrom]
  | succ c ih =>
      change sumFrom p a (b + c) + p (a + (b + c)) =
        sumFrom p a b + (sumFrom p (a + b) c + p ((a + b) + c))
      rw [ih]
      simp only [Nat.add_assoc]

theorem sumFrom_length_mono (p : Nat → Nat) (a : Nat) {b c : Nat} (h : b ≤ c) :
    sumFrom p a b ≤ sumFrom p a c := by
  have hc : c = b + (c - b) := by omega
  rw [hc, sumFrom_concat]
  omega

theorem sumFrom_nested (p : Nat → Nat) (a b k l : Nat)
    (hstart : b ≤ a) (hend : a + k ≤ b + l) :
    sumFrom p a k ≤ sumFrom p b l := by
  have ha := sumFrom_concat p 0 a k
  have hb := sumFrom_concat p 0 b l
  simp only [Nat.zero_add] at ha hb
  have hlo := sumFrom_length_mono p 0 hstart
  have hhi := sumFrom_length_mono p 0 hend
  omega

theorem pair_sum_budget (p q : Nat → Nat) (m a k : Nat)
    (budget : ∀ i, p i + q i ≤ m) :
    sumFrom p a k + sumFrom q a k ≤ k * m := by
  induction k with
  | zero => simp [sumFrom]
  | succ k ih =>
      have hb := budget (a + k)
      simp only [sumFrom, Nat.succ_mul k m]
      omega

theorem sum_budget (p : Nat → Nat) (m a k : Nat)
    (budget : ∀ i, p i ≤ m) : sumFrom p a k ≤ k * m := by
  induction k with
  | zero => simp [sumFrom]
  | succ k ih =>
      have hb := budget (a + k)
      simp only [sumFrom, Nat.succ_mul k m]
      omega

theorem pair_nested_budget (p q : Nat → Nat) (m a k b l s t : Nat)
    (budget : ∀ i, p i + q i ≤ m)
    (ha : s ≤ a) (hA : a + k ≤ s + t)
    (hb : s ≤ b) (hB : b + l ≤ s + t) :
    sumFrom p a k + sumFrom q b l ≤ t * m := by
  have hp := sumFrom_nested p a s k t ha hA
  have hq := sumFrom_nested q b s l t hb hB
  have hsum := pair_sum_budget p q m s t budget
  omega

theorem least_bounded (P : Nat → Prop) (t : Nat) (existsP : ∃ i, i ≤ t ∧ P i) :
    ∃ i, i ≤ t ∧ P i ∧ ∀ j, j < i → ¬ P j := by
  classical
  induction t with
  | zero =>
      obtain ⟨i, hi, hP⟩ := existsP
      have hi0 : i = 0 := by omega
      subst i
      exact ⟨0, by omega, hP, by intro j hj; omega⟩
  | succ t ih =>
      by_cases early : ∃ i, i ≤ t ∧ P i
      · obtain ⟨i, hi, hp, hmin⟩ := ih early
        exact ⟨i, by omega, hp, hmin⟩
      · obtain ⟨i, hi, hp⟩ := existsP
        have hi' : i = t + 1 := by
          by_cases he : i ≤ t
          · exact False.elim (early ⟨i, he, hp⟩)
          · omega
        subst i
        exact ⟨t + 1, by omega, hp, by
          intro j hj hpj
          exact early ⟨j, by omega, hpj⟩⟩

theorem greatest_bounded (P : Nat → Prop) (t : Nat) (existsP : ∃ i, i ≤ t ∧ P i) :
    ∃ i, i ≤ t ∧ P i ∧ ∀ j, i < j → j ≤ t → ¬ P j := by
  classical
  induction t with
  | zero =>
      obtain ⟨i, hi, hp⟩ := existsP
      have hi0 : i = 0 := by omega
      subst i
      exact ⟨0, by omega, hp, by intro j hj htop; omega⟩
  | succ t ih =>
      by_cases hp : P (t + 1)
      · exact ⟨t + 1, by omega, hp, by intro j hj htop; omega⟩
      · obtain ⟨i, hi, hpi⟩ := existsP
        have hi' : i ≤ t := by
          by_cases hit : i = t + 1
          · subst i; exact False.elim (hp hpi)
          · omega
        obtain ⟨a, ha, hpa, hmax⟩ := ih ⟨i, hi', hpi⟩
        refine ⟨a, by omega, hpa, ?_⟩
        intro j haj hjtop hpj
        by_cases hje : j = t + 1
        · subst j; exact hp hpj
        · exact hmax j haj (by omega) hpj

structure Active (n phase : Nat) (p : Nat → Nat) (t : Nat) where
  start : Nat
  len : Nat
  len_pos : 1 ≤ len
  bounded : start + len ≤ t
  full_start : phaseCounter n phase p start = phaseCap n phase start
  positive : ∀ j, j < len → 0 < phaseCounter n phase p (start + j)
  proper : ∀ j, 0 < j → j < len →
    phaseCounter n phase p (start + j) < phaseCap n phase (start + j)
  captured : phaseCounter n phase p (start + len) = 0

theorem active_exists (n phase : Nat) (p : Nat → Nat) (t : Nat)
    (hn : 1 ≤ n) (captured : phaseCounter n phase p t = 0) :
    Nonempty (Active n phase p t) := by
  obtain ⟨b, hb, hb0, hfirst⟩ := least_bounded
    (fun i => phaseCounter n phase p i = 0) t ⟨t, by omega, captured⟩
  have hbpos : 1 ≤ b := by
    have hc := phaseCap_lower n phase 0
    by_cases hz : b = 0
    · subst b; simp only [phaseCounter] at hb0; omega
    · omega
  obtain ⟨a, ha, hfull, hlast⟩ := greatest_bounded
    (fun i => phaseCounter n phase p i = phaseCap n phase i) (b - 1)
    ⟨0, by omega, rfl⟩
  have hab : a < b := by omega
  have heq : a + (b - a) = b := by omega
  refine ⟨⟨a, b - a, by omega, by omega, hfull, ?_, ?_, ?_⟩⟩
  · intro j hj
    have hne := hfirst (a + j) (by omega)
    omega
  · intro j hj0 hj
    have hne := hlast (a + j) (by omega) (by omega)
    have hle := phaseCounter_le n phase p (a + j)
    omega
  · simpa only [heq] using hb0

theorem step_affine {cap u p v : Nat} (hstep : v = step cap u p)
    (hv : 0 < v) (hcap : v < cap) : v + 2 * p = u + 1 := by
  unfold step at hstep
  split at hstep
  · omega
  · simp only [Nat.min_def] at hstep
    split at hstep <;> omega

theorem step_captured {cap u p : Nat} (hcap : 1 ≤ cap)
    (captured : step cap u p = 0) : u / 2 ≤ p := by
  unfold step at captured
  split at captured
  · assumption
  · simp only [Nat.min_def] at captured
    split at captured <;> omega

theorem active_affine {n phase t : Nat} {p : Nat → Nat}
    (a : Active n phase p t) (j : Nat) (hj : j < a.len) :
    phaseCounter n phase p (a.start + j) + 2 * sumFrom p a.start j =
      phaseCap n phase a.start + j := by
  induction j with
  | zero => simp only [Nat.add_zero, sumFrom, Nat.mul_zero, a.full_start]
  | succ j ih =>
      have old := ih (by omega)
      have hpos := a.positive (j + 1) hj
      have hproper := a.proper (j + 1) (by omega) hj
      have hstep : phaseCounter n phase p (a.start + (j + 1)) =
          step (phaseCap n phase (a.start + (j + 1)))
            (phaseCounter n phase p (a.start + j)) (p (a.start + j)) := by
        rw [show a.start + (j + 1) = (a.start + j) + 1 by omega]
        rfl
      have heq := step_affine hstep hpos hproper
      simp only [sumFrom]
      omega

theorem active_probe_lower {n phase t : Nat} {p : Nat → Nat}
    (a : Active n phase p t) (hn : 1 ≤ n) :
    phaseCap n phase a.start + a.len ≤ 2 * sumFrom p a.start a.len + 2 := by
  have hlen : a.len - 1 + 1 = a.len := by have := a.len_pos; omega
  have hprev := active_affine a (a.len - 1) (by have := a.len_pos; omega)
  have hcap := phaseCap_lower n phase (a.start + a.len)
  have hz : step (phaseCap n phase (a.start + a.len))
      (phaseCounter n phase p (a.start + (a.len - 1)))
      (p (a.start + (a.len - 1))) = 0 := by
    have hc := a.captured
    rw [show a.start + a.len = (a.start + (a.len - 1)) + 1 by omega] at hc
    change step (phaseCap n phase (a.start + (a.len - 1) + 1))
      (phaseCounter n phase p (a.start + (a.len - 1)))
      (p (a.start + (a.len - 1))) = 0 at hc
    simpa only [Nat.add_assoc, hlen] using hc
  have hlast := step_captured (by omega : 1 ≤ phaseCap n phase (a.start + a.len)) hz
  have hsum : sumFrom p a.start a.len =
      sumFrom p a.start (a.len - 1) + p (a.start + (a.len - 1)) := by
    have hx : sumFrom p a.start (a.len - 1 + 1) =
      sumFrom p a.start (a.len - 1) + p (a.start + (a.len - 1)) := rfl
    simpa only [hlen] using hx
  have hpos := a.len_pos
  omega


theorem active_exception_bound {n phase t : Nat} {p : Nat → Nat}
    (a : Active n phase p t) (m blocks d : Nat)
    (hm : 2 ≤ m) (hmeven : m % 2 = 0) (hd : d + 1 = 2 * m)
    (hn : n = blocks * d + m + 1) (budget : ∀ i, p i ≤ m) :
    blocks * m + m / 2 ≤ sumFrom p a.start a.len ∧
    (sumFrom p a.start a.len = blocks * m + m / 2 →
      a.len = blocks + 1 ∧ phaseCap n phase a.start = n) := by
  have hnpos : 1 ≤ n := by omega
  have hlower := active_probe_lower a hnpos
  have hupper := sum_budget p m a.start a.len budget
  have hcap := phaseCap_lower n phase a.start
  have hprod (j : Nat) : j * d + j = 2 * (j * m) := by
    calc
      j * d + j = j * (d + 1) := by simp [Nat.mul_add]
      _ = j * (2 * m) := by rw [hd]
      _ = 2 * (j * m) := by rw [Nat.mul_left_comm]
  have hlenprod := hprod a.len
  have hblocksprod := hprod blocks
  have hlen : blocks + 1 ≤ a.len := by
    by_cases h : a.len ≤ blocks
    · have hmul := Nat.mul_le_mul_right d h
      omega
    · omega
  constructor
  · omega
  · intro heq
    constructor <;> omega

theorem phaseCap_small {n phase t : Nat} (h : phaseCap n phase t = n) :
    (phase + t) % 2 = 1 := by
  unfold phaseCap at h
  split at h <;> omega

theorem odd_exception_impossible (m blocks d n : Nat) (p q : Nat → Nat)
    (hm : 2 ≤ m) (hmeven : m % 2 = 0) (hblocks : blocks % 2 = 0)
    (hd : d + 1 = 2 * m) (hn : n = blocks * d + m + 1)
    (budget : ∀ i, p i + q i ≤ m)
    (left : phaseCounter n 0 p (2 * blocks + 1) = 0)
    (right : phaseCounter n 1 q (2 * blocks + 1) = 0) : False := by
  have hnpos : 1 ≤ n := by omega
  obtain ⟨a⟩ := active_exists n 0 p (2 * blocks + 1) hnpos left
  obtain ⟨b⟩ := active_exists n 1 q (2 * blocks + 1) hnpos right
  have ha := active_exception_bound a m blocks d hm hmeven hd hn (by
    intro i; have := budget i; omega)
  have hb := active_exception_bound b m blocks d hm hmeven hd hn (by
    intro i; have := budget i; omega)
  have hab := pair_nested_budget p q m a.start a.len b.start b.len
    0 (2 * blocks + 1) budget (by omega) (by simpa using a.bounded)
      (by omega) (by simpa using b.bounded)
  have hprod : (2 * blocks + 1) * m = 2 * (blocks * m) + m := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have hpa : sumFrom p a.start a.len = blocks * m + m / 2 := by omega
  have hpb : sumFrom q b.start b.len = blocks * m + m / 2 := by omega
  obtain ⟨hal, hac⟩ := ha.2 hpa
  obtain ⟨hbl, hbc⟩ := hb.2 hpb
  have hap := phaseCap_small hac
  have hbp := phaseCap_small hbc
  have habound := a.bounded
  have hbbound := b.bounded
  have haodd : a.start % 2 = 1 := by omega
  have hbeven : b.start % 2 = 0 := by omega
  have habudget : sumFrom p a.start a.len + sumFrom q b.start b.len ≤
      (2 * blocks) * m := by
    by_cases hz : b.start = 0
    · exact pair_nested_budget p q m a.start a.len b.start b.len 0 (2 * blocks)
        budget (by omega) (by omega) (by omega) (by omega)
    · exact pair_nested_budget p q m a.start a.len b.start b.len 1 (2 * blocks)
        budget (by omega) (by omega) (by omega) (by omega)
  have hprod' : (2 * blocks) * m = 2 * (blocks * m) := by
    rw [Nat.mul_assoc]
  omega

end Princess.PathOddRankLower

#print axioms Princess.PathOddRankLower.odd_exception_impossible
