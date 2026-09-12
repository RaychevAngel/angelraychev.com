import Std

/-! Finite inverse-profile arithmetic. No geometric or hunter-number theorem
is assumed here. Subtraction is natural-number subtraction; the inclusion of
the zero-cardinality entry makes these maxima equal to signed-surplus maxima. -/
namespace Princess.ProfileInverse

def maxTo (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (maxTo f n) (f (n + 1))

theorem le_maxTo (f : Nat → Nat) (n k : Nat) (hk : k ≤ n) :
    f k ≤ maxTo f n := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      subst k
      exact Nat.le_refl _
  | succ n ih =>
      by_cases h : k ≤ n
      · exact Nat.le_trans (ih h) (Nat.le_max_left _ _)
      · have : k = n + 1 := by omega
        subst k
        exact Nat.le_max_right _ _

theorem maxTo_le (f : Nat → Nat) (n b : Nat)
    (h : ∀ k, k ≤ n → f k ≤ b) : maxTo f n ≤ b := by
  induction n with
  | zero => exact h 0 (Nat.le_refl _)
  | succ n ih =>
      exact Nat.max_le.mpr ⟨ih (fun k hk => h k (by omega)), h (n+1) (by omega)⟩

theorem maxTo_attained (f : Nat → Nat) (n : Nat) :
    ∃ k, k ≤ n ∧ maxTo f n = f k := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | succ n ih =>
      obtain ⟨k, hk, hv⟩ := ih
      by_cases h : maxTo f n ≤ f (n + 1)
      · exact ⟨n+1, Nat.le_refl _, Nat.max_eq_right h⟩
      · refine ⟨k, by omega, ?_⟩
        change max (maxTo f n) (f (n+1)) = f k
        rw [Nat.max_eq_left (by omega), hv]

def inverse (e : Nat) (f : Nat → Nat) (z : Nat) : Nat :=
  maxTo (fun k => if f k ≤ z then k else 0) e

def surplus (e : Nat) (f : Nat → Nat) : Nat :=
  maxTo (fun k => f k - k) e

theorem inverse_le (e : Nat) (f : Nat → Nat) (z : Nat) :
    inverse e f z ≤ e := by
  apply maxTo_le
  intro k hk
  split <;> omega

theorem le_inverse (e : Nat) (f : Nat → Nat) (z k : Nat)
    (hk : k ≤ e) (h : f k ≤ z) : k ≤ inverse e f z := by
  have := le_maxTo (fun k => if f k ≤ z then k else 0) e k hk
  simpa only [inverse, if_pos h] using this

theorem inverse_feasible (e : Nat) (f : Nat → Nat) (z : Nat)
    (hzero : f 0 = 0) : f (inverse e f z) ≤ z := by
  obtain ⟨k, _, h⟩ := maxTo_attained (fun k => if f k ≤ z then k else 0) e
  change inverse e f z = (if f k ≤ z then k else 0) at h
  by_cases hf : f k ≤ z
  · rw [if_pos hf] at h
    simpa only [h] using hf
  · rw [if_neg hf] at h
    simp only [h, hzero]
    omega

theorem inverse_next (e : Nat) (f : Nat → Nat) (z : Nat)
    (h : inverse e f z < e) : z < f (inverse e f z + 1) := by
  by_cases hf : f (inverse e f z + 1) ≤ z
  · have := le_inverse e f z (inverse e f z + 1) (by omega) hf
    omega
  · omega

theorem surplus_bound (e : Nat) (f : Nat → Nat) (k : Nat) (hk : k ≤ e) :
    f k ≤ k + surplus e f := by
  have := le_maxTo (fun k => f k - k) e k hk
  change f k - k ≤ surplus e f at this
  omega

/-- The natural-subtraction maximum is attained as an ordinary signed
difference, because f(0)=0 supplies a zero-surplus witness. -/
theorem surplus_attained (e : Nat) (f : Nat → Nat) (hzero : f 0 = 0) :
    ∃ k, k ≤ e ∧ f k = k + surplus e f := by
  by_cases hu : surplus e f = 0
  · exact ⟨0, Nat.zero_le _, by omega⟩
  · obtain ⟨k, hk, hat⟩ := maxTo_attained (fun k => f k-k) e
    change surplus e f = f k-k at hat
    exact ⟨k, hk, by omega⟩

/-- A finite inverse identity, conditional only on the displayed profile
properties. The graph module below supplies these from actual neighborhoods. -/
theorem inverse_surplus (m : Nat) (f : Nat → Nat)
    (_hm : 0 < m) (hzero : f 0 = 0)
    (hfull : f (m+1) = m)
    (hpos : ∀ k, 0 < k → k ≤ m+1 → 0 < f k)
    (hbound : ∀ k, k ≤ m+1 → f k ≤ m)
    (hmono : ∀ a b, a ≤ b → b ≤ m+1 → f a ≤ f b) :
    maxTo (fun z => z - inverse (m+1) f z) m = surplus (m+1) f := by
  apply Nat.le_antisymm
  · apply maxTo_le
    intro z hz
    have hi := inverse_le (m+1) f z
    by_cases he : inverse (m+1) f z = m+1
    · omega
    · have hn := inverse_next (m+1) f z (by omega)
      have hs := surplus_bound (m+1) f (inverse (m+1) f z + 1) (by omega)
      omega
  · by_cases hu : surplus (m+1) f = 0
    · omega
    · obtain ⟨x, hx, hat⟩ := maxTo_attained (fun k => f k - k) (m+1)
      change surplus (m+1) f = f x - x at hat
      have hxpos : 0 < x := by
        by_cases h : x = 0
        · simp only [h, hzero, Nat.sub_zero] at hat
          omega
        · omega
      have hfpos := hpos x hxpos hx
      have hfbound := hbound x hx
      let z := f x - 1
      have hz : z ≤ m := by omega
      have hi := inverse_le (m+1) f z
      have hif := inverse_feasible (m+1) f z hzero
      have hix : inverse (m+1) f z < x := by
        by_cases h : x ≤ inverse (m+1) f z
        · have hh := hmono x (inverse (m+1) f z) h hi
          omega
        · omega
      have hb := le_maxTo (fun z => z - inverse (m+1) f z) m z hz
      omega

/-- If g is the complementary inverse of f on classes of sizes m+1 and m,
their maximum surpluses differ by exactly one. No hunter-number axiom is used. -/
theorem dual_surplus (m : Nat) (f g : Nat → Nat)
    (hm : 0 < m) (hzero : f 0 = 0)
    (hfull : f (m+1) = m)
    (hpos : ∀ k, 0 < k → k ≤ m+1 → 0 < f k)
    (hbound : ∀ k, k ≤ m+1 → f k ≤ m)
    (hmono : ∀ a b, a ≤ b → b ≤ m+1 → f a ≤ f b)
    (hdual : ∀ y, y ≤ m → g y = m+1 - inverse (m+1) f (m-y)) :
    surplus m g = surplus (m+1) f + 1 := by
  have hinv := inverse_surplus m f hm hzero hfull hpos hbound hmono
  apply Nat.le_antisymm
  · apply maxTo_le
    intro y hy
    have hid := inverse_le (m+1) f (m-y)
    have hmax := le_maxTo (fun z => z - inverse (m+1) f z) m (m-y) (by omega)
    rw [hinv] at hmax
    rw [hdual y hy]
    omega
  · obtain ⟨z, hz, hat⟩ := maxTo_attained (fun z => z - inverse (m+1) f z) m
    rw [hinv] at hat
    by_cases hzeroU : surplus (m+1) f = 0
    · have invzero : inverse (m+1) f 0 = 0 := by
        have hi := inverse_le (m+1) f 0
        have hf := inverse_feasible (m+1) f 0 hzero
        by_cases h : inverse (m+1) f 0 = 0
        · exact h
        · have := hpos (inverse (m+1) f 0) (by omega) hi
          omega
      have hg := hdual m (Nat.le_refl _)
      simp only [Nat.sub_self, invzero, Nat.sub_zero] at hg
      have hb := le_maxTo (fun k => g k - k) m m (Nat.le_refl _)
      change g m - m ≤ surplus m g at hb
      omega
    · have hid := inverse_le (m+1) f z
      have hzpos : inverse (m+1) f z < z := by omega
      have hdual' := hdual (m-z) (by omega)
      have hdiff : m-(m-z) = z := by omega
      rw [hdiff] at hdual'
      have hb := le_maxTo (fun k => g k - k) m (m-z) (by omega)
      change g (m-z) - (m-z) ≤ surplus m g at hb
      omega

end Princess.ProfileInverse
#print axioms Princess.ProfileInverse.dual_surplus
