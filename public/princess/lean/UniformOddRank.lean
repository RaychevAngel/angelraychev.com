import Std

/-! Scalar potential for the uniform odd-rectangle minimum-budget lower bound.
The two neighborhood inequalities in `Step` are geometric hypotheses; this
module does not prove the odd-rectangle profile theorem or a physical bridge. -/
namespace Princess.UniformOddRank

def cutoff (b : Nat) : Nat := 2*(b*b) + 2*b + 2

def cap (b h : Nat) : Nat := 2*h - (4*(b*b) + 2*b + 6)

def value (b h k p : Nat) : Nat := min (cap b h) (2*k+p-cutoff b)

/-- Neighborhood lower bounds supplied by the ordinary exact profiles.
The central plateau inequality suffices; exact equality is not required. -/
def Step (b h k p r j : Nat) : Prop :=
  k-r ≤ j+1 ∧
  (b*b < k-r → k-r < h-b*b-1 → k-r+b+p ≤ j)

theorem clipping (c offset x y t : Nat) (h : x ≤ y+t) :
    min c (x-offset) ≤ min c (y-offset) + t := by
  simp only [Nat.min_def]
  split <;> split <;> omega

theorem value_zero (b h p : Nat) (hp : p ≤ 1) : value b h 0 p = 0 := by
  simp only [value, cutoff]
  have hz : 2*0+p-(2*(b*b)+2*b+2) = 0 := by omega
  rw [hz]
  exact Nat.min_zero _

theorem value_monotone (b h p a k : Nat) (ha : a ≤ k) :
    value b h a p ≤ value b h k p := by
  unfold value
  exact clipping (cap b h) (cutoff b) (2*a+p) (2*k+p) 0 (by omega)

/-- One cohort loses potential only when it receives the entire minimum
budget b+1, and even then loses at most one. -/
theorem potential_step (b h k p r j : Nat)
    (hp : p ≤ 1) (hr : r ≤ b+1) (step : Step b h k p r j) :
    value b h k p ≤ value b h j (1-p) + if r = b+1 then 1 else 0 := by
  obtain ⟨hnear, hmiddle⟩ := step
  by_cases hlo : k-r ≤ b*b
  · have hv : value b h k p ≤ if r = b+1 then 1 else 0 := by
      have hle := Nat.min_le_right (cap b h) (2*k+p-cutoff b)
      change value b h k p ≤ 2*k+p-cutoff b at hle
      unfold cutoff at hle
      split <;> omega
    omega
  · by_cases hhi : h-b*b-1 ≤ k-r
    · have target : cap b h ≤ 2*j+(1-p)-cutoff b := by
        unfold cap cutoff
        omega
      have full : value b h j (1-p) = cap b h := Nat.min_eq_left target
      have hle := Nat.min_le_left (cap b h) (2*k+p-cutoff b)
      change value b h k p ≤ cap b h at hle
      rw [full]
      omega
    · have hm := hmiddle (by omega) (by omega)
      have raw : 2*k+p ≤ 2*j+(1-p)+(if r = b+1 then 1 else 0) := by
        split <;> omega
      exact clipping (cap b h) (cutoff b) (2*k+p) (2*j+(1-p))
        (if r = b+1 then 1 else 0) raw

theorem value_initial_majority (b h : Nat) : value b h h 0 = cap b h := by
  apply Nat.min_eq_left
  unfold cap cutoff
  omega

theorem value_initial_minority (b h : Nat) (hh : 1 ≤ h) :
    value b h (h-1) 1 = cap b h := by
  apply Nat.min_eq_left
  unfold cap cutoff
  omega

/-- The sum over current physical colors decreases by at most one under
the shared minimum budget. The successor colors are explicitly exchanged. -/
theorem two_cohort_step (b h k₀ k₁ r₀ r₁ j₀ j₁ : Nat)
    (budget : r₀+r₁ ≤ b+1)
    (step₀ : Step b h k₀ 0 r₀ j₀) (step₁ : Step b h k₁ 1 r₁ j₁) :
    value b h k₀ 0 + value b h k₁ 1 ≤
      value b h j₁ 0 + value b h j₀ 1 + 1 := by
  have left := potential_step b h k₀ 0 r₀ j₀ (by omega) (by omega) step₀
  have right := potential_step b h k₁ 1 r₁ j₁ (by omega) (by omega) step₁
  simp only [Nat.sub_zero, Nat.sub_self] at left right
  by_cases h₀ : r₀ = b+1 <;> by_cases h₁ : r₁ = b+1 <;>
    simp [h₀, h₁] at left right <;> omega

end Princess.UniformOddRank
#print axioms Princess.UniformOddRank.potential_step
#print axioms Princess.UniformOddRank.two_cohort_step
