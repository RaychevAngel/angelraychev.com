import Std

/-! Exact two-candidate minimization of a pronic root plus a square root.
The roots are defined by their integer capacity functions. This is an
arithmetic theorem; it does not assert the unfinished rectangle midpoint
criterion or any new geometric compression theorem.
-/
namespace Princess.RootConvolution

def ceiling (capacity : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if n+1 ≤ capacity (ceiling capacity n)
      then ceiling capacity n else ceiling capacity n + 1

theorem ceiling_spec (capacity : Nat → Nat)
    (hmono : ∀ a b, a ≤ b → capacity a ≤ capacity b)
    (hstep : ∀ a, capacity a < capacity (a+1)) (n t : Nat) :
    ceiling capacity n ≤ t ↔ n ≤ capacity t := by
  induction n generalizing t with
  | zero => simp [ceiling]
  | succ n ih =>
    have old : n ≤ capacity (ceiling capacity n) := (ih _).mp (Nat.le_refl _)
    simp only [ceiling]
    split
    · rename_i h
      constructor
      · intro ht
        exact Nat.le_trans h (hmono _ _ ht)
      · intro ht
        exact (ih _).mpr (by omega)
    · rename_i h
      have bound : n+1 ≤ capacity (ceiling capacity n+1) := by
        have := hstep (ceiling capacity n)
        omega
      constructor
      · intro ht
        exact Nat.le_trans bound (hmono _ _ ht)
      · intro ht
        by_cases he : ceiling capacity n + 1 ≤ t
        · exact he
        · have := hmono t (ceiling capacity n) (by omega)
          omega

def pronicCapacity (r : Nat) := r*(r+1)
def squareCapacity (r : Nat) := r*r
def q (n : Nat) := ceiling pronicCapacity n
def R (n : Nat) := ceiling squareCapacity n

theorem pronic_mono (a b : Nat) (h : a ≤ b) :
    pronicCapacity a ≤ pronicCapacity b := by
  exact Nat.mul_le_mul h (by omega)

theorem square_mono (a b : Nat) (h : a ≤ b) :
    squareCapacity a ≤ squareCapacity b := by
  exact Nat.mul_le_mul h h

theorem pronic_step (a : Nat) : pronicCapacity a < pronicCapacity (a+1) := by
  simp only [pronicCapacity, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem square_step (a : Nat) : squareCapacity a < squareCapacity (a+1) := by
  simp only [squareCapacity, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem q_spec (n t : Nat) : q n ≤ t ↔ n ≤ t*(t+1) :=
  ceiling_spec pronicCapacity pronic_mono pronic_step n t

theorem R_spec (n t : Nat) : R n ≤ t ↔ n ≤ t*t :=
  ceiling_spec squareCapacity square_mono square_step n t

theorem q_mono (a b : Nat) (h : a ≤ b) : q a ≤ q b :=
  (q_spec _ _).mpr (Nat.le_trans h ((q_spec _ _).mp (Nat.le_refl _)))

theorem R_mono (a b : Nat) (h : a ≤ b) : R a ≤ R b :=
  (R_spec _ _).mpr (Nat.le_trans h ((R_spec _ _).mp (Nat.le_refl _)))

def capacitySum (r s : Nat) := r*(r+1)+s*s

theorem move_to_square (a x s : Nat) (h : a+x ≤ s) :
    capacitySum (a+x) s ≤ capacitySum a (s+x) := by
  by_cases hx : x=0
  · subst x; simp [capacitySum]
  · have hfactor : 2*a+1 ≤ 2*s := by omega
    have hp := Nat.mul_le_mul_left x hfactor
    simp only [capacitySum, Nat.mul_two, Nat.mul_add, Nat.mul_one, Nat.mul_comm] at *
    omega

theorem move_to_pronic (r b y : Nat) (h : b ≤ r) :
    capacitySum r (b+y) ≤ capacitySum (r+y) b := by
  have hfactor : 2*b ≤ 2*r+1 := by omega
  have hp := Nat.mul_le_mul_left y hfactor
  simp only [capacitySum, Nat.mul_two, Nat.mul_add, Nat.mul_one, Nat.mul_comm] at *
  omega

/-- At a fixed sum, one of the two permitted extreme allocations has
at least the original square-plus-pronic capacity. -/
theorem extreme_capacity (r s a b : Nat) (ha : a ≤ r) (hb : b ≤ s) :
    capacitySum r s ≤ capacitySum a (r+s-a) ∨
    capacitySum r s ≤ capacitySum (r+s-b) b := by
  by_cases hrs : r ≤ s
  · have hr : a+(r-a)=r := by omega
    have h := move_to_square a (r-a) s (by omega)
    rw [hr] at h
    have he : s+(r-a)=r+s-a := by omega
    rw [he] at h
    exact Or.inl h
  · have hs : b+(s-b)=s := by omega
    have h := move_to_pronic r b (s-b) (by omega)
    rw [hs] at h
    have he : r+(s-b)=r+s-b := by omega
    rw [he] at h
    exact Or.inr h

def leftCandidate (l u : Nat) := min u ((q l)*(q l+1))
def rightCandidate (S l u : Nat) := max l (S-(R (S-u))*(R (S-u)))
def cost (S y : Nat) := q y+R (S-y)

theorem candidates_in_interval (S l u : Nat) (hlu : l ≤ u) (huS : u ≤ S) :
    l ≤ leftCandidate l u ∧ leftCandidate l u ≤ u ∧
    l ≤ rightCandidate S l u ∧ rightCandidate S l u ≤ u := by
  have hq := (q_spec l (q l)).mp (Nat.le_refl _)
  have hR := (R_spec (S-u) (R (S-u))).mp (Nat.le_refl _)
  simp only [leftCandidate, rightCandidate, Nat.min_def, Nat.max_def]
  split <;> split <;> omega

/-- Every interval value is bounded below by one of two explicit values.
Together with interval membership this identifies the exact minimum. -/
theorem two_candidate_lower (S l u y : Nat)
    (hlu : l ≤ u) (huS : u ≤ S) (hly : l ≤ y) (hyu : y ≤ u) :
    min (cost S (leftCandidate l u)) (cost S (rightCandidate S l u)) ≤
      cost S y := by
  let r := q y
  let s := R (S-y)
  let a := q l
  let b := R (S-u)
  have ha : a ≤ r := q_mono _ _ hly
  have hb : b ≤ s := R_mono _ _ (by omega)
  have hry : y ≤ r*(r+1) := (q_spec _ _).mp (Nat.le_refl _)
  have hsy : S-y ≤ s*s := (R_spec _ _).mp (Nat.le_refl _)
  have hS : S ≤ capacitySum r s := by unfold capacitySum; omega
  have hr0 : S-u ≤ b*b := (R_spec _ _).mp (Nat.le_refl _)
  have hq0 : l ≤ a*(a+1) := (q_spec _ _).mp (Nat.le_refl _)
  have candidates := candidates_in_interval S l u hlu huS
  rcases extreme_capacity r s a b ha hb with hleft | hright
  · have hcap : S ≤ a*(a+1)+(r+s-a)*(r+s-a) := Nat.le_trans hS hleft
    have hqa : q (leftCandidate l u) ≤ a := by
      apply (q_spec _ _).mpr
      exact Nat.min_le_right _ _
    have hrb : R (S-leftCandidate l u) ≤ r+s-a := by
      apply (R_spec _ _).mpr
      have hb' : b ≤ r+s-a := by omega
      have hsquares := square_mono _ _ hb'
      unfold squareCapacity at hsquares
      unfold leftCandidate
      change S-min u (a*(a+1)) ≤ (r+s-a)*(r+s-a)
      simp only [Nat.min_def]
      split <;> omega
    have hcost : cost S (leftCandidate l u) ≤ r+s := by unfold cost; omega
    exact Nat.le_trans (Nat.min_le_left _ _) hcost
  · have hcap : S ≤ (r+s-b)*(r+s-b+1)+b*b := Nat.le_trans hS hright
    have hrb : R (S-rightCandidate S l u) ≤ b := by
      apply (R_spec _ _).mpr
      unfold rightCandidate
      change S-max l (S-b*b) ≤ b*b
      omega
    have hqa : q (rightCandidate S l u) ≤ r+s-b := by
      apply (q_spec _ _).mpr
      have ha' : a ≤ r+s-b := by omega
      have hpronics := pronic_mono _ _ ha'
      unfold pronicCapacity at hpronics
      unfold rightCandidate
      change max l (S-b*b) ≤ (r+s-b)*(r+s-b+1)
      omega
    have hcost : cost S (rightCandidate S l u) ≤ r+s := by unfold cost; omega
    exact Nat.le_trans (Nat.min_le_right _ _) hcost

/-- An attaining point is one of the two candidates, and every interval
point has at least its cost. Both roots are the explicit total functions
defined above, not external oracle hypotheses. -/
theorem exact_minimum (S l u : Nat) (hlu : l ≤ u) (huS : u ≤ S) :
    ∃ y, l ≤ y ∧ y ≤ u ∧
      cost S y = min (cost S (leftCandidate l u)) (cost S (rightCandidate S l u)) ∧
      ∀ z, l ≤ z → z ≤ u → cost S y ≤ cost S z := by
  have hc := candidates_in_interval S l u hlu huS
  have hlower := two_candidate_lower S l u
  by_cases h : cost S (leftCandidate l u) ≤ cost S (rightCandidate S l u)
  · refine ⟨leftCandidate l u, hc.1, hc.2.1, ?_, ?_⟩
    · exact (Nat.min_eq_left h).symm
    · intro z hl hz
      simpa only [Nat.min_eq_left h] using hlower z hlu huS hl hz
  · have hr : cost S (rightCandidate S l u) ≤ cost S (leftCandidate l u) := by omega
    refine ⟨rightCandidate S l u, hc.2.2.1, hc.2.2.2, ?_, ?_⟩
    · exact (Nat.min_eq_right hr).symm
    · intro z hl hz
      simpa only [Nat.min_eq_right hr] using hlower z hlu huS hl hz

end Princess.RootConvolution
#print axioms Princess.RootConvolution.exact_minimum
