import Std

/-! A general two-candidate minimum for inverse discrete-convex capacities.
The inverse is constructed by finite search from an unboundedness witness;
flat initial or interior capacity steps are allowed. No geometric or game
normal-form hypotheses are hidden in this arithmetic statement.
-/
namespace Princess.ConvexCapacityConvolution

/-- Increasing integer increments, restricted to a finite interval. -/
def ConvexTo (f : Nat → Int) (T : Nat) : Prop :=
  ∀ i j, i ≤ j → j < T → f (i+1)-f i ≤ f (j+1)-f j

private theorem interval_nonincreasing (f : Nat → Int) (a n : Nat)
    (h : ∀ i, a ≤ i → i < a+n → f (i+1) ≤ f i) : f (a+n) ≤ f a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (by intro i hi hj; exact h i hi (by omega))
    have hs := h (a+n) (by omega) (by omega)
    have he : a+(n+1)=a+n+1 := by omega
    rw [he]
    omega

private theorem interval_nondecreasing (f : Nat → Int) (a n : Nat)
    (h : ∀ i, a ≤ i → i < a+n → f i ≤ f (i+1)) : f a ≤ f (a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (by intro i hi hj; exact h i hi (by omega))
    have hs := h (a+n) (by omega) (by omega)
    have he : a+(n+1)=a+n+1 := by omega
    rw [he]
    omega

/-- Convexity is used as an explicit increment inequality, not supplied
as the desired endpoint-maximization conclusion. -/
theorem endpoint_maximum (f : Nat → Int) (T l y u : Nat)
    (hc : ConvexTo f T) (hly : l ≤ y) (hyu : y ≤ u) (huT : u ≤ T) :
    f y ≤ f l ∨ f y ≤ f u := by
  by_cases he : y=l
  · subst y; exact Or.inl (Int.le_refl _)
  have hy : 0 < y := by omega
  have hy1 : y-1+1=y := by omega
  by_cases hs : f y ≤ f (y-1)
  · have hn := interval_nonincreasing f l (y-l) (by
      intro i hi hj
      have hd := hc i (y-1) (by omega) (by omega)
      rw [hy1] at hd
      omega)
    have hl : l+(y-l)=y := by omega
    rw [hl] at hn
    exact Or.inl hn
  · have hn := interval_nondecreasing f y (u-y) (by
      intro i hi hj
      have hd := hc (y-1) i (by omega) (by omega)
      rw [hy1] at hd
      omega)
    have hu : y+(u-y)=u := by omega
    rw [hu] at hn
    exact Or.inr hn

structure Capacity where
  value : Nat → Nat
  mono : ∀ a b, a ≤ b → value a ≤ value b
  unbounded : ∀ k, ∃ s, k ≤ value s
  convex : ∀ i j, i ≤ j →
    (value (i+1) : Int)-value i ≤ (value (j+1) : Int)-value j

private def search (A : Capacity) (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if k ≤ A.value n then search A k n else n+1

private theorem search_spec (A : Capacity) (k n : Nat) (hn : k ≤ A.value n) :
    ∀ t, search A k n ≤ t ↔ k ≤ A.value t := by
  induction n with
  | zero =>
    intro t
    have ht := A.mono 0 t (by omega)
    simp only [search]
    omega
  | succ n ih =>
    intro t
    simp only [search]
    split
    · rename_i h
      exact ih h t
    · rename_i h
      constructor
      · intro ht
        exact Nat.le_trans hn (A.mono _ _ ht)
      · intro ht
        by_cases he : n+1 ≤ t
        · exact he
        · have hm := A.mono t n (by omega)
          omega

noncomputable def root (A : Capacity) (k : Nat) : Nat :=
  search A k (Classical.choose (A.unbounded k))

theorem root_spec (A : Capacity) (k t : Nat) : root A k ≤ t ↔ k ≤ A.value t :=
  search_spec A k _ (Classical.choose_spec (A.unbounded k)) t

theorem root_mono (A : Capacity) (a b : Nat) (h : a ≤ b) : root A a ≤ root A b :=
  (root_spec A _ _).mpr (Nat.le_trans h ((root_spec A _ _).mp (Nat.le_refl _)))

private theorem sum_convex (A B : Capacity) (T : Nat) :
    ConvexTo (fun i => (A.value i : Int)+B.value (T-i)) T := by
  intro i j hij hjT
  have ha := A.convex i j hij
  have hb := B.convex (T-(j+1)) (T-(i+1)) (by omega)
  have hi : T-(i+1)+1=T-i := by omega
  have hj : T-(j+1)+1=T-j := by omega
  rw [hi,hj] at hb
  dsimp only
  omega

theorem extreme_capacity (A B : Capacity) (r s a b : Nat)
    (ha : a ≤ r) (hb : b ≤ s) :
    A.value r+B.value s ≤ A.value a+B.value (r+s-a) ∨
    A.value r+B.value s ≤ A.value (r+s-b)+B.value b := by
  have hh := endpoint_maximum (fun i => (A.value i : Int)+B.value (r+s-i))
    (r+s) a r (r+s-b) (sum_convex A B (r+s)) ha (by omega) (by omega)
  have hs : r+s-r=s := by omega
  have hb' : r+s-(r+s-b)=b := by omega
  rw [hs,hb'] at hh
  omega

noncomputable def leftCandidate (A : Capacity) (l u : Nat) := min u (A.value (root A l))
noncomputable def rightCandidate (B : Capacity) (S l u : Nat) := max l (S-B.value (root B (S-u)))
noncomputable def cost (A B : Capacity) (S y : Nat) := root A y+root B (S-y)

theorem candidates_in_interval (A B : Capacity) (S l u : Nat)
    (hlu : l ≤ u) (huS : u ≤ S) :
    l ≤ leftCandidate A l u ∧ leftCandidate A l u ≤ u ∧
    l ≤ rightCandidate B S l u ∧ rightCandidate B S l u ≤ u := by
  have ha := (root_spec A l (root A l)).mp (Nat.le_refl _)
  have hb := (root_spec B (S-u) (root B (S-u))).mp (Nat.le_refl _)
  simp only [leftCandidate,rightCandidate,Nat.min_def,Nat.max_def]
  split <;> split <;> omega

theorem two_candidate_lower (A B : Capacity) (S l u y : Nat)
    (_hlu : l ≤ u) (huS : u ≤ S) (hly : l ≤ y) (hyu : y ≤ u) :
    min (cost A B S (leftCandidate A l u)) (cost A B S (rightCandidate B S l u)) ≤
      cost A B S y := by
  let r := root A y
  let s := root B (S-y)
  let a := root A l
  let b := root B (S-u)
  have ha : a ≤ r := root_mono A _ _ hly
  have hb : b ≤ s := root_mono B _ _ (by omega)
  have hry : y ≤ A.value r := (root_spec A _ _).mp (Nat.le_refl _)
  have hsy : S-y ≤ B.value s := (root_spec B _ _).mp (Nat.le_refl _)
  have hS : S ≤ A.value r+B.value s := by omega
  have hr0 : S-u ≤ B.value b := (root_spec B _ _).mp (Nat.le_refl _)
  have hq0 : l ≤ A.value a := (root_spec A _ _).mp (Nat.le_refl _)
  rcases extreme_capacity A B r s a b ha hb with hleft | hright
  · have hcap := Nat.le_trans hS hleft
    have hqa : root A (leftCandidate A l u) ≤ a := by
      apply (root_spec A _ _).mpr
      exact Nat.min_le_right _ _
    have hrb : root B (S-leftCandidate A l u) ≤ r+s-a := by
      apply (root_spec B _ _).mpr
      have hsizes := B.mono b (r+s-a) (by omega)
      unfold leftCandidate
      change S-min u (A.value a) ≤ B.value (r+s-a)
      simp only [Nat.min_def]
      split <;> omega
    have hcost : cost A B S (leftCandidate A l u) ≤ r+s := by unfold cost; omega
    exact Nat.le_trans (Nat.min_le_left _ _) hcost
  · have hcap := Nat.le_trans hS hright
    have hrb : root B (S-rightCandidate B S l u) ≤ b := by
      apply (root_spec B _ _).mpr
      unfold rightCandidate
      change S-max l (S-B.value b) ≤ B.value b
      omega
    have hqa : root A (rightCandidate B S l u) ≤ r+s-b := by
      apply (root_spec A _ _).mpr
      have hsizes := A.mono a (r+s-b) (by omega)
      unfold rightCandidate
      change max l (S-B.value b) ≤ A.value (r+s-b)
      omega
    have hcost : cost A B S (rightCandidate B S l u) ≤ r+s := by unfold cost; omega
    exact Nat.le_trans (Nat.min_le_right _ _) hcost

theorem exact_minimum (A B : Capacity) (S l u : Nat)
    (hlu : l ≤ u) (huS : u ≤ S) :
    ∃ y, l ≤ y ∧ y ≤ u ∧
      cost A B S y = min (cost A B S (leftCandidate A l u))
        (cost A B S (rightCandidate B S l u)) ∧
      ∀ z, l ≤ z → z ≤ u → cost A B S y ≤ cost A B S z := by
  have hc := candidates_in_interval A B S l u hlu huS
  have hlower := two_candidate_lower A B S l u
  by_cases h : cost A B S (leftCandidate A l u) ≤ cost A B S (rightCandidate B S l u)
  · refine ⟨leftCandidate A l u,hc.1,hc.2.1,?_,?_⟩
    · exact (Nat.min_eq_left h).symm
    · intro z hl hz
      simpa only [Nat.min_eq_left h] using hlower z hlu huS hl hz
  · have hr : cost A B S (rightCandidate B S l u) ≤ cost A B S (leftCandidate A l u) := by omega
    refine ⟨rightCandidate B S l u,hc.2.2.1,hc.2.2.2,?_,?_⟩
    · exact (Nat.min_eq_right hr).symm
    · intro z hl hz
      simpa only [Nat.min_eq_right hr] using hlower z hlu huS hl hz

/-- The original square and pronic examples are concrete instances of the
general theorem; no inverse formula is supplied as an oracle. -/
def squareCapacity : Capacity where
  value s := s*s
  mono a b h := Nat.mul_le_mul h h
  unbounded k := by
    refine ⟨k+1, ?_⟩
    have hh := Nat.mul_le_mul_left (k+1) (show 1 ≤ k+1 by omega)
    simp only [Nat.mul_one] at hh
    omega
  convex i j hij := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

def pronicCapacity : Capacity where
  value s := s*(s+1)
  mono a b h := Nat.mul_le_mul h (by omega)
  unbounded k := by
    refine ⟨k+1, ?_⟩
    have hh := Nat.mul_le_mul_left (k+1) (show 1 ≤ k+1+1 by omega)
    simp only [Nat.mul_one] at hh
    omega
  convex i j hij := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

theorem square_root_spec (k s : Nat) : root squareCapacity k ≤ s ↔ k ≤ s*s :=
  root_spec squareCapacity k s

theorem pronic_root_spec (k s : Nat) : root pronicCapacity k ≤ s ↔ k ≤ s*(s+1) :=
  root_spec pronicCapacity k s

private theorem convex_from_local (f : Nat → Int)
    (hs : ∀ i, f (i+1)-f i ≤ f (i+2)-f (i+1)) :
    ∀ i j, i ≤ j → f (i+1)-f i ≤ f (j+1)-f j := by
  intro i j
  induction j with
  | zero =>
    intro h
    have : i=0 := by omega
    subst i
    omega
  | succ j ih =>
    intro h
    by_cases he : i=j+1
    · subst i; omega
    · have hp := ih (by omega)
      have hn := hs j
      have hj : j+1+1=j+2 := by omega
      rw [hj]
      omega

def maximumCapacity (A B : Capacity) : Capacity where
  value s := max (A.value s) (B.value s)
  mono a b h := by
    have ha := A.mono a b h
    have hb := B.mono a b h
    omega
  unbounded k := by
    obtain ⟨s,hs⟩ := A.unbounded k
    exact ⟨s,Nat.le_trans hs (Nat.le_max_left _ _)⟩
  convex := by
    apply convex_from_local (fun n => ((max (A.value n) (B.value n) : Nat) : Int))
    intro i
    have ha := A.convex i (i+1) (by omega)
    have hb := B.convex i (i+1) (by omega)
    have hi : i+1+1=i+2 := by omega
    rw [hi] at ha hb
    have a0 := Nat.le_max_left (A.value i) (B.value i)
    have a2 := Nat.le_max_left (A.value (i+2)) (B.value (i+2))
    have b0 := Nat.le_max_right (A.value i) (B.value i)
    have b2 := Nat.le_max_right (A.value (i+2)) (B.value (i+2))
    by_cases hm : A.value (i+1) ≤ B.value (i+1)
    · rw [Nat.max_eq_right hm]
      omega
    · rw [Nat.max_eq_left (show B.value (i+1) ≤ A.value (i+1) by omega)]
      omega

def triangle : Nat → Nat
  | 0 => 0
  | n+1 => triangle n+n

private theorem triangle_mono (a b : Nat) (h : a ≤ b) : triangle a ≤ triangle b := by
  induction b with
  | zero =>
    have : a=0 := by omega
    subst a
    omega
  | succ b ih =>
    by_cases he : a=b+1
    · subst a; omega
    · have hh := ih (by omega)
      simp only [triangle]
      omega

theorem triangle_double_next (n : Nat) : 2*triangle (n+1)=n*(n+1) := by
  induction n with
  | zero => simp [triangle]
  | succ n ih =>
    have hh : triangle (n+1+1)=triangle (n+1)+(n+1) := rfl
    rw [hh,Nat.mul_add,ih]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

theorem triangle_value (n : Nat) : triangle n=n*(n-1)/2 := by
  cases n with
  | zero => simp [triangle]
  | succ n =>
    have hh := triangle_double_next n
    have hn : n+1-1=n := by omega
    rw [hn,Nat.mul_comm (n+1) n,←hh]
    omega

def triangularCapacity : Capacity where
  value := triangle
  mono := triangle_mono
  unbounded k := by refine ⟨k+1,?_⟩; simp only [triangle]; omega
  convex i j hij := by simp only [triangle]; omega

private theorem truncated_step (h n : Nat) (hh : h ≤ n) :
    (n+1)*(n+1-h)+h=n*(n-h)+2*n+1 := by
  let d := n-h
  have hn : n=d+h := by omega
  have hd : d+h+1-h=d+1 := by omega
  rw [hn,hd]
  simp only [Nat.add_sub_cancel,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
  omega

def truncatedQuadraticCapacity (h : Nat) : Capacity where
  value s := s*(s-h)
  mono a b hab := Nat.mul_le_mul hab (by omega)
  unbounded k := by
    refine ⟨k+h+1,?_⟩
    have hsub : k+h+1-h=k+1 := by omega
    rw [hsub]
    have hm := Nat.mul_le_mul_left (k+h+1) (show 1 ≤ k+1 by omega)
    simp only [Nat.mul_one] at hm
    omega
  convex i j hij := by
    by_cases hi : h ≤ i
    · have hsi := truncated_step h i hi
      have hsj := truncated_step h j (by omega)
      omega
    · have h0 : i-h=0 := by omega
      have h1 : i+1-h=0 := by omega
      rw [h0,h1]
      simp only [Nat.mul_zero]
      by_cases hj : h ≤ j
      · have hs := truncated_step h j hj
        omega
      · have h2 : j-h=0 := by omega
        have h3 : j+1-h=0 := by omega
        rw [h2,h3]
        simp

/-- The exact capacity used by the punctured-quadrant theorem. The maximum
with zero-truncated multiplication agrees with the integer quadratic maximum. -/
def puncturedCapacity (h : Nat) : Capacity :=
  maximumCapacity triangularCapacity (truncatedQuadraticCapacity h)

theorem punctured_root_spec (h k s : Nat) :
    root (puncturedCapacity h) k ≤ s ↔ k ≤ max (s*(s-1)/2) (s*(s-h)) := by
  have hh := root_spec (puncturedCapacity h) k s
  change root (puncturedCapacity h) k ≤ s ↔ k ≤ max (triangle s) (s*(s-h)) at hh
  simpa only [triangle_value] using hh

theorem punctured_exact_minimum (hA hB S l u : Nat)
    (hlu : l ≤ u) (huS : u ≤ S) :
    ∃ y, l ≤ y ∧ y ≤ u ∧
      cost (puncturedCapacity hA) (puncturedCapacity hB) S y =
        min (cost (puncturedCapacity hA) (puncturedCapacity hB) S
          (leftCandidate (puncturedCapacity hA) l u))
        (cost (puncturedCapacity hA) (puncturedCapacity hB) S
          (rightCandidate (puncturedCapacity hB) S l u)) ∧
      ∀ z, l ≤ z → z ≤ u →
        cost (puncturedCapacity hA) (puncturedCapacity hB) S y ≤
          cost (puncturedCapacity hA) (puncturedCapacity hB) S z :=
  exact_minimum (puncturedCapacity hA) (puncturedCapacity hB) S l u hlu huS

end Princess.ConvexCapacityConvolution
#print axioms Princess.ConvexCapacityConvolution.exact_minimum
#print axioms Princess.ConvexCapacityConvolution.punctured_exact_minimum
