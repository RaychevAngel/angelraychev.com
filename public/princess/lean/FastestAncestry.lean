import Std

/-!
The new ancestry argument for two shared-budget deficit recurrences.

`InverseSystem` lists the monotonicity and two inverse-concentration
inequalities used in the ordinary odd-rectangle proof. They are explicit
hypotheses, not axioms or conclusions hidden in a search predicate. The
root formulas, rectangle geometry, last-tie clock, and physical midpoint
reduction are not instantiated in this module.
-/

namespace Princess.FastestAncestry

structure InverseSystem where
  zero : Nat → Nat
  one : Nat → Nat
  limit : Nat
  mono_zero : ∀ a b, a ≤ b → b ≤ limit → zero a ≤ zero b
  mono_one : ∀ a b, a ≤ b → b ≤ limit → one a ≤ one b
  small_one : ∀ a, a < 2 → one a = 0
  concentrate_zero : ∀ x y, x+y ≤ limit → zero y + one x ≤ zero (x+y)
  concentrate_one : ∀ x y, x+y ≤ limit → 2 ≤ x →
    zero y + one x ≤ one (x+y)

def Step (I : InverseSystem) (m x y x' y' : Nat) : Prop :=
  ∃ p q, p+q ≤ m ∧ x' = I.zero (y+q) ∧ y' = I.one (x+p)

def High (A B x y : Nat) : Prop := min A B < x+y

/-- `true` means the original primary cohort currently occupies color one. -/
def Secondary (p : Bool) (x y : Nat) : Nat := if p then x else y

def Dominant (p : Bool) (A B : Nat) : Prop := if p then A < B else B < A

theorem step_individual (I : InverseSystem) (m A B x y x' y' : Nat)
    (hx : x ≤ A) (hy : y ≤ B) (hd : max A B + m ≤ I.limit)
    (hs : Step I m x y x' y') :
    x' ≤ I.zero (B+m) ∧ y' ≤ I.one (A+m) := by
  rcases hs with ⟨p,q,hpq,rfl,rfl⟩
  constructor
  · apply I.mono_zero <;> omega
  · apply I.mono_one <;> omega

theorem step_concentrated (I : InverseSystem) (m A B x y x' y' : Nat)
    (hx : x ≤ A) (hy : y ≤ B) (ht : x+y ≤ max A B)
    (hd : max A B + m ≤ I.limit) (hs : Step I m x y x' y') :
    x'+y' ≤ max (I.zero (B+m)) (I.one (A+m)) := by
  have hi := step_individual I m A B x y x' y' hx hy hd hs
  rcases hs with ⟨p,q,hpq,rfl,rfl⟩
  by_cases hAB : A ≤ B
  · have hc := I.concentrate_zero (x+p) (y+q) (by omega)
    have hm := I.mono_zero (x+p+(y+q)) (B+m) (by omega) (by omega)
    omega
  · by_cases hpos : 2 ≤ x+p
    · have hc := I.concentrate_one (x+p) (y+q) (by omega) hpos
      have hm := I.mono_one (x+p+(y+q)) (A+m) (by omega) (by omega)
      omega
    · have hz := I.small_one (x+p) (by omega)
      omega

/-- A mixed successor of a low-total state is low-total again. -/
theorem low_total_persists (I : InverseSystem) (m A B x y x' y' : Nat)
    (ht : x+y ≤ min A B) (hd : max A B + m ≤ I.limit)
    (hs : Step I m x y x' y') (hy' : 0 < y') :
    x'+y' ≤ min (I.zero (B+m)) (I.one (A+m)) := by
  rcases hs with ⟨p,q,hpq,rfl,rfl⟩
  have hpos : 2 ≤ x+p := by
    by_cases h : x+p < 2
    · have hz := I.small_one (x+p) h
      omega
    · omega
  have h0 := I.concentrate_zero (x+p) (y+q) (by omega)
  have h1 := I.concentrate_one (x+p) (y+q) (by omega) hpos
  have hm0 := I.mono_zero (x+p+(y+q)) (B+m) (by omega) (by omega)
  have hm1 := I.mono_one (x+p+(y+q)) (A+m) (by omega) (by omega)
  omega

/-- A pure high-total state cannot have its small secondary as its only
nonzero coordinate. This handles rebirth after an intervening pure state. -/
theorem pure_high_primary (A B C x y : Nat) (p : Bool)
    (hx : x ≤ A) (hy : y ≤ B) (hC : C < min A B)
    (hsec : Secondary p x y ≤ C) (hpure : x=0 ∨ y=0)
    (hhigh : High A B x y) : Dominant p A B := by
  cases p <;> simp only [Secondary, Dominant, Bool.false_eq_true, if_false,
    if_true] at * <;> unfold High at hhigh <;> omega

/-- The primary color flips on movement. A high mixed successor must keep
the same original primary as its fastest solo ancestry. -/
theorem high_primary_step (I : InverseSystem) (m A B C x y x' y' : Nat)
    (p : Bool) (hx : x ≤ A) (hy : y ≤ B)
    (ht : x+y ≤ max A B) (hd : max A B+m ≤ I.limit)
    (hs : Step I m x y x' y')
    (hC : C < min (I.zero (B+m)) (I.one (A+m)))
    (hsec : Secondary (!p) x' y' ≤ C)
    (hprev : High A B x y → Dominant p A B)
    (hhigh : High (I.zero (B+m)) (I.one (A+m)) x' y') :
    Dominant (!p) (I.zero (B+m)) (I.one (A+m)) := by
  have hi := step_individual I m A B x y x' y' hx hy hd hs
  by_cases hpure : x'=0 ∨ y'=0
  · exact pure_high_primary _ _ C x' y' (!p) hi.1 hi.2 hC hsec hpure hhigh
  have hypos : 0 < y' := by omega
  have hold : High A B x y := by
    by_cases h : x+y ≤ min A B
    · have hh := low_total_persists I m A B x y x' y' h hd hs hypos
      unfold High at hhigh
      omega
    · unfold High
      omega
  have hdom := hprev hold
  rcases hs with ⟨r,s,hrs,rfl,rfl⟩
  have hpos : 2 ≤ x+r := by
    by_cases h : x+r < 2
    · have hz := I.small_one (x+r) h
      omega
    · omega
  cases p
  · simp only [Dominant, Bool.false_eq_true, if_false] at hdom
    have hc := I.concentrate_one (x+r) (y+s) (by omega) hpos
    have hm := I.mono_one (x+r+(y+s)) (A+m) (by omega) (by omega)
    simp only [Bool.not_false, Dominant, if_true]
    unfold High at hhigh
    omega
  · simp only [Dominant, if_true] at hdom
    have hc := I.concentrate_zero (x+r) (y+s) (by omega)
    have hm := I.mono_zero (x+r+(y+s)) (B+m) (by omega) (by omega)
    simp only [Bool.not_true, Dominant, Bool.false_eq_true, if_false]
    unfold High at hhigh
    omega

def Phase (p : Bool) : Nat → Bool
  | 0 => p
  | t+1 => !(Phase p t)

/-- A trajectory starts at a pure reset state and follows actual shared
quota transitions. Capacities follow their full-budget scalar recurrence.
The secondary bound is an external fresh-cohort estimate, not an ancestry
or optimality assumption. -/
theorem trace_high_primary (I : InverseSystem) (m C T : Nat) (p : Bool)
    (A B x y : Nat → Nat)
    (hA : ∀ t, t<T → A (t+1)=I.zero (B t+m))
    (hB : ∀ t, t<T → B (t+1)=I.one (A t+m))
    (hd : ∀ t, t<T → max (A t) (B t)+m ≤ I.limit)
    (hs : ∀ t, t<T → Step I m (x t) (y t) (x (t+1)) (y (t+1)))
    (hC : ∀ t, t≤T → C < min (A t) (B t))
    (hsec : ∀ t, t≤T → Secondary (Phase p t) (x t) (y t) ≤ C)
    (hx0 : x 0 ≤ A 0) (hy0 : y 0 ≤ B 0)
    (hpure : x 0=0 ∨ y 0=0) :
    ∀ t, t≤T → x t≤A t ∧ y t≤B t ∧ x t+y t≤max (A t) (B t) ∧
      (High (A t) (B t) (x t) (y t) → Dominant (Phase p t) (A t) (B t)) := by
  intro t ht
  induction t with
  | zero =>
    refine ⟨hx0,hy0,?_,?_⟩
    · omega
    · intro hh
      exact pure_high_primary (A 0) (B 0) C (x 0) (y 0) p hx0 hy0
        (hC 0 (by omega)) (hsec 0 (by omega)) hpure hh
  | succ t ih =>
    have htt : t<T := by omega
    obtain ⟨hx,hy,htot,hdom⟩ := ih (by omega)
    have hst := hs t htt
    have hdt := hd t htt
    have hi := step_individual I m (A t) (B t) (x t) (y t)
      (x (t+1)) (y (t+1)) hx hy hdt hst
    have hc := step_concentrated I m (A t) (B t) (x t) (y t)
      (x (t+1)) (y (t+1)) hx hy htot hdt hst
    rw [←hA t htt, ←hB t htt] at hi hc
    refine ⟨hi.1,hi.2,hc,?_⟩
    intro hh
    have hp := high_primary_step I m (A t) (B t) C (x t) (y t)
      (x (t+1)) (y (t+1)) (Phase p t) hx hy htot hdt hst
      (by rw [←hA t htt, ←hB t htt]; exact hC (t+1) ht)
      (hsec (t+1) ht) hdom
      (by rw [←hA t htt, ←hB t htt]; exact hh)
    rw [←hA t htt, ←hB t htt] at hp
    exact hp

def CutCost (E M x y u v : Nat) : Nat := (E-(x+u))+(M-(y+v))

/-- Two pure-reset histories cannot improve a feasible midpoint below both
the scalar residual sum and the untouched-secondary lower bound. -/
theorem midpoint_obstruction (E M A B C m x y u v : Nat) (p q : Bool)
    (ht : x+y ≤ max A B) (hu : u+v ≤ max A B)
    (hp : High A B x y → Dominant p A B)
    (hq : High A B u v → Dominant q A B)
    (hsec : Secondary p x y ≤ C) (hsec' : Secondary q u v ≤ C)
    (hscalar : m < E+M-(A+B)) (hsmall : m < min E M-2*C) :
    m < CutCost E M x y u v := by
  by_cases hlow : x+y ≤ min A B
  · unfold CutCost
    omega
  by_cases hlow' : u+v ≤ min A B
  · unfold CutCost
    omega
  have hp' := hp (by unfold High; omega)
  have hq' := hq (by unfold High; omega)
  cases p <;> cases q <;>
    simp only [Secondary, Dominant, Bool.false_eq_true, if_false, if_true] at * <;>
    unfold CutCost <;> omega

/-- Composed result for two independent half-histories from the same pure
reset layer. No high-primary conclusion is supplied as a hypothesis. -/
theorem reset_midpoint_obstruction (I : InverseSystem) (m C T E M : Nat)
    (p q : Bool) (A B x y u v : Nat → Nat)
    (hA : ∀ t, t<T → A (t+1)=I.zero (B t+m))
    (hB : ∀ t, t<T → B (t+1)=I.one (A t+m))
    (hd : ∀ t, t<T → max (A t) (B t)+m ≤ I.limit)
    (hxy : ∀ t, t<T → Step I m (x t) (y t) (x (t+1)) (y (t+1)))
    (huv : ∀ t, t<T → Step I m (u t) (v t) (u (t+1)) (v (t+1)))
    (hC : ∀ t, t≤T → C < min (A t) (B t))
    (hsec : ∀ t, t≤T → Secondary (Phase p t) (x t) (y t) ≤ C)
    (hsec' : ∀ t, t≤T → Secondary (Phase q t) (u t) (v t) ≤ C)
    (hx0 : x 0 ≤ A 0) (hy0 : y 0 ≤ B 0)
    (hu0 : u 0 ≤ A 0) (hv0 : v 0 ≤ B 0)
    (hpure : x 0=0 ∨ y 0=0) (hpure' : u 0=0 ∨ v 0=0)
    (hscalar : m < E+M-(A T+B T)) (hsmall : m < min E M-2*C) :
    m < CutCost E M (x T) (y T) (u T) (v T) := by
  have hfirst := trace_high_primary I m C T p A B x y hA hB hd hxy hC hsec
    hx0 hy0 hpure T (Nat.le_refl _)
  have hsecond := trace_high_primary I m C T q A B u v hA hB hd huv hC hsec'
    hu0 hv0 hpure' T (Nat.le_refl _)
  exact midpoint_obstruction E M (A T) (B T) C m (x T) (y T) (u T) (v T)
    (Phase p T) (Phase q T) hfirst.2.2.1 hsecond.2.2.1
    hfirst.2.2.2 hsecond.2.2.2 (hsec T (Nat.le_refl _))
    (hsec' T (Nat.le_refl _)) hscalar hsmall

#print axioms low_total_persists
#print axioms trace_high_primary
#print axioms midpoint_obstruction
#print axioms reset_midpoint_obstruction

end Princess.FastestAncestry
