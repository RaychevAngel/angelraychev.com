import Std

/-!
Exact interval reachability for two counters with a shared daily budget.
This is the algebraic middle-region lemma, not a formalization of the
rectangle's geometric profile theorem or the complete search problem.
The rates may vary with time; their sum is the fixed integer `w`.
-/

namespace Princess.MiddleIntervalTransfer

def InBand (L U a b : Int) : Prop :=
  L ≤ a ∧ a ≤ U ∧ L ≤ b ∧ b ≤ U

def IntervalState (L U S lo hi a b : Int) : Prop :=
  InBand L U a b ∧ a + b = S ∧ lo ≤ a ∧ a ≤ hi

def Step (L U m w r a b a' b' : Int) : Prop :=
  ∃ p : Int, 0 ≤ p ∧ p ≤ m ∧
    a' = a + r - p ∧ b' = b + (w - r) - (m - p) ∧ InBand L U a' b'

/-- An endpoint in the propagated interval has an actual predecessor. -/
theorem interval_predecessor
    (L U S lo hi m w r a' b' : Int)
    (hLU : L ≤ U) (hS : 2 * L ≤ S ∧ S ≤ 2 * U)
    (hlohi : lo ≤ hi) (hloU : lo ≤ U) (hLhi : L ≤ hi)
    (hloS : lo ≤ S - L) (hShi : S - U ≤ hi)
    (hr : 0 ≤ r ∧ r ≤ m) (hs : 0 ≤ w-r ∧ w-r ≤ m)
    (hn : IntervalState L U (S+w-m) (lo+r-m) (hi+r) a' b') :
    ∃ a b, IntervalState L U S lo hi a b ∧ Step L U m w r a b a' b' := by
  rcases hn with ⟨⟨hLa, haU, hLb, hbU⟩, hsum, hlow, hhigh⟩
  let a := max (max L (S-U)) (max lo (a'-r))
  have haL : L ≤ a := by dsimp [a]; omega
  have haS : S-U ≤ a := by dsimp [a]; omega
  have halo : lo ≤ a := by dsimp [a]; omega
  have har : a'-r ≤ a := by dsimp [a]; omega
  have haU' : a ≤ U := by dsimp [a]; omega
  have haS' : a ≤ S-L := by dsimp [a]; omega
  have hahi : a ≤ hi := by dsimp [a]; omega
  have harp : a ≤ a'-r+m := by dsimp [a]; omega
  refine ⟨a, S-a, ?_, ?_⟩
  · unfold IntervalState InBand
    omega
  · refine ⟨a+r-a', ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try unfold InBand) <;> omega

def accumulated (r : Nat → Int) : Nat → Int
  | 0 => 0
  | t+1 => accumulated r t + r t

def total (A B w m : Int) (t : Nat) : Int :=
  A+B+(t : Int)*(w-m)

inductive Reach (L U m w A B : Int) (r : Nat → Int) : Nat → Int → Int → Prop
  | initial : Reach L U m w A B r 0 A B
  | next {t a b a' b'} : Reach L U m w A B r t a b →
      Step L U m w (r t) a b a' b' → Reach L U m w A B r (t+1) a' b'

theorem accumulated_bounds (m w : Int) (r : Nat → Int)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ m)
    (hs : ∀ t, 0 ≤ w-r t ∧ w-r t ≤ m) (t : Nat) :
    0 ≤ accumulated r t ∧ accumulated r t ≤ (t : Int)*m ∧
    0 ≤ (t : Int)*w-accumulated r t ∧
    (t : Int)*w-accumulated r t ≤ (t : Int)*m := by
  induction t with
  | zero => simp [accumulated]
  | succ t ih =>
    have hrt := hr t
    have hst := hs t
    simp only [accumulated, Int.natCast_add, Int.ofNat_one, Int.add_mul, Int.one_mul]
    omega

theorem reach_interval (L U m w A B : Int) (r : Nat → Int)
    (hAB : InBand L U A B)
    {t : Nat} {a b : Int} (h : Reach L U m w A B r t a b) :
    IntervalState L U (total A B w m t)
      (A+accumulated r t-(t : Int)*m) (A+accumulated r t) a b := by
  induction h with
  | initial =>
    simpa [IntervalState, total, accumulated] using hAB
  | @next t a b a' b' h step ih =>
    rcases ih with ⟨hband, hsum, hlo, hhi⟩
    rcases step with ⟨p, hp0, hpm, ha, hb, hband'⟩
    refine ⟨hband', ?_, ?_, ?_⟩
    all_goals
      simp only [total, accumulated, Int.natCast_add, Int.ofNat_one,
        Int.add_mul, Int.one_mul] at *
      omega

/-- Every endpoint in the interval is reachable, retaining physical quota
allocations and all intermediate band restrictions. -/
theorem interval_reach (L U m w A B : Int) (r : Nat → Int)
    (hAB : InBand L U A B)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ m)
    (hs : ∀ t, 0 ≤ w-r t ∧ w-r t ≤ m)
    (t : Nat)
    (hS : ∀ j, j ≤ t → 2*L ≤ total A B w m j ∧ total A B w m j ≤ 2*U)
    (a b : Int)
    (hend : IntervalState L U (total A B w m t)
      (A+accumulated r t-(t : Int)*m) (A+accumulated r t) a b) :
    Reach L U m w A B r t a b := by
  induction t generalizing a b with
  | zero =>
    have ha : a=A := by simp [IntervalState, accumulated] at hend; omega
    have hb : b=B := by simp [IntervalState, total, accumulated] at hend; omega
    subst a; subst b
    exact Reach.initial
  | succ t ih =>
    have hc := accumulated_bounds m w r hr hs t
    have hst := hS t (by omega)
    have hAB' := hAB
    unfold InBand at hAB'
    have hn : IntervalState L U (total A B w m t+w-m)
        (A+accumulated r t-(t : Int)*m+r t-m)
        (A+accumulated r t+r t) a b := by
      rcases hend with ⟨hb, he, hl, hu⟩
      refine ⟨hb, ?_, ?_, ?_⟩
      all_goals
        simp only [total, accumulated, Int.natCast_add, Int.ofNat_one,
          Int.add_mul, Int.one_mul] at *
        omega
    have hp := interval_predecessor L U (total A B w m t)
      (A+accumulated r t-(t : Int)*m) (A+accumulated r t)
      m w (r t) a b
      (by omega) hst (by omega) (by omega) (by omega)
      (by unfold total; rw [Int.mul_sub]; omega)
      (by unfold total; rw [Int.mul_sub]; omega)
      (hr t) (hs t) hn
    rcases hp with ⟨a0,b0,hprev,hstep⟩
    exact Reach.next (ih (fun j hj => hS j (by omega)) a0 b0 hprev) hstep

theorem total_stays_in_band (L U m w A B : Int) (t : Nat)
    (hAB : InBand L U A B)
    (hend : 2*L ≤ total A B w m t ∧ total A B w m t ≤ 2*U) :
    ∀ j, j ≤ t → 2*L ≤ total A B w m j ∧ total A B w m j ≤ 2*U := by
  intro j hj
  have hj0 : (0 : Int) ≤ (j : Int) := by omega
  have hjt : (j : Int) ≤ (t : Int) := by omega
  unfold total at *
  unfold InBand at hAB
  by_cases h : 0 ≤ w-m
  · have h0 := Int.mul_nonneg hj0 h
    have h1 := Int.mul_le_mul_of_nonneg_right hjt h
    omega
  · have h0 := Int.mul_nonpos_of_nonneg_of_nonpos hj0 (by omega : w-m ≤ 0)
    have h1 := Int.mul_le_mul_of_nonpos_right hjt (by omega : w-m ≤ 0)
    omega

/-- Endpoint conditions alone characterize all reachable pairs. -/
theorem exact_interval_iff (L U m w A B : Int) (r : Nat → Int)
    (hAB : InBand L U A B)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ m)
    (hs : ∀ t, 0 ≤ w-r t ∧ w-r t ≤ m)
    (t : Nat) (a b : Int) :
    Reach L U m w A B r t a b ↔
      IntervalState L U (total A B w m t)
        (A+accumulated r t-(t : Int)*m) (A+accumulated r t) a b := by
  constructor
  · exact reach_interval L U m w A B r hAB
  · intro hend
    have hsum : 2*L ≤ total A B w m t ∧ total A B w m t ≤ 2*U := by
      rcases hend with ⟨⟨h1,h2,h3,h4⟩,h5,h6,h7⟩
      omega
    exact interval_reach L U m w A B r hAB hr hs t
      (total_stays_in_band L U m w A B t hAB hsum) a b hend

def alternatingRate (b : Int) (z t : Nat) : Int :=
  b + ((t+z)%2 : Nat)

theorem alternating_accumulated (b : Int) (z : Nat) (hz : z ≤ 1) (t : Nat) :
    accumulated (alternatingRate b z) t = (t : Int)*b + (((t+z)/2 : Nat) : Int) := by
  induction t with
  | zero => simp [accumulated]; omega
  | succ t ih =>
    simp only [accumulated, ih, alternatingRate, Int.natCast_add,
      Int.ofNat_one, Int.add_mul, Int.one_mul]
    omega

/-- The alternating-rate formula used by the odd-rectangle middle region.
The rectangle's geometric safe-band hypotheses are supplied externally. -/
theorem odd_middle_interval_iff (L U m b A B : Int)
    (hb : 1 ≤ b) (hm : b+1 ≤ m) (z : Nat) (hz : z ≤ 1)
    (hAB : InBand L U A B) (t : Nat) (a c : Int) :
    Reach L U m (2*b+1) A B (alternatingRate b z) t a c ↔
      IntervalState L U (A+B+(t : Int)*(2*b+1-m))
        (A+(t : Int)*b+(((t+z)/2 : Nat) : Int)-(t : Int)*m)
        (A+(t : Int)*b+(((t+z)/2 : Nat) : Int)) a c := by
  have hr : ∀ t, 0 ≤ alternatingRate b z t ∧ alternatingRate b z t ≤ m := by
    intro t
    unfold alternatingRate
    omega
  have hs : ∀ t, 0 ≤ (2*b+1)-alternatingRate b z t ∧
      (2*b+1)-alternatingRate b z t ≤ m := by
    intro t
    unfold alternatingRate
    omega
  have h := exact_interval_iff L U m (2*b+1) A B (alternatingRate b z)
    hAB hr hs t a c
  rw [alternating_accumulated b z hz t] at h
  simpa only [total, Int.add_assoc] using h

#print axioms exact_interval_iff
#print axioms odd_middle_interval_iff

end Princess.MiddleIntervalTransfer
