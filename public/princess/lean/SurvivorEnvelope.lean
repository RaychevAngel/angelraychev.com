import CaptureRecurrence
import LadderCardinality

/-! Exact survivor-envelope certificates, interpreted as actual walk capture.
The envelope sets need not be contained in their nominal preceding beliefs.
Time `last` is zero based, so a certificate has `last+1` inspection rounds.
-/
namespace Princess.SurvivorEnvelope

open Princess.CaptureRecurrence Princess.LadderCardinality

def nominal {V : Type} (adj : V → V → Prop) (initial : Region V)
    (R : Nat → Region V) : Nat → Region V
  | 0 => initial
  | t+1 => move adj (R t)

def probe {V : Type} (adj : V → V → Prop) (initial : Region V)
    (R : Nat → Region V) (t : Nat) : Region V :=
  fun v => nominal adj initial R t v ∧ ¬ R t v

def Certificate {V : Type} (adj : V → V → Prop) (initial : Region V)
    (legal : Nat → Region V → Prop) (last : Nat) (R : Nat → Region V) : Prop :=
  Empty (R last) ∧ ∀ t, t ≤ last → legal t (probe adj initial R t)

theorem possible_subset_nominal {V : Type} (adj : V → V → Prop)
    (initial : Region V) (R : Nat → Region V) (t : Nat) :
    Subset (possible adj initial (probe adj initial R) t) (nominal adj initial R t) := by
  classical
  induction t with
  | zero => exact fun _ h => h
  | succ t ih =>
      rintro v ⟨u, ⟨hu, hprobe⟩, hedge⟩
      refine ⟨u, ?_, hedge⟩
      apply Classical.byContradiction
      intro hR
      exact hprobe ⟨ih u hu, hR⟩

theorem certificate_sound {V : Type} (adj : V → V → Prop)
    (initial : Region V) (legal : Nat → Region V → Prop) (last : Nat)
    (R : Nat → Region V) (cert : Certificate adj initial legal last R) :
    (∀ t, t ≤ last → legal t (probe adj initial R t)) ∧
      GuaranteesAt adj initial (probe adj initial R) last := by
  refine ⟨cert.2, ?_⟩
  intro v hv
  exact ⟨possible_subset_nominal adj initial R last v
    ((possible_iff_reachable adj initial (probe adj initial R) last v).mpr hv), cert.1 v⟩

theorem certificate_complete {V : Type} (adj : V → V → Prop)
    (initial : Region V) (legal : Nat → Region V → Prop)
    (downward : ∀ t A B, Subset A B → legal t B → legal t A)
    (last : Nat) (shots : Nat → Region V)
    (budget : ∀ t, t ≤ last → legal t (shots t))
    (capture : GuaranteesAt adj initial shots last) :
    ∃ R, Certificate adj initial legal last R := by
  classical
  let R : Nat → Region V := fun t v => possible adj initial shots t v ∧ ¬ shots t v
  have heq (t : Nat) : nominal adj initial R t = possible adj initial shots t := by
    cases t <;> rfl
  refine ⟨R, ?_, ?_⟩
  · intro v hv
    exact hv.2 ((guarantees_iff_belief_covered adj initial shots last).mp capture v hv.1)
  · intro t ht
    apply downward t (probe adj initial R t) (shots t) _ (budget t ht)
    intro v hv
    apply Classical.byContradiction
    intro hs
    apply hv.2
    refine ⟨?_, hs⟩
    rw [← heq t]
    exact hv.1

theorem actual_capture_iff_certificate {V : Type} (adj : V → V → Prop)
    (initial : Region V) (legal : Nat → Region V → Prop)
    (downward : ∀ t A B, Subset A B → legal t B → legal t A) (last : Nat) :
    (∃ shots : Nat → Region V,
      (∀ t, t ≤ last → legal t (shots t)) ∧ GuaranteesAt adj initial shots last) ↔
    ∃ R, Certificate adj initial legal last R := by
  constructor
  · rintro ⟨shots, budget, capture⟩
    exact certificate_complete adj initial legal downward last shots budget capture
  · rintro ⟨R, cert⟩
    exact ⟨probe adj initial R, certificate_sound adj initial legal last R cert⟩

theorem budget_capture_iff_certificate {n : Nat}
    (adj : Fin n → Fin n → Prop) (initial : Region (Fin n))
    (budget : Nat → Nat) (last : Nat) :
    (∃ shots : Nat → Region (Fin n),
      (∀ t, t ≤ last → card (shots t) ≤ budget t) ∧
      GuaranteesAt adj initial shots last) ↔
    ∃ R : Nat → Region (Fin n), Empty (R last) ∧
      ∀ t, t ≤ last → card (probe adj initial R t) ≤ budget t := by
  simpa only [Certificate] using
    (actual_capture_iff_certificate adj initial (fun t S => card S ≤ budget t)
      (fun t A B hAB hB => Nat.le_trans (card_mono A B hAB) hB) last)

/-! A Cartesian-product specialization gives the local column costs. -/

def productAdj {V W : Type} (left : V → V → Prop) (right : W → W → Prop)
    (x y : V × W) : Prop :=
  (x.2 = y.2 ∧ left x.1 y.1) ∨ (x.1 = y.1 ∧ right x.2 y.2)

def fiber {V W : Type} (S : Region (V × W)) (w : W) : Region V := fun v => S (v,w)

theorem move_fiber {V W : Type} (left : V → V → Prop) (right : W → W → Prop)
    (S : Region (V × W)) (v : V) (w : W) :
    move (productAdj left right) S (v,w) ↔
      move left (fiber S w) v ∨ ∃ u, right u w ∧ fiber S u v := by
  constructor
  · rintro ⟨⟨a,b⟩, hS, hedge⟩
    rcases hedge with ⟨hb, hleft⟩ | ⟨ha, hright⟩
    · cases hb
      exact Or.inl ⟨a, hS, hleft⟩
    · cases ha
      exact Or.inr ⟨b, hright, hS⟩
  · rintro (⟨a, hS, hedge⟩ | ⟨b, hedge, hS⟩)
    · exact ⟨(a,w), hS, Or.inl ⟨rfl, hedge⟩⟩
    · exact ⟨(v,b), hS, Or.inr ⟨rfl, hedge⟩⟩

def productList (a b : Nat) : List (Fin a × Fin b) :=
  (List.finRange b).flatMap (fun j => (List.finRange a).map (fun i => (i,j)))

noncomputable def productCard {a b : Nat} (S : Region (Fin a × Fin b)) : Nat :=
  cardOn (productList a b) S

theorem cardOn_fiber_sum {V W : Type} (xs : List V) (ys : List W)
    (S : Region (V × W)) :
    cardOn (ys.flatMap (fun j => xs.map (fun i => (i,j)))) S =
      (ys.map (fun j => cardOn xs (fiber S j))).sum := by
  induction ys with
  | nil => simp [cardOn]
  | cons y ys ih =>
      simp only [List.flatMap_cons, cardOn_append, cardOn_map, List.map_cons,
        List.sum_cons, ih]
      rfl

theorem productCard_fibers {a b : Nat} (S : Region (Fin a × Fin b)) :
    productCard S = ((List.finRange b).map (fun j => card (fiber S j))).sum :=
  cardOn_fiber_sum (List.finRange a) (List.finRange b) S

noncomputable def localCost {a b : Nat}
    (left : Fin a → Fin a → Prop) (right : Fin b → Fin b → Prop)
    (R : Nat → Region (Fin a × Fin b)) : Nat → Fin b → Nat
  | 0, j => card (fun v => ¬ R 0 (v,j))
  | t+1, j => card (fun v =>
      (move left (fiber (R t) j) v ∨ ∃ k, right k j ∧ R t (v,k)) ∧ ¬ R (t+1) (v,j))

theorem local_cost_exact {a b : Nat}
    (left : Fin a → Fin a → Prop) (right : Fin b → Fin b → Prop)
    (R : Nat → Region (Fin a × Fin b)) (t : Nat) :
    productCard (probe (productAdj left right) (fun _ => True) R t) =
      ((List.finRange b).map (localCost left right R t)).sum := by
  rw [productCard_fibers]
  congr 1
  apply List.map_congr_left
  intro j hj
  cases t with
  | zero =>
      simp only [localCost, card]
      apply cardOn_congr
      intro v hv
      simp [fiber, probe, nominal]
  | succ t =>
      simp only [localCost, card]
      apply cardOn_congr
      intro v hv
      change (move (productAdj left right) (R t) (v,j) ∧ ¬ R (t+1) (v,j)) ↔ _
      rw [move_fiber]
      rfl

theorem product_actual_capture_iff_local_costs {a b : Nat}
    (left : Fin a → Fin a → Prop) (right : Fin b → Fin b → Prop)
    (budget : Nat → Nat) (last : Nat) :
    (∃ shots : Nat → Region (Fin a × Fin b),
      (∀ t, t ≤ last → productCard (shots t) ≤ budget t) ∧
      GuaranteesAt (productAdj left right) (fun _ => True) shots last) ↔
    ∃ R : Nat → Region (Fin a × Fin b), Empty (R last) ∧
      ∀ t, t ≤ last → ((List.finRange b).map (localCost left right R t)).sum ≤ budget t := by
  have equiv := actual_capture_iff_certificate (productAdj left right) (fun _ => True)
    (fun t S => productCard S ≤ budget t) (fun t A B hAB hB =>
      Nat.le_trans (cardOn_mono _ A B (fun v _ => hAB v)) hB) last
  rw [equiv]
  constructor
  · rintro ⟨R, empty, costs⟩
    exact ⟨R, empty, fun t ht => (local_cost_exact left right R t) ▸ costs t ht⟩
  · rintro ⟨R, empty, costs⟩
    refine ⟨R, empty, ?_⟩
    intro t ht
    rw [local_cost_exact]
    exact costs t ht

end Princess.SurvivorEnvelope

#print axioms Princess.SurvivorEnvelope.actual_capture_iff_certificate
#print axioms Princess.SurvivorEnvelope.budget_capture_iff_certificate
#print axioms Princess.SurvivorEnvelope.product_actual_capture_iff_local_costs
