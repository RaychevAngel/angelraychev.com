import PairCodeGeometry
import RobustTwoMove

/-! Attach vertices carrying distinct separated pair codes to the literal
two-type core. Every core-to-outside arrow is present; outside-to-core arrows
omit exactly the assigned pair; outside-to-outside arrows are optional.
The theorem allows every optional subset and retains two-move delivery. -/
namespace Delivery.PairCodeRouting
open DenseTwoType PairCodeGeometry RobustTwoMove

def Base {k q : Nat} (C : Fin q → Code k) : Graph (Sum (Vertex k) (Fin q))
  | .inl s, .inl t => DenseTwoType.edge s t
  | .inl _, .inr _ => True
  | .inr s, .inl t => ¬ (C s).Mem t
  | .inr _, .inr _ => False

def Envelope {k q : Nat} (C : Fin q → Code k) : Graph (Sum (Vertex k) (Fin q))
  | .inl s, .inl t => DenseTwoType.edge s t
  | .inl _, .inr _ => True
  | .inr s, .inl t => ¬ (C s).Mem t
  | .inr s, .inr t => s ≠ t

def Distinct {k q : Nat} (C : Fin q → Code k) : Prop :=
  ∀ x y, (∀ u, (C x).Mem u ↔ (C y).Mem u) → x = y

theorem subset {k q : Nat} (C : Fin q → Code k) : Subgraph (Base C) (Envelope C) := by
  intro s t h
  cases s <;> cases t <;> first | exact h | exact h.elim

theorem loopless {k q : Nat} (C : Fin q → Code k) : Extremal.Loopless (Envelope C) := by
  intro s h
  cases s with
  | inl s => exact h.1 rfl
  | inr s => exact h rfl

theorem witnesses {k q : Nat} (hk : 5 ≤ k) (C : Fin q → Code k)
    (distinct : Distinct C) : Witnesses (Base C) (Envelope C) := by
  classical
  intro s t c different initial absent
  cases s with
  | inl s =>
    cases t with
    | inr t => exact False.elim (absent trivial)
    | inl t =>
      have pair : missing s t := Classical.byContradiction (fun h =>
        absent ⟨fun e => different (congrArg Sum.inl e),h⟩)
      cases c with
      | inl c =>
        obtain ⟨u,cu,su,ut⟩ := safe_neighbor hk pair
          (fun e => initial (congrArg Sum.inl e))
        refine ⟨.inl u,⟨fun e => ut (e ▸ pair),su⟩,⟨fun e => su (e ▸ pair),ut⟩,?_,?_⟩
        · intro e
          have same := Sum.inl.inj e
          exact missing_loopless c (same ▸ cu)
        · intro edge; exact edge.2 cu
      | inr c =>
        obtain ⟨u,cu,su,ut⟩ := block_escape (C c) pair
        exact ⟨.inl u,⟨fun e => ut (e ▸ pair),su⟩,⟨fun e => su (e ▸ pair),ut⟩,
          (by intro h; cases h),fun edge => edge cu⟩
  | inr s =>
    cases t with
    | inl t =>
      have target : (C s).Mem t := Classical.byContradiction absent
      cases c with
      | inl c =>
        obtain ⟨u,cu,su,ut⟩ := row_target_escape hk (C s) target c
        refine ⟨.inl u,su,⟨?_,ut⟩,?_,?_⟩
        · intro same; subst u; exact su target
        · intro e; exact missing_loopless c ((Sum.inl.inj e) ▸ cu)
        · intro edge; exact edge.2 cu
      | inr c =>
        have cd : ¬ ∀ u, (C c).Mem u ↔ (C s).Mem u :=
          fun h => initial (congrArg Sum.inr (distinct c s h))
        obtain ⟨u,cu,su,ut⟩ := code_target_escape (C s) (C c) target cd
        refine ⟨.inl u,su,⟨?_,ut⟩,(by intro h; cases h),fun edge => edge cu⟩
        intro same; subst u; exact su target
    | inr t =>
      cases c with
      | inl c =>
        obtain ⟨u,cu,su⟩ := row_escape hk (C s) c
        refine ⟨.inl u,su,trivial,?_,?_⟩
        · intro e; exact missing_loopless c ((Sum.inl.inj e) ▸ cu)
        · intro edge; exact edge.2 cu
      | inr c =>
        have cd : ¬ ∀ u, (C c).Mem u ↔ (C s).Mem u :=
          fun h => initial (congrArg Sum.inr (distinct c s h))
        obtain ⟨u,cu,su⟩ := difference (C c) (C s) cd
        exact ⟨.inl u,su,trivial,(by intro h; cases h),fun edge => edge cu⟩

theorem two_move {k q : Nat} (hk : 5 ≤ k) (C : Fin q → Code k)
    (distinct : Distinct C) (G : Graph (Sum (Vertex k) (Fin q)))
    (lower : Subgraph (Base C) G) (upper : Subgraph G (Envelope C))
    (s t : Sum (Vertex k) (Fin q)) : Universal G t 2 s :=
  envelope_universal lower upper (witnesses hk C distinct) s t

#print axioms witnesses
#print axioms two_move
end Delivery.PairCodeRouting
