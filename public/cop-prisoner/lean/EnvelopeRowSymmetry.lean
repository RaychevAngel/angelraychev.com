import EnvelopeSymmetry

/-! Sparse row-list automorphism checks avoid testing every ordered pair. -/
namespace Delivery.EnvelopeRowSymmetry
open FiniteGame GraphRelabeling

def edge {n : Nat} (rows : Fin n → List (Fin n)) : Graph (Fin n) :=
  fun s t => t∈rows s

theorem invariant {n : Nat} (rows : Fin n → List (Fin n))
    (σ τ : Fin n → Fin n) (left : ∀ x, τ (σ x)=x)
    (mapped : ∀ s, (rows s).map σ=rows (σ s)) :
    ∀ s t, edge rows s t ↔ edge rows (σ s) (σ t) := by
  intro s t
  change t∈rows s ↔ σ t∈rows (σ s)
  rw [←mapped s]
  constructor
  · intro member
    exact List.mem_map.mpr ⟨t,member,rfl⟩
  · intro member
    obtain ⟨x,mem,same⟩ := List.mem_map.mp member
    have equality : x=t := by simpa only [left] using congrArg τ same
    simpa only [equality] using mem

def iso {n : Nat} (rows : Fin n → List (Fin n))
    (σ τ : Fin n → Fin n) (left : ∀ x, τ (σ x)=x) (right : ∀ x, σ (τ x)=x)
    (mapped : ∀ s, (rows s).map σ=rows (σ s)) : Iso (edge rows) (edge rows) where
  toFun := σ
  invFun := τ
  left_inv := left
  right_inv := right
  edge_iff := invariant rows σ τ left mapped

theorem invariant_of_rows {n : Nat} (rows : Fin n → List (Fin n))
    (σ τ : Fin n → Fin n) (left : ∀ x, τ (σ x)=x)
    (forward : ∀ s t, t∈rows s → σ t∈rows (σ s))
    (backward : ∀ s t, t∈rows (σ s) → τ t∈rows s) :
    ∀ s t, edge rows s t ↔ edge rows (σ s) (σ t) := by
  intro s t
  constructor
  · exact forward s t
  · intro member
    simpa only [edge,left] using backward s (σ t) member

def iso_of_rows {n : Nat} (rows : Fin n → List (Fin n))
    (σ τ : Fin n → Fin n) (left : ∀ x, τ (σ x)=x) (right : ∀ x, σ (τ x)=x)
    (forward : ∀ s t, t∈rows s → σ t∈rows (σ s))
    (backward : ∀ s t, t∈rows (σ s) → τ t∈rows s) : Iso (edge rows) (edge rows) where
  toFun := σ
  invFun := τ
  left_inv := left
  right_inv := right
  edge_iff := invariant_of_rows rows σ τ left forward backward

#print axioms invariant
#print axioms invariant_of_rows
end Delivery.EnvelopeRowSymmetry
