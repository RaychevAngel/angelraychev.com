import FiniteExclusionThirtyNineHamiltonian
import FiniteExclusionHamiltonianAttainer

/-! Exact maximum for the nine-vertex Hamiltonian two-factor family. The family
is explicit: a graph is isomorphic to a directed Hamiltonian cycle together
with a disjoint loopless permutation. This is narrower than all regular
nine-vertex graphs, and narrower than all graphs with eighteen arcs. -/
namespace Delivery.FiniteExclusion.HamiltonianSharp
open FiniteGame Extremal

def Family (E : Graph (Fin 9)) : Prop :=
  ∃ b : Assignment 9, Valid Thirty9Minimum.a b ∧
    Nonempty (GraphRelabeling.Iso E (edgeOf Thirty9Minimum.a b))

theorem upper (E : Graph (Fin 9)) (member : Family E) : score E ≤ 30 := by
  obtain ⟨b,valid,⟨iso⟩⟩ := member
  rw [GraphRelabeling.score_eq iso]
  exact Thirty9Minimum.upper b valid

theorem arcs (E : Graph (Fin 9)) (member : Family E) : arcCount E = 18 := by
  obtain ⟨b,valid,⟨iso⟩⟩ := member
  rw [GraphRelabeling.arcCount_eq iso]
  exact nine_factor_arcs _ _ valid

theorem attained : ∃ E : Graph (Fin 9), Family E ∧ score E = 30 := by
  exact ⟨SparseWitness9.edge,
    ⟨HamiltonianAttainer.second,HamiltonianAttainer.valid,⟨HamiltonianAttainer.witnessIso⟩⟩,
    SparseWitness9.exact_score⟩

theorem maximum :
    (∀ E : Graph (Fin 9), Family E → score E ≤ 30) ∧
    ∃ E : Graph (Fin 9), Family E ∧ score E = 30 := ⟨upper,attained⟩

#print axioms maximum
end Delivery.FiniteExclusion.HamiltonianSharp
