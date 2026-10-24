import RegularNineSharp2x2x2x3
import RegularNineSharp2x2x5
import RegularNineSharp2x3x4
import RegularNineSharp2x7
import RegularNineSharp3x3x3
import RegularNineSharp3x6
import RegularNineSharp4x5
import FiniteExclusionHamiltonianSharp
import FiniteExclusionRegularNine

/-! The sharp maximum for all loopless nine-vertex graphs with two incoming
and two outgoing arrows per vertex. All eight first-factor cycle types are
covered. No Hamiltonicity or supplied factorization premise remains. -/
namespace Delivery.FiniteExclusion.RegularNineSharp
open FiniteGame Extremal DenseCombinatorics

theorem canonical_upper (cycle : Nine.CycleType) (b : Assignment 9)
    (valid : Valid (Nine.first cycle) b) :
    score (edgeOf (Nine.first cycle) b)≤30 := by
  cases cycle with
  | c2223 => exact Sharp2x2x2x3.upper b valid
  | c225 => exact Sharp2x2x5.upper b valid
  | c234 => exact Sharp2x3x4.upper b valid
  | c27 => exact Sharp2x7.upper b valid
  | c333 => exact Sharp3x3x3.upper b valid
  | c36 => exact Sharp3x6.upper b valid
  | c45 => exact Sharp4x5.upper b valid
  | c9 => exact Thirty9Minimum.upper b valid

theorem upper (E : Graph (Fin 9)) (loopless : Loopless E)
    (outdegree : ∀ s, card (E s)=2)
    (indegree : ∀ t, card (fun s => E s t)=2) : score E≤30 := by
  obtain ⟨a,b,ainj,binj,degrees,edges⟩ :=
    FiniteHall.loopless_two_permutation_factors E loopless outdegree indegree
  obtain ⟨cycle,⟨conjugacy⟩⟩ :=
    CycleNormalizationNine.canonicalize a ainj (fun s => (degrees s).1)
  have valid : Valid a b := ⟨binj,fun s => (degrees s).2⟩
  have same : E=edgeOf a b := funext fun s => funext fun t => propext (edges s t)
  rw [same,conjugacy.score_eq b]
  exact canonical_upper cycle (conjugacy.push b) (conjugacy.valid_push b valid)

theorem attained : ∃ E : Graph (Fin 9), Loopless E ∧
    (∀ s, card (E s)=2) ∧ (∀ t, card (fun s => E s t)=2) ∧ score E=30 := by
  refine ⟨SparseWitness9.edge,SparseWitness9.loopless,?_,?_,SparseWitness9.exact_score⟩
  · intro s
    rw [card_eq]
    revert s
    decide +kernel
  · intro t
    rw [card_eq]
    revert t
    decide +kernel

theorem maximum :
    (∀ E : Graph (Fin 9), Loopless E → (∀ s, card (E s)=2) →
      (∀ t, card (fun s => E s t)=2) → score E≤30) ∧
    ∃ E : Graph (Fin 9), Loopless E ∧
      (∀ s, card (E s)=2) ∧ (∀ t, card (fun s => E s t)=2) ∧ score E=30 :=
  ⟨upper,attained⟩

#print axioms upper
#print axioms maximum
end Delivery.FiniteExclusion.RegularNineSharp
