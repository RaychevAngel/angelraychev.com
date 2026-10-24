import FiniteHall
import CycleNormalizationNine

/-! An unconditional, exhaustive exclusion for all nine-vertex loopless
2-in/2-out digraphs. Factorization, cycle normalization, relabeling, complete
second-factor branching, all pruning, and all surviving losing leaves are
proved in Lean. This is the no-universal-regular-graph theorem (score≤53),
not the stronger separately recorded sharp regular maximum30. -/
namespace Delivery.FiniteExclusion.RegularNine
open FiniteGame Extremal DenseCombinatorics

theorem upper (E : Graph (Fin 9)) (loopless : Loopless E)
    (outdegree : ∀ s, card (E s) = 2)
    (indegree : ∀ t, card (fun s => E s t) = 2) : score E ≤ 53 := by
  obtain ⟨a,b,ainj,binj,degrees,edges⟩ :=
    FiniteHall.loopless_two_permutation_factors E loopless outdegree indegree
  obtain ⟨cycle,⟨conjugacy⟩⟩ :=
    CycleNormalizationNine.canonicalize a ainj (fun s => (degrees s).1)
  have valid : Valid a b := ⟨binj,fun s => (degrees s).2⟩
  have same : E = edgeOf a b := by
    funext s t
    exact propext (edges s t)
  rw [same,conjugacy.score_eq b]
  exact Nine.upper cycle (conjugacy.push b) (conjugacy.valid_push b valid)

theorem exact_budget (E : Graph (Fin 9)) (loopless : Loopless E)
    (outdegree : ∀ s, card (E s) = 2)
    (indegree : ∀ t, card (fun s => E s t) = 2) :
    arcCount E = 18 ∧ missingCount E = 54 := by
  obtain ⟨a,b,_,binj,degrees,edges⟩ :=
    FiniteHall.loopless_two_permutation_factors E loopless outdegree indegree
  have valid : Valid a b := ⟨binj,fun s => (degrees s).2⟩
  have same : E = edgeOf a b := by
    funext s t
    exact propext (edges s t)
  rw [same]
  exact ⟨nine_factor_arcs a b valid,
    nine_factor_missing a b (fun s => (degrees s).1) valid⟩

/-- Some genuine missing pair fails against a permitted cop start/policy.
The statement ranges over every graph of the specified degrees. -/
theorem not_all_guaranteed (E : Graph (Fin 9)) (loopless : Loopless E)
    (outdegree : ∀ s, card (E s) = 2)
    (indegree : ∀ t, card (fun s => E s t) = 2) :
    ¬ (∀ s t, s ≠ t → ¬ E s t → Guaranteed E s t) := by
  intro all
  have bound := upper E loopless outdegree indegree
  have budget := exact_budget E loopless outdegree indegree
  have score := score_eq_missing E all
  omega

#print axioms upper
#print axioms exact_budget
#print axioms not_all_guaranteed
end Delivery.FiniteExclusion.RegularNine
