import VertexEquality
import FiniteExclusionRegularNine

/-! Unrestricted strict nine-vertex upper bound. Equality in the general vertex
bound would force two incoming and two outgoing arrows at every vertex; that
entire family is excluded by complete finite certificates and normalization.
This is a strictness theorem, not the sharp regular bound 30, the global budget
value M_E(18)=33, or the full finite classification. -/
namespace Delivery.FiniteExclusion.UnrestrictedNine
open FiniteGame Extremal

theorem upper (E : Graph (Fin 9)) (loopless : Loopless E) : score E ≤ 53 := by
  have bound := VertexBound.vertex_upper E loopless
  apply Classical.byContradiction
  intro greater
  have equality : score E = 9 * (9-3) := by omega
  obtain ⟨outdegree,indegree⟩ := VertexEquality.degree_two_of_equality
    (by omega : 4 ≤ 9) E loopless equality
  have strict := RegularNine.upper E loopless outdegree indegree
  omega

theorem not_vertex_equality (E : Graph (Fin 9)) (loopless : Loopless E) :
    score E ≠ 54 := by
  have bound := upper E loopless
  omega

#print axioms upper
#print axioms not_vertex_equality
end Delivery.FiniteExclusion.UnrestrictedNine
