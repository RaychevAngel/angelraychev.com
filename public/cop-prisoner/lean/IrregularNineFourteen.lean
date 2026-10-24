import IrregularNine14P00
import IrregularNine14P01
import IrregularNine14P02
import IrregularNine14P03
import IrregularNine14P04
import IrregularNine14P05
import IrregularNine14P06
import IrregularNine14P07
import IrregularNine14P08
import IrregularNine14P09
import IrregularNine14P10
import IrregularNine14Profile

namespace Delivery.IrregularNine14
open FiniteGame Extremal RowPrefix

theorem canonical_upper (p : Fin 11) : Upper (D p) (R p) [] 13 := by
  rcases p with ⟨i,hi⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact P00.canonical_upper
  · exact P01.canonical_upper
  · exact P02.canonical_upper
  · exact P03.canonical_upper
  · exact P04.canonical_upper
  · exact P05.canonical_upper
  · exact P06.canonical_upper
  · exact P07.canonical_upper
  · exact P08.canonical_upper
  · exact P09.canonical_upper
  · exact P10.canonical_upper

/-- Complete positive-degree nine-vertex upper bound at budget fourteen.
All eleven degree profiles, every row branch, and all loss certificates are checked. -/
theorem positive_upper (E : Graph (Fin 9)) (loopless : Loopless E)
    (budget : arcCount E=14)
    (positiveOut : ∀ x, 1≤SparseSupport.outdegree E x)
    (positiveIn : ∀ x, 1≤SparseSupport.indegree E x) : score E≤13 := by
  by_cases small : score E≤13
  · exact small
  · obtain ⟨p,F,⟨iso⟩,prescribed⟩ :=
      IrregularNine14Profile.normalize E loopless budget positiveOut positiveIn (by omega)
    have bound := canonical_upper p F prescribed (by intro s h; simp at h)
    rw [GraphRelabeling.score_eq iso]
    exact bound

#print axioms canonical_upper
#print axioms positive_upper
end Delivery.IrregularNine14
