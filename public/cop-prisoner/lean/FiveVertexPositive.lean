import FiveVertexPositive09
import FiveVertexPositive10
import FiveVertexPositive11
import FiveVertexPositive12
import FiveVertexPositive13
import FiveVertexPositive14

namespace Delivery.FiveVertexPositive
open FiniteGame Extremal SparseSupport
theorem upper (E : Graph (Fin 5)) (loopless : Loopless E)
    (budget : 9≤arcCount E ∧ arcCount E≤14)
    (positiveOut : ∀x,1≤outdegree E x) (positiveIn : ∀x,1≤indegree E x) :
    score E≤if arcCount E≤11 then 3 else 2 := by
  have cases : arcCount E=9 ∨ arcCount E=10 ∨ arcCount E=11 ∨
      arcCount E=12 ∨ arcCount E=13 ∨ arcCount E=14 := by omega
  rcases cases with h|h|h|h|h|h
  · simpa [h] using FiveVertexPositive09.upper E loopless h positiveOut positiveIn
  · simpa [h] using FiveVertexPositive10.upper E loopless h positiveOut positiveIn
  · simpa [h] using FiveVertexPositive11.upper E loopless h positiveOut positiveIn
  · simpa [h] using FiveVertexPositive12.upper E loopless h positiveOut positiveIn
  · simpa [h] using FiveVertexPositive13.upper E loopless h positiveOut positiveIn
  · simpa [h] using FiveVertexPositive14.upper E loopless h positiveOut positiveIn
#print axioms upper
end Delivery.FiveVertexPositive
