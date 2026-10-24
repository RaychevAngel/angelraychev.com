import IrregularNineFourteen
import PositiveFourteenSupport

/-! Unconditional positive-support fourteen-arrow bound at all orders from
nine. This deliberately does not claim the unrestricted fourteen-arrow table. -/
namespace Delivery.PositiveFourteen
open FiniteGame Extremal SparseSupport

theorem upper {n : Nat} (order : 9≤n) (E : Graph (Fin n))
    (loopless : Loopless E) (budget : arcCount E=14)
    (outgoing : ∀x,1≤outdegree E x) (incoming : ∀x,1≤indegree E x) :
    score E≤13 :=
  PositiveFourteenSupport.upper_with_nine IrregularNine14.positive_upper
    order E loopless budget outgoing incoming

#print axioms upper
end Delivery.PositiveFourteen
