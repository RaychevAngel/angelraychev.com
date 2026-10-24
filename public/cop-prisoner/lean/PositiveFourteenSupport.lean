import IrregularTenFourteen

/-! Positive-support reduction for the sharp fourteen-arrow upper bound.
The only finite input not supplied in this module is the order-nine bound. -/
namespace Delivery.PositiveFourteenSupport
open FiniteGame Extremal DenseCombinatorics SparseSupport

theorem large_order {n : Nat} (order : 11≤n) (E : Graph (Fin n))
    (loopless : Loopless E) (budget : arcCount E=14)
    (outgoing : ∀x,1≤outdegree E x) (incoming : ∀x,1≤indegree E x) :
    score E≤9 := by
  have counts := positive_support_counts E outgoing incoming
  have rectangle := eligible_rectangle E loopless
  have left : card (ActiveOut E)≤3 := by omega
  have right : card (ActiveIn E)≤3 := by omega
  have product := Nat.mul_le_mul left right
  omega

theorem upper_with_nine
    (nine : ∀E : Graph (Fin 9), Loopless E → arcCount E=14 →
      (∀x,1≤outdegree E x) → (∀x,1≤indegree E x) → score E≤13)
    {n : Nat} (order : 9≤n) (E : Graph (Fin n)) (loopless : Loopless E)
    (budget : arcCount E=14) (outgoing : ∀x,1≤outdegree E x)
    (incoming : ∀x,1≤indegree E x) : score E≤13 := by
  by_cases isNine : n=9
  · subst n
    exact nine E loopless budget outgoing incoming
  by_cases isTen : n=10
  · subst n
    exact IrregularTen14.positive_upper E loopless budget outgoing incoming
  have bound := large_order (by omega : 11≤n) E loopless budget outgoing incoming
  omega

#print axioms large_order
#print axioms upper_with_nine
end Delivery.PositiveFourteenSupport
