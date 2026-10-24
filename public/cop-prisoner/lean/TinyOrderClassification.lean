import DenseZero

/-! Every admissible budget at orders zero through three. -/
namespace Delivery.TinyOrderClassification
open FiniteGame Extremal

theorem score_zero {n : Nat} (small : n≤3) (E : Graph (Fin n))
    (loops : Loopless E) : score E=0 := by
  have upper := VertexBound.vertex_upper E loops
  rw [Nat.sub_eq_zero_of_le small,Nat.mul_zero] at upper
  omega

theorem maximum {n m : Nat} (small : n≤3) (admissible : m≤n*(n-1)) :
    IsMaximum n m 0 := by
  refine ⟨fun E loops _ => Nat.le_of_eq (score_zero small E loops),
    DenseZero.initialGraph n m,DenseZero.initialGraph_loopless n m,
    DenseZero.initialGraph_arcCount admissible,?_⟩
  exact score_zero small _ (DenseZero.initialGraph_loopless n m)

#print axioms maximum
end Delivery.TinyOrderClassification
