import DenseStaircaseConstruction
import DenseFirstStep

/-! Complete dense-region classification at every order n≥20, with a literal
adjacency recipe for each budget. This does not assert the sparse/main-region
classification or the small-order dense tables. -/
namespace Delivery.DenseClassification
open FiniteGame Extremal

structure Attainer (n m value : Nat) where
  edge : Graph (Fin n)
  loopless : Loopless edge
  arcs : arcCount edge = m
  count : score edge = value

def staircase (n r : Nat) : Nat := 2*n-r-DenseCounting.ceilHalf r-1

def formula (n m : Nat) : Nat :=
  if m = n*(n-3) then 2*n
  else if m ≤ n*(n-2) then staircase n (m-n*(n-3)) else 0

def offsetAttainer (n r : Nat) (hn : 20 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) :
    Attainer n (n*(n-3)+r) (staircase n r) := by
  by_cases one : r = 1
  · subst r
    exact ⟨DenseFirstStep.graph n (by omega),DenseFirstStep.graph_loopless (by omega),
      DenseFirstStep.graph_arcCount (by omega),by
        rw [DenseFirstStep.graph_score]
        simp only [staircase,DenseCounting.ceilHalf]
        omega⟩
  · have r2 : 2 ≤ r := by omega
    have order : r+(n-r) = n := by omega
    have count : (r-2)/2+2*(n-r) = staircase n r := by
      unfold staircase DenseCounting.ceilHalf
      omega
    have result : Attainer (r+(n-r)) ((r+(n-r))*(r+(n-r)-3)+r) ((r-2)/2+2*(n-r)) :=
      ⟨DenseStaircaseConstruction.graph r (n-r) r2 (by omega),
        DenseStaircaseConstruction.loopless r2 (by omega),
        DenseStaircaseConstruction.arc_count r2 (by omega),
        DenseStaircaseConstruction.score_count r2 (by omega)⟩
    simpa only [order,count] using result

theorem endpoint_identity {n : Nat} (hn : 3 ≤ n) :
    n*(n-2) = n*(n-3)+n := by
  have eq : n-2 = (n-3)+1 := by omega
  rw [eq,Nat.mul_add,Nat.mul_one]

/-- A concrete constructor, chosen by the displayed budget cases. -/
def attainer (n m : Nat) (hn : 20 ≤ n) (low : n*(n-3) ≤ m)
    (admissible : m ≤ n*(n-1)) : Attainer n m (formula n m) := by
  by_cases boundary : m = n*(n-3)
  · subst m
    simpa [formula] using
      (show Attainer n (n*(n-3)) (2*n) from
        ⟨DenseCore.graph n (by omega),DenseCore.graph_loopless (by omega),
          DenseCore.graph_arcCount (by omega),DenseCore.graph_score (by omega)⟩)
  · by_cases dense : m ≤ n*(n-2)
    · have endpoint := endpoint_identity (by omega : 3 ≤ n)
      have offset : 1 ≤ m-n*(n-3) := by omega
      have offsetN : m-n*(n-3) ≤ n := by omega
      have exactBudget : n*(n-3)+(m-n*(n-3)) = m := by omega
      simpa only [formula,if_neg boundary,if_pos dense,exactBudget] using
        offsetAttainer n (m-n*(n-3)) hn offset offsetN
    · have zero : formula n m = 0 := by simp only [formula,if_neg boundary,if_neg dense]
      rw [zero]
      exact ⟨DenseZero.initialGraph n m,DenseZero.initialGraph_loopless n m,
        DenseZero.initialGraph_arcCount admissible,
        DenseZero.zero_at_budget _ (DenseZero.initialGraph_loopless n m)
          (DenseZero.initialGraph_arcCount admissible) (by omega)⟩

/-- The full dense region, including its boundary and the final zero region. -/
theorem maximum {n m : Nat} (hn : 20 ≤ n) (low : n*(n-3) ≤ m)
    (admissible : m ≤ n*(n-1)) : IsMaximum n m (formula n m) := by
  constructor
  · intro E noLoops arrows
    by_cases boundary : m = n*(n-3)
    · rw [formula,if_pos boundary]
      exact (DenseCore.maximum (by omega)).1 E noLoops (arrows.trans boundary)
    · by_cases dense : m ≤ n*(n-2)
      · have endpoint := endpoint_identity (by omega : 3 ≤ n)
        have budget : arcCount E = n*(n-3)+(m-n*(n-3)) := by omega
        have upper := DenseStaircase.bound_at_offset E noLoops (by omega)
          (by omega : 1 ≤ m-n*(n-3)) (by omega) budget
        simpa only [formula,if_neg boundary,if_pos dense,staircase] using upper
      · have zero := DenseZero.zero_at_budget E noLoops arrows (by omega : n*(n-2) < m)
        simp only [formula,if_neg boundary,if_neg dense,zero,Nat.le_refl]
  · let G := attainer n m hn low admissible
    exact ⟨G.edge,G.loopless,G.arcs,G.count⟩

#print axioms attainer
#print axioms maximum
end Delivery.DenseClassification
