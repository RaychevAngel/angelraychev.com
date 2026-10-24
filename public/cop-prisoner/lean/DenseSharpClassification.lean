import DenseSmallStaircase

/-! The sharp dense-domain threshold: every order at least eleven. The
finite bridge selects listed adjacency tables; all orders at least twenty
retain the existing parameterized construction. -/
namespace Delivery.DenseSharpClassification
open FiniteGame Extremal DenseClassification

def offsetAttainer (n r : Nat) (hn : 11≤n) (positive : 1≤r) (limit : r≤n) :
    Attainer n (n*(n-3)+r) (staircase n r) := by
  by_cases large : 20≤n
  · exact DenseClassification.offsetAttainer n r large positive limit
  · exact DenseSmallStaircase.attainer n r hn (by omega) positive limit

def attainer (n m : Nat) (hn : 11≤n) (low : n*(n-3)≤m)
    (admissible : m≤n*(n-1)) : Attainer n m (formula n m) := by
  by_cases boundary : m=n*(n-3)
  · subst m
    simpa [formula] using
      (show Attainer n (n*(n-3)) (2*n) from
        ⟨DenseCore.graph n (by omega),DenseCore.graph_loopless (by omega),
          DenseCore.graph_arcCount (by omega),DenseCore.graph_score (by omega)⟩)
  · by_cases dense : m≤n*(n-2)
    · have endpoint := endpoint_identity (by omega : 3≤n)
      have offset : 1≤m-n*(n-3) := by omega
      have offsetN : m-n*(n-3)≤n := by omega
      have exactBudget : n*(n-3)+(m-n*(n-3))=m := by omega
      simpa only [formula,if_neg boundary,if_pos dense,exactBudget] using
        offsetAttainer n (m-n*(n-3)) hn offset offsetN
    · have zero : formula n m=0 := by simp only [formula,if_neg boundary,if_neg dense]
      rw [zero]
      exact ⟨DenseZero.initialGraph n m,DenseZero.initialGraph_loopless n m,
        DenseZero.initialGraph_arcCount admissible,
        DenseZero.zero_at_budget _ (DenseZero.initialGraph_loopless n m)
          (DenseZero.initialGraph_arcCount admissible) (by omega)⟩

theorem maximum {n m : Nat} (hn : 11≤n) (low : n*(n-3)≤m)
    (admissible : m≤n*(n-1)) : IsMaximum n m (formula n m) := by
  constructor
  · intro E noLoops arrows
    by_cases boundary : m=n*(n-3)
    · rw [formula,if_pos boundary]
      exact (DenseCore.maximum (by omega)).1 E noLoops (arrows.trans boundary)
    · by_cases dense : m≤n*(n-2)
      · have endpoint := endpoint_identity (by omega : 3≤n)
        have budget : arcCount E=n*(n-3)+(m-n*(n-3)) := by omega
        have upper := DenseStaircase.bound_at_offset E noLoops (by omega)
          (by omega : 1≤m-n*(n-3)) (by omega) budget
        simpa only [formula,if_neg boundary,if_pos dense,staircase] using upper
      · have zero := DenseZero.zero_at_budget E noLoops arrows (by omega : n*(n-2)<m)
        simp only [formula,if_neg boundary,if_neg dense,zero,Nat.le_refl]
  · let G := attainer n m hn low admissible
    exact ⟨G.edge,G.loopless,G.arcs,G.count⟩

#print axioms attainer
#print axioms maximum
end Delivery.DenseSharpClassification
