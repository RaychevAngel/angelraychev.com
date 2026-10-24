import SparseParity
import GraphPadding
import ExtremalExamples

/-! Reusable sparse attainment from actual cores and isolate padding.
The uniform all-order sparse core family is not assumed here; the concrete
twelve-vertex instance is certified by the existing literal rank table. -/
namespace Delivery.SparseAttainment
open Extremal

theorem maximum_even_of_core {n k : Nat} (hk : 5 ≤ k) (order : k ≤ n)
    (E : Graph (Fin k)) (loopless : Loopless E) (arcs : arcCount E=2*k)
    (value : score E=k*(k-3)) : IsMaximum n (2*k) (k*(k-3)) := by
  constructor
  · intro F loopF budget
    exact SparseParity.even_upper F loopF hk budget
  · obtain ⟨F,loopF,budget,attaining⟩ := GraphPadding.pad_to_order E loopless order
    exact ⟨F,loopF,budget.trans arcs,attaining.trans value⟩

theorem maximum_odd_of_core {n k : Nat} (hk : 5 ≤ k) (order : k+1 ≤ n)
    (E : Graph (Fin (k+1))) (loopless : Loopless E) (arcs : arcCount E=2*k+1)
    (value : score E=k*(k-3)+2) : IsMaximum n (2*k+1) (k*(k-3)+2) := by
  constructor
  · intro F loopF budget
    exact SparseParity.odd_upper F loopF hk budget
  · obtain ⟨F,loopF,budget,attaining⟩ := GraphPadding.pad_to_order E loopless order
    exact ⟨F,loopF,budget.trans arcs,attaining.trans value⟩

/-- Unconditional exact cell at every ambient order n≥12, using the literal
24-arrow, 108-guarantee core and the unrestricted sparse upper theorem. -/
theorem maximum_twentyfour {n : Nat} (order : 12 ≤ n) : IsMaximum n 24 108 :=
  maximum_even_of_core (by decide) order TwelveVertex.edge
    ExtremalExamples.twelve_loopless ExtremalExamples.twelve_arcs ExtremalExamples.twelve_score

/-- Fresh one-predecessor sinks increase an exact arrow budget while keeping
the graph's score, with the resulting order stated explicitly. -/
theorem raise_budget {n m : Nat} (E : Graph (Fin n)) (loopless : Loopless E) (v : Fin n)
    (budget : arcCount E ≤ m) :
    ∃ F : Graph (Fin (n+(m-arcCount E))), Loopless F ∧ arcCount F=m ∧ score F=score E := by
  refine ⟨GraphPadding.sinks E v (m-arcCount E),GraphPadding.sinks_loopless loopless v _,?_,
    GraphPadding.sinks_score E v _⟩
  rw [GraphPadding.sinks_arcs]
  omega

#print axioms maximum_even_of_core
#print axioms maximum_odd_of_core
#print axioms maximum_twentyfour
#print axioms raise_budget
end Delivery.SparseAttainment
