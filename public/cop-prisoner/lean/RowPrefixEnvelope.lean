import RowPrefixKernel
import SparseDeletion

namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

def used {n : Nat} (p : List Nat) (t : Fin n) : Nat :=
  ((List.finRange n).filter fun s => decide (known p s t)).length

def upperEdge {n : Nat} (R : Fin n → Nat) (p : List Nat) : Graph (Fin n) :=
  fun s t => known p s t ∨ (p.length ≤ s.val ∧ s ≠ t ∧ used p t < R t)
instance {n : Nat} (R : Fin n → Nat) (p : List Nat) : DecidableRel (upperEdge R p) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem remaining_capacity {n : Nat} {D R : Fin n → Nat} {p : List Nat}
    {E : Graph (Fin n)} (valid : Prescribed D R E) (agrees : Agrees p E)
    {s t : Fin n} (future : p.length ≤ s.val) (edge : E s t) : used p t < R t := by
  have lo := (sandwich valid.1 agrees).1
  have disjoint : ∀ x, known p x t → x = s → False := by
    rintro x ⟨h,_⟩ rfl
    omega
  have union := card_disjoint_union disjoint
  have bound : card (fun x => known p x t ∨ x = s) ≤ indegree E t := by
    apply card_mono
    rintro x (known | rfl)
    · exact lo x t known
    · exact edge
  rw [union,SparseDeletion.card_singleton,valid.2.2 t,card_eq] at bound
  change used p t + 1 ≤ R t at bound
  omega

theorem tight_sandwich {n : Nat} {D R : Fin n → Nat} {p : List Nat}
    {E : Graph (Fin n)} (valid : Prescribed D R E) (agrees : Agrees p E) :
    RobustTwoMove.Subgraph (known p) E ∧ RobustTwoMove.Subgraph E (upperEdge R p) := by
  refine ⟨(sandwich valid.1 agrees).1,?_⟩
  intro s t edge
  by_cases before : s.val < p.length
  · exact Or.inl ⟨before,(agrees s before t).mp edge⟩
  · exact Or.inr ⟨by omega,fun same => valid.1 s (same ▸ edge),
      remaining_capacity valid agrees (by omega) edge⟩

#print axioms tight_sandwich
end Delivery.RowPrefix
