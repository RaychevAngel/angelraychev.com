import RowPrefixPermutation
import RowPrefixBooleanNine

namespace Delivery.RowPrefix.PermutationNine
open BooleanNine

def check (D R : Fin 9 → Nat) (p q : List Nat) (f g : Fin 9 → Fin 9) : Bool :=
  all9 (fun x => decide (g (f x) = x ∧ f (g x) = x)) &&
  all9 (fun x => decide (D (f x) = D x ∧ R (f x) = R x)) &&
  all9 (fun s => decide (s.val < q.length → (f s).val < p.length)) &&
  all9 (fun s => if hq : s.val < q.length then
    if hp : (f s).val < p.length then all9 (fun t => decide (bit p[(f s).val] (f t) ↔ bit q[s.val] t))
    else true else true)

theorem check_true (D R : Fin 9 → Nat) (p q : List Nat) (f g : Fin 9 → Fin 9) :
    check D R p q f g = true ↔ PermMapOK D R p q f g := by
  simp only [check,Bool.and_eq_true,all9_true,decide_eq_true_eq,PermMapOK]
  constructor
  · rintro ⟨⟨⟨inv,degree⟩,length⟩,bits⟩
    refine ⟨inv,degree,length,?_⟩
    intro s hq hp t
    have bitCheck := bits s
    rw [dif_pos hq,dif_pos hp] at bitCheck
    exact of_decide_eq_true ((all9_true _).mp bitCheck t)
  · rintro ⟨inv,degree,length,bits⟩
    refine ⟨⟨⟨inv,degree⟩,length⟩,?_⟩
    intro s
    split
    next hq =>
      split
      next hp => exact (all9_true _).mpr (fun t => decide_eq_true (bits s hq hp t))
      next => rfl
    next => rfl

#print axioms check_true
end Delivery.RowPrefix.PermutationNine
