import RowPrefixSymmetry
import RowPrefixLoss

/-! Complete reflected prescribed-degree trees. Every raw row is either
impossible or transported by a checked symmetry to a checked child. -/
namespace Delivery.RowPrefix

inductive Tree (n : Nat) where
  | invalid
  | bound (certificate : Bound n)
  | branch (representatives : List Nat) (route : Route n) (children : Nat → Tree n)

def Tree.check {n : Nat} (D R : Fin n → Nat) (choices : Nat → List Nat)
    (bound : Nat) (p : List Nat) : Tree n → Bool
  | .invalid => decide (¬PrefixOK D R p)
  | .bound cert => decide (BoundOK D R p bound cert)
  | .branch representatives route children =>
    if h : p.length < n then
      decide (RoutesOK D R p (choices (D ⟨p.length,h⟩)) representatives route) &&
        representatives.all (fun mask => (children mask).check D R choices bound (p++[mask]))
    else false

theorem Tree.sound {n : Nat} (D R : Fin n → Nat) (choices : Nat → List Nat)
    (complete : ∀ s : Fin n, RowCover n (D s) (choices (D s)))
    (bound : Nat) (p : List Nat) (tree : Tree n)
    (checked : tree.check D R choices bound p = true) : Upper D R p bound := by
  induction tree generalizing p with
  | invalid => exact invalid_upper D R p bound (of_decide_eq_true checked)
  | bound cert => exact bound_sound D R p bound cert (of_decide_eq_true checked)
  | branch representatives route children ih =>
    simp only [Tree.check] at checked
    split at checked
    next h =>
      simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
      exact routed_branch D R p bound h (choices (D ⟨p.length,h⟩)) representatives route
        (complete ⟨p.length,h⟩) checked.1
        (fun mask member => ih mask (p++[mask]) (checked.2 mask member))
    next h => contradiction

#print axioms Tree.sound
end Delivery.RowPrefix
