import RowPrefixCampingNine

namespace Delivery.RowPrefix.CampingNine

structure Leaf where
  initial : List Nat
  cert : MixedBound 9

def checkLeaves (D R : Fin 9 → Nat) (bound left total : Nat) (leaves : List Leaf) : Bool :=
  leaves.all fun leaf => reducedCheck D R leaf.initial bound left total leaf.cert

theorem leaf_upper (D R : Fin 9 → Nat) (bound left total : Nat) (leaves : List Leaf)
    (left_eq : eligibleCount D R + lowSum D + lowSum R = left)
    (total_eq : degreeSum D = total)
    (checked : checkLeaves D R bound left total leaves = true)
    (i : Nat) (hi : i < leaves.length) : Upper D R leaves[i].initial bound := by
  apply reduced_sound D R _ bound left total leaves[i].cert left_eq total_eq
  exact List.all_eq_true.mp checked leaves[i] (List.getElem_mem hi)

#print axioms leaf_upper
end Delivery.RowPrefix.CampingNine
