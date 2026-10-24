import RowPrefixPairLoss

namespace Delivery.RowPrefix.CornerWitnessNine
open FiniteGame Extremal DenseCombinatorics BooleanNine CampingNine

def CornersOK (D R : Fin 9 → Nat) (p : List Nat) (corners : List (Fin 9 × Fin 9)) : Prop :=
  corners.Nodup ∧ ∀ st∈corners, ¬2≤D st.1 ∧ ¬2≤R st.2 ∧ known p st.1 st.2

theorem corner_count (D R : Fin 9 → Nat) (p : List Nat) (corners : List (Fin 9 × Fin 9))
    (checked : CornersOK D R p corners) : corners.length≤cornerCount D R p := by
  apply checked.1.length_le_of_subset
  intro st member
  simp only [List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq]
  exact checked.2 st member

def check (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat)
    (cert : PairBound 9) (corners : List (Fin 9 × Fin 9)) : Bool :=
  fastEnvelopeCheck R p cert.upper cert.lower cert.available &&
  cert.camps.all (campCheck cert.upper cert.lower) &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  decide cert.pairs.Nodup &&
  cert.pairs.all (fun st => decide (2≤D st.1 ∧ 2≤R st.2 ∧ st.1≠st.2 ∧
    (CampExists cert.camps st.1 st.2 ∨ LossExists cert.losses st.1 st.2))) &&
  decide corners.Nodup &&
  corners.all (fun st => decide (¬2≤D st.1 ∧ ¬2≤R st.2 ∧ known p st.1 st.2)) &&
  decide (left ≤ bound + cert.pairs.length + total + corners.length)

theorem sound (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat)
    (cert : PairBound 9) (corners : List (Fin 9 × Fin 9))
    (left_eq : eligibleCount D R + lowSum D + lowSum R=left)
    (total_eq : degreeSum D=total)
    (checked : check D R p bound left total cert corners=true) : Upper D R p bound := by
  apply pair_bound_sound D R p bound left total cert left_eq total_eq
  simp only [check,Bool.and_eq_true,fastEnvelopeCheck_true,List.all_eq_true,campCheck_true,
    regionCheck_true,decide_eq_true_eq,and_assoc] at checked
  rcases checked with ⟨envelope,camps,games,unique,pairs,cornerUnique,cornersGood,numeric⟩
  refine ⟨envelope,camps,games,unique,pairs,?_⟩
  have count := corner_count D R p corners ⟨cornerUnique,cornersGood⟩
  omega

#print axioms sound
end Delivery.RowPrefix.CornerWitnessNine
