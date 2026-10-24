import RowPrefixCamping
import RowPrefixBooleanNine

namespace Delivery.RowPrefix.CampingNine
open BooleanNine

def fastEnvelopeCheck (R : Fin 9 → Nat) (p : List Nat)
    (upper lower : Rows 9) (available : Nat) : Bool :=
  all9 (fun t => decide (bit available t ↔ used p t < R t)) &&
  all9 (fun r => decide (lower r = (if h : r.val < p.length then p[r.val] else 0) ||| 2^r.val)) &&
  all9 (fun r => decide (upper r = if r.val < p.length then lower r else available ||| 2^r.val))

theorem fastEnvelopeCheck_true (R : Fin 9 → Nat) (p : List Nat)
    (upper lower : Rows 9) (available : Nat) :
    fastEnvelopeCheck R p upper lower available = true ↔ FastEnvelopeOK R p upper lower available := by
  simp only [fastEnvelopeCheck,Bool.and_eq_true,all9_true,decide_eq_true_eq,FastEnvelopeOK,and_assoc]

def campCheck (upper lower : Rows 9) (loss : CampLoss 9) : Bool :=
  decide (loss.region &&& loss.targets = 0) &&
  all9 (fun r => decide (bit loss.region r → r ≠ loss.cop →
    upper r &&& loss.targets=0 ∧ upper r &&& (lower loss.cop ||| loss.region)=upper r))

theorem campCheck_true (upper lower : Rows 9) (loss : CampLoss 9) :
    campCheck upper lower loss = true ↔ CampRegionOK upper lower loss := by
  simp only [campCheck,Bool.and_eq_true,all9_true,decide_eq_true_eq,CampRegionOK]

def coverCheck (D R : Fin 9 → Nat) (cert : MixedBound 9) : Bool :=
  all9 (fun s => all9 (fun t => decide (bit (cert.lost s) t →
    2 ≤ D s ∧ 2 ≤ R t ∧ s ≠ t ∧ (CampExists cert.camps s t ∨ LossExists cert.losses s t))))

def boundCheck (D R : Fin 9 → Nat) (p : List Nat) (bound : Nat) (cert : MixedBound 9) : Bool :=
  fastEnvelopeCheck R p cert.upper cert.lower cert.available &&
  cert.camps.all (campCheck cert.upper cert.lower) &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  coverCheck D R cert &&
  decide (eligibleCount D R + lowSum D + lowSum R ≤
    bound + allowedCount cert.lost + degreeSum D + cornerCount D R p)

theorem boundCheck_true (D R : Fin 9 → Nat) (p : List Nat) (bound : Nat) (cert : MixedBound 9) :
    boundCheck D R p bound cert = true ↔ MixedBoundOK D R p bound cert := by
  simp only [boundCheck,Bool.and_eq_true,fastEnvelopeCheck_true,List.all_eq_true,campCheck_true,
    regionCheck_true,coverCheck,all9_true,decide_eq_true_eq,MixedBoundOK,and_assoc]


def reducedCheck (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat) (cert : MixedBound 9) : Bool :=
  fastEnvelopeCheck R p cert.upper cert.lower cert.available &&
  cert.camps.all (campCheck cert.upper cert.lower) &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  coverCheck D R cert &&
  decide (left ≤ bound + allowedCount cert.lost + total + cornerCount D R p)

theorem reduced_sound (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat)
    (cert : MixedBound 9)
    (left_eq : eligibleCount D R + lowSum D + lowSum R = left)
    (total_eq : degreeSum D = total)
    (checked : reducedCheck D R p bound left total cert = true) : Upper D R p bound := by
  apply mixed_bound_sound D R p bound cert
  simp only [reducedCheck,Bool.and_eq_true,fastEnvelopeCheck_true,List.all_eq_true,campCheck_true,
    regionCheck_true,coverCheck,all9_true,decide_eq_true_eq,and_assoc] at checked
  refine ⟨checked.1,checked.2.1,checked.2.2.1,checked.2.2.2.1,?_⟩
  rw [left_eq,total_eq]
  exact checked.2.2.2.2

#print axioms boundCheck_true
end Delivery.RowPrefix.CampingNine
