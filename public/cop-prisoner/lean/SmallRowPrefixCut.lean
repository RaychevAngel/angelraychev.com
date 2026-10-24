import SmallRowPrefixBoolean
import RowPrefixCutLoss

/-! Reflected arbitrary-order checks for the prescribed-degree cut/loss rule. -/
namespace Delivery.RowPrefix.SmallCut
open FiniteGame SmallBoolean

def lostCheck (D R : Fin n → Nat) (lost : Rows n) (losses : List (Loss n)) : Bool :=
  allN (n:=n) (fun s => allN (n:=n) (fun t => decide
    (bit (lost s) t → 2 ≤ D s ∧ 2 ≤ R t ∧ s ≠ t ∧ LossExists losses s t)))

theorem lostCheck_true (D R : Fin n → Nat) (lost : Rows n) (losses : List (Loss n)) :
    lostCheck D R lost losses = true ↔ LostOK D R lost losses := by
  simp only [lostCheck,allN_true,decide_eq_true_eq,LostOK]

def boundCheck (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : CutBound n) : Bool :=
  envelopeCheck R p cert.upper cert.lower &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  lostCheck D R cert.lost cert.losses &&
  decide (eligibleCount D R + lowSum D + lowSum R ≤
    bound + allowedCount cert.lost + degreeSum D + cornerCount D R p)

theorem boundCheck_true (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : CutBound n) :
    boundCheck D R p bound cert = true ↔ CutBoundOK D R p bound cert := by
  simp only [boundCheck,Bool.and_eq_true,envelopeCheck_true,List.all_eq_true,regionCheck_true,
    lostCheck_true,decide_eq_true_eq,CutBoundOK]
  simp only [and_assoc]

#print axioms boundCheck_true
end Delivery.RowPrefix.SmallCut
