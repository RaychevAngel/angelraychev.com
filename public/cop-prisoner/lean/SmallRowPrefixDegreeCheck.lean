import SmallRowPrefixDegreeLoss

/-! Reflected checks for the degree-aware actual-completion envelope. -/
namespace Delivery.RowPrefix.DegreeLoss
open SmallBoolean

def envelopeCheck (D R : Fin n → Nat) (p : List Nat) (upper lower : Rows n) (available : Nat) : Bool :=
  allN (n:=n) (fun t => decide (bit available t ↔ used p t<R t)) &&
  allN (n:=n) (fun r => decide (lower r=(if h:r.val<p.length then p[r.val] else 0) ||| 2^r.val)) &&
  allN (n:=n) (fun r => decide (upper r=if r.val<p.length then lower r else
    if D r=0 then 2^r.val else available ||| 2^r.val))

theorem envelopeCheck_true (D R : Fin n → Nat) (p : List Nat) (upper lower : Rows n) (available : Nat) :
    envelopeCheck D R p upper lower available=true ↔ EnvelopeOK D R p upper lower available := by
  simp only [envelopeCheck,Bool.and_eq_true,allN_true,decide_eq_true_eq,EnvelopeOK,and_assoc]

def boundCheck (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : Bound n) : Bool :=
  envelopeCheck D R p cert.upper cert.lower available &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  coverCheck D R p cert.allowed cert.losses && decide (allowedCount cert.allowed≤bound)

theorem boundCheck_true (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : Bound n) :
    boundCheck D R p bound available cert=true ↔ BoundOK D R p bound available cert := by
  simp only [boundCheck,Bool.and_eq_true,envelopeCheck_true,List.all_eq_true,regionCheck_true,
    coverCheck_true,decide_eq_true_eq,BoundOK,and_assoc]

def cutCheck (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : CutBound n) : Bool :=
  envelopeCheck D R p cert.upper cert.lower available &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  SmallCut.lostCheck D R cert.lost cert.losses &&
  decide (eligibleCount D R+lowSum D+lowSum R≤bound+allowedCount cert.lost+degreeSum D+cornerCount D R p)

theorem cutCheck_true (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : CutBound n) :
    cutCheck D R p bound available cert=true ↔ CutBoundOK D R p bound available cert := by
  simp only [cutCheck,Bool.and_eq_true,envelopeCheck_true,List.all_eq_true,regionCheck_true,
    SmallCut.lostCheck_true,decide_eq_true_eq,CutBoundOK,and_assoc]

#print axioms boundCheck_true
#print axioms cutCheck_true
end Delivery.RowPrefix.DegreeLoss
