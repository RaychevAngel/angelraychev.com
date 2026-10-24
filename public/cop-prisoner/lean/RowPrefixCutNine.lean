import RowPrefixBooleanNine
import RowPrefixCutLoss

/-! Reflected nine-vertex checks for the prescribed-degree cut/loss rule. -/
namespace Delivery.RowPrefix.CutNine
open FiniteGame BooleanNine

def lostCheck (D R : Fin 9 → Nat) (lost : Rows 9) (losses : List (Loss 9)) : Bool :=
  all9 (fun s => all9 (fun t => decide
    (bit (lost s) t → 2 ≤ D s ∧ 2 ≤ R t ∧ s ≠ t ∧ LossExists losses s t)))

theorem lostCheck_true (D R : Fin 9 → Nat) (lost : Rows 9) (losses : List (Loss 9)) :
    lostCheck D R lost losses = true ↔ LostOK D R lost losses := by
  simp only [lostCheck,all9_true,decide_eq_true_eq,LostOK]

def boundCheck (D R : Fin 9 → Nat) (p : List Nat) (bound : Nat) (cert : CutBound 9) : Bool :=
  envelopeCheck R p cert.upper cert.lower &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  lostCheck D R cert.lost cert.losses &&
  decide (eligibleCount D R + lowSum D + lowSum R ≤
    bound + allowedCount cert.lost + degreeSum D + cornerCount D R p)

theorem boundCheck_true (D R : Fin 9 → Nat) (p : List Nat) (bound : Nat) (cert : CutBound 9) :
    boundCheck D R p bound cert = true ↔ CutBoundOK D R p bound cert := by
  simp only [boundCheck,Bool.and_eq_true,envelopeCheck_true,List.all_eq_true,regionCheck_true,
    lostCheck_true,decide_eq_true_eq,CutBoundOK]
  simp only [and_assoc]

inductive Tree where
  | invalid
  | bound (cert : CutBound 9)
  | branch (representatives : List Nat) (route : Route 9) (children : Nat → Tree)

def check (D R : Fin 9 → Nat) (choices : Nat → List Nat)
    (bound : Nat) (p : List Nat) : Tree → Bool
  | .invalid => !prefixCheck D R p
  | .bound cert => boundCheck D R p bound cert
  | .branch representatives route children =>
    if h : p.length < 9 then
      routesCheck D R p (choices (D ⟨p.length,h⟩)) representatives route &&
        representatives.all (fun mask => check D R choices bound (p++[mask]) (children mask))
    else false

theorem sound (D R : Fin 9 → Nat) (choices : Nat → List Nat)
    (complete : ∀ s : Fin 9, RowCover 9 (D s) (choices (D s)))
    (bound : Nat) (p : List Nat) (tree : Tree)
    (checked : check D R choices bound p tree = true) : Upper D R p bound := by
  induction tree generalizing p with
  | invalid =>
    apply invalid_upper D R p bound
    intro valid
    have := (prefixCheck_true D R p).mpr valid
    simp only [check,this] at checked
    contradiction
  | bound cert => exact cut_bound_sound D R p bound cert ((boundCheck_true _ _ _ _ _).mp checked)
  | branch representatives route children ih =>
    simp only [check] at checked
    split at checked
    next h =>
      simp only [Bool.and_eq_true,routesCheck_true,List.all_eq_true] at checked
      exact routed_branch D R p bound h (choices (D ⟨p.length,h⟩)) representatives route
        (complete ⟨p.length,h⟩) checked.1
        (fun mask member => ih mask (p++[mask]) (checked.2 mask member))
    next h => contradiction

#print axioms sound
end Delivery.RowPrefix.CutNine
