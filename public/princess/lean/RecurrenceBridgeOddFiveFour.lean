import FiveRowFourProbeArithmetic

/-! A universal scalar lower potential for four inspections on odd five-row
boards. Physical exact profiles and their nesting are ordinary antecedents. -/
namespace Princess.RecurrenceBridgeOddFiveFour
open Princess.FiveRowFourProbeArithmetic (core)

def profile (h z k : Nat) : Nat :=
  if k=0 then 0 else if z=0 then
    if h≤k then h else k+(if k=1 ∨ h-3≤k then 1 else 2)
  else if k=h then h+1 else k+(if k≤2 ∨ h-2≤k then 2 else 3)

def cap (h : Nat) : Nat :=
  if h%3=0 then 8*(h/3)-8 else
  if h%3=1 then 8*(h/3)-5 else 8*(h/3)-4

def value (h b z : Nat) : Nat :=
  if z=0 ∧ b=h then cap h-1 else
  if z=0 ∧ b=h-1 then min (core b z) (cap h-2) else
  min (cap h) (core b z)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_certificate : ∀ (t : Fin 12) (b : Fin 25) (z : Fin 2) (p : Fin 5),
    b.val≤(t.val+12)+1-z.val → (b.val=0 ∨ 3-z.val≤b.val) →
    value (t.val+12) b.val z.val ≤ p.val+
      value (t.val+12) (profile (t.val+12) z.val (b.val-p.val)) (1-z.val) := by
  decide +kernel

end Princess.RecurrenceBridgeOddFiveFour
#print axioms Princess.RecurrenceBridgeOddFiveFour.finite_certificate
