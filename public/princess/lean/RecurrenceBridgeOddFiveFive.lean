import RecurrenceBridgeOddFiveFour

/-! Finite arithmetic bases for the ordinary translation proof at budget five.
No full physical odd-five classification is asserted by this module. -/
namespace Princess.RecurrenceBridgeOddFiveFive
open Princess.RecurrenceBridgeOddFiveFour (profile)

def core (b z : Nat) : Nat :=
  if b≤5 then b else 2*b-
    (if z=0 then (if b%5=0 ∨ b%5=3 then 6 else 5)
      else (if b%5=0 ∨ b%5=2 then 5 else 4))

def value (h b z : Nat) : Nat :=
  if z=0 ∧ b=h then 2*h-6 else min (2*h-5) (core b z)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_certificate : ∀ (t : Fin 2) (b : Fin 19) (z : Fin 2) (p : Fin 6),
    b.val≤(5*t.val+12)+1-z.val → (b.val=0 ∨ 3-z.val≤b.val) →
    value (5*t.val+12) b.val z.val ≤ p.val+
      value (5*t.val+12) (profile (5*t.val+12) z.val (b.val-p.val)) (1-z.val) := by
  decide +kernel

end Princess.RecurrenceBridgeOddFiveFive
#print axioms Princess.RecurrenceBridgeOddFiveFive.finite_certificate
