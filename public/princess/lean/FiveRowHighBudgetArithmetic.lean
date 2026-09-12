import Std

/-! Three finite cardinality certificates for the even five-row proof.
The geometric neighborhood bound represented by profile is proved separately. -/
namespace Princess.FiveRowHighBudgetArithmetic

def profile (h k : Nat) : Nat :=
  if k = 0 then 0 else if k ≥ h-1 then h else
  if k = h-2 then h-1 else if k = 1 then 2 else k+2

def step (h m p : Nat) (state : Nat × Nat) : Nat × Nat :=
  (profile h (state.1-p), profile h (state.2-(m-p)))

def total (state : Nat × Nat) : Nat := state.1+state.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fifteen_eight : ∀ p q r : Fin 9,
    8 < total (step 15 8 r (step 15 8 q (step 15 8 p (15,15)))) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fifteen_eleven : ∀ p q : Fin 12,
    11 < total (step 15 11 q (step 15 11 p (15,15))) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem twenty_fourteen : ∀ p q : Fin 15,
    14 < total (step 20 14 q (step 20 14 p (20,20))) := by decide

end Princess.FiveRowHighBudgetArithmetic
#print axioms Princess.FiveRowHighBudgetArithmetic.fifteen_eight
#print axioms Princess.FiveRowHighBudgetArithmetic.fifteen_eleven
#print axioms Princess.FiveRowHighBudgetArithmetic.twenty_fourteen
