import LocalArena

/-! Safe transfers may make variable progress, provided every possible safe
handoff strictly lowers one natural measure. This generalizes a fixed stage
chain without omitting the intervening pursuer response. -/
namespace Delivery.SafeProgress
open FiniteGame LocalArena

/-- Eligibility can exclude a defective source at every handoff. The bound is
on actual messenger moves; delivery still has its usual terminal priority. -/
theorem winning {V : Type} {E : Graph V} (Eligible : V → Prop)
    (measure : V → Nat) (transferBound deliveryBound : Nat) (t : V)
    (transfer : ∀ r c, Eligible r → r≠c → 0<measure r →
      SafeReach E (fun z => Eligible z ∧ measure z<measure r) transferBound r c)
    (finish : ∀ r c, Eligible r → r≠c → measure r=0 →
      Winning E t deliveryBound r c)
    (r c : V) (eligible : Eligible r) (safe : r≠c) :
    Winning E t (measure r*transferBound+deliveryBound) r c := by
  generalize eq : measure r=m
  induction m using Nat.strongRecOn generalizing r c with
  | ind m ih =>
    by_cases zero : m=0
    · have result := finish r c eligible safe (by omega)
      simpa only [zero,Nat.zero_mul,Nat.zero_add] using result
    · have positive : 0<measure r := by omega
      have next : ∀ z d, (Eligible z ∧ measure z<measure r) → z≠d →
          Winning E t ((m-1)*transferBound+deliveryBound) z d := by
        intro z d goal distinct
        have small : measure z<m := by omega
        have result := ih (measure z) small z d goal.1 distinct rfl
        have bound := Nat.mul_le_mul_right transferBound (show measure z≤m-1 by omega)
        exact winning_mono result (by omega)
      have result := safe_then_delivery (transfer r c eligible safe positive) next
      have successor : m-1+1=m := by omega
      have budget : transferBound+((m-1)*transferBound+deliveryBound)=
          m*transferBound+deliveryBound := by
        calc
          _=((m-1)+1)*transferBound+deliveryBound := by
            rw [Nat.add_mul,Nat.one_mul]
            omega
          _=m*transferBound+deliveryBound := by rw [successor]
      simpa only [budget] using result

#print axioms winning
end Delivery.SafeProgress
