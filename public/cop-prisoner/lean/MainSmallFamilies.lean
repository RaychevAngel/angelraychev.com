import MainTiny13
import MainTiny14
import TwelveHubCodes
import PairCodeConstruction
import SmallDenseEnvelopeMaxima
import CircleConstruction

/-! Arithmetic instances needed for the short main-interval bridge. -/
namespace Delivery.MainSmallFamilies
open Extremal DenseCombinatorics

theorem circle16 {m : Nat} (low : 80≤m) (high : m≤112) : IsMaximum 16 m (240-m) :=
  CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide)
    (by decide) low high

theorem circle17 {m : Nat} (low : 85≤m) (high : m≤102) : IsMaximum 17 m (272-m) := by
  apply CircleConstruction.guarded_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) low
  have count : card (fun d : Fin 17 => CircleGuarded.Allowed 17 7 d.val)=7 := by
    unfold CircleGuarded.Allowed CircleEnvelope.Allowed
    rw [card_eq]
    decide +kernel
  simpa only [count] using high

theorem circle18 {m : Nat} (low : 90≤m) (high : m≤108) : IsMaximum 18 m (306-m) := by
  apply CircleConstruction.guarded_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) low
  have count : card (fun d : Fin 18 => CircleGuarded.Allowed 18 7 d.val)=7 := by
    unfold CircleGuarded.Allowed CircleEnvelope.Allowed
    rw [card_eq]
    decide +kernel
  simpa only [count] using high

#print axioms circle16
#print axioms circle17
#print axioms circle18
end Delivery.MainSmallFamilies
