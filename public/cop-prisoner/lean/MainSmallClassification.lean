import MainSmall13
import MainSmall14
import MainSmall15
import MainSmall16
import MainSmall17
import MainSmall18

/-! The complete main interval at orders thirteen through eighteen. -/
namespace Delivery.MainSmallClassification
open Extremal
theorem maximum {n m : Nat} (lowOrder : 13≤n) (highOrder : n≤18)
    (low : 2*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  have cases : n=13 ∨ n=14 ∨ n=15 ∨ n=16 ∨ n=17 ∨ n=18 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact MainSmall13.maximum low high
  · exact MainSmall14.maximum low high
  · exact MainSmall15.maximum low high
  · exact MainSmall16.maximum low high
  · exact MainSmall17.maximum low high
  · exact MainSmall18.maximum low high
#print axioms maximum
end Delivery.MainSmallClassification
