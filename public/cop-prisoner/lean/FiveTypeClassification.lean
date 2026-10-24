import FiveFinite65
import FiveFinite70
import FiveFinite75
import FiveFullRing16
import FiveFullRing17
import FiveFullRing18
import FiveFullRing19
import FiveFullRing20
import FiveFullRing21
import FiveFullRing22
import FiveShortRing10
import FiveShortRing11
import MainUpperInterval
import MainSmallSparse

/-! Direct numerical consequences of the twelve finite five-type charts.
The ten full envelopes meet the established upper main interval at 3n.
The two shorter envelopes also provide sparse cores at their 2n endpoints. -/
namespace Delivery.FiveTypeClassification
open Extremal

def FullOrder (n : Nat) : Prop :=
  n=65 ∨ n=70 ∨ n=75 ∨ n=80 ∨ n=85 ∨ n=90 ∨ n=95 ∨ n=100 ∨ n=105 ∨ n=110

theorem full_lower {n m : Nat} (order : FullOrder n)
    (low : 2*n≤m) (high : m≤3*n) : IsMaximum n m (n*(n-1)-m) := by
  rcases order with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact FiveFinite65.maximum low high
  · exact FiveFinite70.maximum low high
  · exact FiveFinite75.maximum low high
  · exact FiveFullRing16.maximum low high
  · exact FiveFullRing17.maximum low high
  · exact FiveFullRing18.maximum low high
  · exact FiveFullRing19.maximum low high
  · exact FiveFullRing20.maximum low high
  · exact FiveFullRing21.maximum low high
  · exact FiveFullRing22.maximum low high

theorem maximum {n m : Nat} (order : FullOrder n)
    (low : 2*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  by_cases lower : m≤3*n
  · exact full_lower order low lower
  · have large : 25≤n := by unfold FullOrder at order; omega
    exact MainUpperInterval.maximum large (by omega) high

theorem short_lower {n m : Nat} (order : n=50 ∨ n=55)
    (low : 2*n≤m) (high : m≤2*n+n/5) : IsMaximum n m (n*(n-1)-m) := by
  rcases order with rfl|rfl
  · exact FiveShortRing10.maximum low high
  · exact FiveShortRing11.maximum low high

theorem sparse_even {n k : Nat} (order : k=50 ∨ k=55 ∨ FullOrder k)
    (host : k≤n) : IsMaximum n (2*k) (k*(k-3)) := by
  have large : 5≤k := by unfold FullOrder at order; omega
  apply MainSmallSparse.from_main_endpoint large host
  rcases order with rfl|rfl|full
  · exact FiveShortRing10.maximum (by decide) (by decide)
  · exact FiveShortRing11.maximum (by decide) (by decide)
  · exact full_lower full (Nat.le_refl _) (by omega)

#print axioms full_lower
#print axioms maximum
#print axioms short_lower
#print axioms sparse_even
end Delivery.FiveTypeClassification
