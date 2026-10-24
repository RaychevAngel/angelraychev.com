import MainSmallClassification
import SparseAttainment

/-! The small main-interval endpoints supply the sparse even cores. No
separate finite even-certificate catalogue is needed at these orders. -/
namespace Delivery.MainSmallSparse
open Extremal

theorem from_main_endpoint {n k : Nat} (size : 5≤k) (host : k≤n)
    (endpoint : IsMaximum k (2*k) (k*(k-1)-2*k)) :
    IsMaximum n (2*k) (k*(k-3)) := by
  obtain ⟨E,noLoops,budget,count⟩ := endpoint.2
  have subtraction : k*(k-1)-2*k=k*(k-3) := by
    rw [show k-1=k-3+2 by omega,Nat.mul_add,Nat.mul_comm k 2,
      Nat.add_sub_cancel]
  exact SparseAttainment.maximum_even_of_core size host E noLoops budget
    (count.trans subtraction)

theorem maximum {n k : Nat} (size : 12≤k) (small : k≤18) (host : k≤n) :
    IsMaximum n (2*k) (k*(k-3)) := by
  by_cases twelve : k=12
  · subst k
    exact SparseAttainment.maximum_twentyfour host
  have capacity : 2*k≤k*(k-3) := by
    have bound := Nat.mul_le_mul_left k (show 2≤k-3 by omega)
    simpa only [Nat.mul_comm k 2] using bound
  exact from_main_endpoint (by omega) host
    (MainSmallClassification.maximum (by omega) small (Nat.le_refl _) capacity)

#print axioms from_main_endpoint
#print axioms maximum
end Delivery.MainSmallSparse
