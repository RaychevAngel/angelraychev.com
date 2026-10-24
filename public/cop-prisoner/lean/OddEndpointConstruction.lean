import OddEndpointAttainment
import OddEndpointSavedCertificates

/-! The explicit odd sparse attainer at every support order at least98.
All 847 required local objectives are supplied by the two frozen archives
and checked in Lean against the actual padded local arenas. -/
namespace Delivery.OddEndpointConstruction
open OddEndpointGraph OddEndpointCertificatesSpec FiniteGame Extremal

def attainer (n : Nat) (large : 98≤n) : Graph (Fin n) :=
  OddEndpointAttainment.attainer n large

theorem attainer_exact (n : Nat) (large : 98≤n) :
    Loopless (attainer n large) ∧ arcCount (attainer n large)=2*n-1 ∧
      score (attainer n large)=(n-1)*(n-4)+2 :=
  OddEndpointAttainment.attainer_exact OddEndpointSavedCertificates.certificates n large

theorem winning {k : Nat} (hk : 15≤k) (r : Case)
    (large : OddEndpointParameters.minimum r≤k) (t s c : Vertex hk r)
    (ordinary : s≠lowSource hk r) (recipient : t≠lowTarget hk r) (safe : s≠c) :
    Winning (edge hk r) t
      (OddEndpointComposition.measure hk r t s*transferBound r+deliveryBound r) s c := by
  have bounds := OddEndpointParameters.projection_bounds r large
  exact OddEndpointComposition.winning hk r bounds.2 bounds.1
    (OddEndpointSavedCertificates.certificates r) t s c ordinary recipient safe

theorem maximum_odd {host support : Nat} (large : 98≤support) (order : support≤host) :
    IsMaximum host (2*support-1) ((support-1)*(support-4)+2) :=
  OddEndpointAttainment.maximum_odd OddEndpointSavedCertificates.certificates large order

#print axioms attainer_exact
#print axioms winning
#print axioms maximum_odd
end Delivery.OddEndpointConstruction
