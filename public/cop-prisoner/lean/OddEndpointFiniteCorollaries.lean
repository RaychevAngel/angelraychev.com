import OddEndpointConstruction

/-! Six smaller support orders use the same checked odd catalogue and
stronger residue-specific window thresholds. No new literal tables occur. -/
namespace Delivery.OddEndpointFiniteCorollaries
open OddEndpointGraph OddEndpointCounts OddEndpointAttainment
open FiniteGame Extremal

 theorem maximum_at_parameters {k host : Nat} (hk : 15≤k) (r : Case)
    (large : OddEndpointParameters.minimum r≤k) (order : 6*k-r.val≤host) :
    IsMaximum host (2*(6*k-r.val)-1) ((6*k-r.val-1)*(6*k-r.val-4)+2) := by
  have size := vertices_length hk r
  have residue := r.isLt
  have result := OddDefectScore.maximum_of_delivery
    (by omega : 6≤(vertices hk r).length) (by omega : (vertices hk r).length≤host)
    (graph hk r) (graph_loopless hk r) (graph_arcs hk r)
    (source hk r) (target hk r) (OddEndpointCounts.defect_distinct hk r)
    (out_one hk r) (in_one hk r) (OddEndpointCounts.defect_missing hk r)
    (fun s t hs ht _ _ => graph_guaranteed OddEndpointSavedCertificates.certificates hk r large s t hs ht)
  simpa only [size] using result

 theorem maximum_odd {host support : Nat}
    (supported : support=88 ∨ support=89 ∨ support=90 ∨ support=94 ∨ support=95 ∨ support=96)
    (order : support≤host) :
    IsMaximum host (2*support-1) ((support-1)*(support-4)+2) := by
  rcases supported with rfl|rfl|rfl|rfl|rfl|rfl
  · exact maximum_at_parameters (by decide : 15≤15) 2 (by decide) order
  · exact maximum_at_parameters (by decide : 15≤15) 1 (by decide) order
  · exact maximum_at_parameters (by decide : 15≤15) 0 (by decide) order
  · exact maximum_at_parameters (by decide : 15≤16) 2 (by decide) order
  · exact maximum_at_parameters (by decide : 15≤16) 1 (by decide) order
  · exact maximum_at_parameters (by decide : 15≤16) 0 (by decide) order

#print axioms maximum_at_parameters
#print axioms maximum_odd
end Delivery.OddEndpointFiniteCorollaries
