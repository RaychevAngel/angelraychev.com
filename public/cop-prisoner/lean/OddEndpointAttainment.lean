import OddEndpointComposition
import OddEndpointCounts
import OddDefectScore

/-! Actual odd core scores and unrestricted maxima, with the saved finite
catalogue stated explicitly as the sole remaining certificate input. -/
namespace Delivery.OddEndpointAttainment
open OddEndpointGraph OddEndpointCounts OddEndpointCertificatesSpec
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

 theorem out_one {k : Nat} (hk : 15≤k) (r : Case) :
    outdegree (graph hk r) (source hk r)=1 := by
  classical
  change card (graph hk r (source hk r))=1
  simpa only [ne_eq,not_true_eq_false,ite_false] using row_count hk r (source hk r)

 theorem in_one {k : Nat} (hk : 15≤k) (r : Case) :
    indegree (graph hk r) (target hk r)=1 := by
  classical
  unfold indegree
  rw [card_congr (graph_incoming hk r)]
  exact card_singleton (fromVertex (predecessor hk r))

 theorem graph_guaranteed
    (certificates : ∀ r a, Catalogued r a → Certificates r a)
    {k : Nat} (hk : 15≤k) (r : Case) (large : OddEndpointParameters.minimum r≤k)
    (s t : Fin (vertices hk r).length) (ordinary : s≠source hk r)
    (recipient : t≠target hk r) : Guaranteed (graph hk r) s t := by
  have sizes := OddEndpointParameters.projection_bounds r large
  apply ((graphIso hk r).guaranteed_iff s t).mpr
  apply OddEndpointComposition.guaranteed hk r sizes.2 sizes.1 (certificates r)
  · intro same
    apply ordinary
    simpa only [graphIso,from_to,source] using congrArg fromVertex same
  · intro same
    apply recipient
    simpa only [graphIso,from_to,target] using congrArg fromVertex same

 theorem graph_score
    (certificates : ∀ r a, Catalogued r a → Certificates r a)
    {k : Nat} (hk : 15≤k) (r : Case) (large : OddEndpointParameters.minimum r≤k) :
    score (graph hk r)=((vertices hk r).length-1)*((vertices hk r).length-4)+2 := by
  have size := vertices_length hk r
  have residue := r.isLt
  apply OddDefectScore.score_exact (by omega) (graph hk r)
    (graph_loopless hk r) (graph_arcs hk r) (source hk r) (target hk r)
    (OddEndpointCounts.defect_distinct hk r) (out_one hk r) (in_one hk r)
    (OddEndpointCounts.defect_missing hk r)
  exact fun s t hs ht _ _ => graph_guaranteed certificates hk r large s t hs ht

 theorem ring_large {n : Nat} (large : 98≤n) :
    15≤OddEndpointParameters.circumferenceOf n := by
  unfold OddEndpointParameters.circumferenceOf
  omega

 theorem core_order {n : Nat} (large : 98≤n) :
    (vertices (ring_large large) (OddEndpointParameters.residue n)).length=n := by
  rw [vertices_length]
  have size := OddEndpointParameters.size n
  omega

 def attainer (n : Nat) (large : 98≤n) : Graph (Fin n) :=
  fun s t => graph (ring_large large) (OddEndpointParameters.residue n)
    (Fin.cast (core_order large).symm s) (Fin.cast (core_order large).symm t)

 def attainerIso (n : Nat) (large : 98≤n) :
    GraphRelabeling.Iso (graph (ring_large large) (OddEndpointParameters.residue n))
      (attainer n large) where
  toFun := Fin.cast (core_order large)
  invFun := Fin.cast (core_order large).symm
  left_inv _ := rfl
  right_inv _ := rfl
  edge_iff _ _ := Iff.rfl

 theorem attainer_exact
    (certificates : ∀ r a, Catalogued r a → Certificates r a)
    (n : Nat) (large : 98≤n) :
    Loopless (attainer n large) ∧ arcCount (attainer n large)=2*n-1 ∧
      score (attainer n large)=(n-1)*(n-4)+2 := by
  let r := OddEndpointParameters.residue n
  have needed := OddEndpointParameters.circumference r large (OddEndpointParameters.size n)
  have iso := attainerIso n large
  refine ⟨iso.loopless (graph_loopless (ring_large large) r),?_,?_⟩
  · have arrows := (GraphRelabeling.arcCount_eq iso).symm.trans (graph_arcs (ring_large large) r)
    simpa only [r,core_order large] using arrows
  · have value := (GraphRelabeling.score_eq iso).symm.trans
      (graph_score certificates (ring_large large) r needed)
    simpa only [r,core_order large] using value

 theorem core_exists
    (certificates : ∀ r a, Catalogued r a → Certificates r a)
    (n : Nat) (large : 98≤n) :
    ∃ E : Graph (Fin n), Loopless E ∧ arcCount E=2*n-1 ∧ score E=(n-1)*(n-4)+2 :=
  ⟨attainer n large,attainer_exact certificates n large⟩

 theorem maximum_odd
    (certificates : ∀ r a, Catalogued r a → Certificates r a)
    {host support : Nat} (large : 98≤support) (order : support≤host) :
    IsMaximum host (2*support-1) ((support-1)*(support-4)+2) := by
  obtain ⟨E,loops,arcs,value⟩ := core_exists certificates support large
  have upper : ∀ F : Graph (Fin host), Loopless F → arcCount F=2*support-1 →
      score F≤(support-1)*(support-4)+2 := by
    intro F loopF arcsF
    have result := SparseParity.odd_upper F loopF (k:=support-1) (by omega) (by omega)
    simpa only [Nat.sub_sub] using result
  refine ⟨upper,?_⟩
  obtain ⟨F,loopF,arcsF,valueF⟩ := GraphPadding.pad_to_order E loops order
  exact ⟨F,loopF,arcsF.trans arcs,valueF.trans value⟩

#print axioms graph_score
#print axioms attainer_exact
#print axioms core_exists
#print axioms maximum_odd
end Delivery.OddEndpointAttainment
