import LowBandCounts
import PairCodeOverlap

/-! Explicit optional prefixes and the complete large-order main interval.
The only supplied premise is the finite catalogue of local certificates. -/
namespace Delivery.LowBandPrefix
open SixTypeGraph SixTypeCounts LowBandCounts FiniteGame Extremal

def ring (n : Nat) : Nat := (n+5)/6
def removals (n : Nat) : Nat := 6*ring n-n
def top (n : Nat) : Nat := 20*ring n-11*removals n

theorem parameters {n : Nat} (large : 115≤n) : 20≤ring n ∧ removals n≤5 := by
  dsimp [ring,removals]; omega
theorem order {n : Nat} (large : 115≤n) : (vertices (ring n) (removals n)).length=n := by
  have bounds := parameters large
  rw [vertices_length (by omega) bounds.2]
  dsimp [ring,removals]
  omega
theorem top_covers {n : Nat} (large : 115≤n) : 3*n≤top n := by
  have bounds := parameters large
  have near : 6*ring n-removals n=n := by dsimp [ring,removals]; omega
  unfold top
  omega

noncomputable def prefixGraph (k r m : Nat) : Graph (Fin (vertices k r).length) :=
  PrefixEnvelope.graph (graph k r) (upperGraph k r) (m-2*(vertices k r).length)

theorem prefix_exact
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {k r m : Nat} (hk : 20≤k) (hr : r≤5)
    (low : 2*(vertices k r).length≤m) (high : m≤20*k-11*r) :
    Loopless (prefixGraph k r m) ∧ arcCount (prefixGraph k r m)=m ∧
      score (prefixGraph k r m)=(vertices k r).length*((vertices k r).length-1)-m := by
  have base := graph_arcs (r:=r) (by omega : 15≤k)
  have upper := upper_arcs hk hr
  have length := PrefixEnvelope.optional_length (graph k r) (upperGraph k r) (graph_subset k r)
  have range : m-2*(vertices k r).length≤(PrefixEnvelope.optional (graph k r) (upperGraph k r)).length := by omega
  have budget : arcCount (graph k r)+(m-2*(vertices k r).length)=m := by omega
  refine ⟨PrefixEnvelope.loopless _ _ _ (graph_subset k r) (upper_loopless k r),?_,?_⟩
  · exact (PrefixEnvelope.arc_count _ _ _ range).trans budget
  · have result := GuaranteedPrefix.score_count _ _ _ (graph_subset k r)
      (upper_loopless k r) (delivers cert hk hr) range
    simpa only [prefixGraph,budget] using result

noncomputable def attainer (n : Nat) (large : 115≤n) (m : Nat) : Graph (Fin n) :=
  fun s t => prefixGraph (ring n) (removals n) m
    (Fin.cast (order large).symm s) (Fin.cast (order large).symm t)

def attainerIso (n : Nat) (large : 115≤n) (m : Nat) :
    GraphRelabeling.Iso (prefixGraph (ring n) (removals n) m) (attainer n large m) where
  toFun := Fin.cast (order large)
  invFun := Fin.cast (order large).symm
  left_inv _ := rfl
  right_inv _ := rfl
  edge_iff _ _ := Iff.rfl

theorem attainer_exact
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {n m : Nat} (large : 115≤n) (low : 2*n≤m) (high : m≤top n) :
    Loopless (attainer n large m) ∧ arcCount (attainer n large m)=m ∧
      score (attainer n large m)=n*(n-1)-m := by
  have bounds := parameters large
  have data := prefix_exact cert bounds.1 bounds.2
    (m:=m) (by simpa only [order large] using low) high
  have iso := attainerIso n large m
  refine ⟨iso.loopless data.1,(GraphRelabeling.arcCount_eq iso).symm.trans data.2.1,?_⟩
  calc
    score (attainer n large m)=score (prefixGraph (ring n) (removals n) m) := (GraphRelabeling.score_eq iso).symm
    _=(vertices (ring n) (removals n)).length*((vertices (ring n) (removals n)).length-1)-m := data.2.2
    _=n*(n-1)-m := congrArg (fun N => N*(N-1)-m) (order large)

theorem maximum
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {n m : Nat} (large : 115≤n) (low : 2*n≤m) (high : m≤top n) :
    IsMaximum n m (n*(n-1)-m) := by
  have bounds := parameters large
  have size : 6*ring n-removals n=n := by dsimp [ring,removals]; omega
  have result := maximum_at_parameters cert bounds.1 bounds.2 (m:=m)
    (by simpa only [size] using low) high
  simpa only [order large] using result

theorem low_band
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {n m : Nat} (large : 115≤n) (low : 2*n≤m) (high : m≤3*n) :
    IsMaximum n m (n*(n-1)-m) :=
  maximum cert large low (Nat.le_trans high (top_covers large))

theorem main_interval
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {n m : Nat} (large : 115≤n) (low : 2*n≤m) (high : m≤n*(n-3)) :
    IsMaximum n m (n*(n-1)-m) := by
  by_cases sparse : m≤3*n
  · exact low_band cert large low sparse
  · exact PairCodeOverlap.maximum (by omega) (by omega) high

#print axioms attainer_exact
#print axioms main_interval
end Delivery.LowBandPrefix
