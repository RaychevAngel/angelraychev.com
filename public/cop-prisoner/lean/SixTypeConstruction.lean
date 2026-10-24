import SixTypeCounts
import SixTypeCertificates

/-! The uniform sparse attainer at every support order at least 85.
All canonical local objectives are supplied by literal kernel certificates.
The finite orders below 85 and the odd endpoint family remain separate. -/
namespace Delivery.SixTypeConstruction
open SixTypeGraph SixTypeLocal SixTypeProjection FiniteGame Extremal

theorem winning {k r : Nat} (hk : 15≤k) (hr : r≤5)
    (s c t : Vertex (holes (k:=k) r)) (safe : s≠c) :
    Winning (edge (holes r)) t (9*k+18) s c := by
  apply SixTypeComposition.winning hk (holes r) _ s c t safe
  intro base
  rw [canonical_crop]
  exact SixTypeCertificates.certificates _
    (SparseCropCoverage.coverage k r base.val hk hr base.isLt)

theorem core_exists (n : Nat) (large : 85≤n) :
    ∃ E : Graph (Fin n), Loopless E ∧ arcCount E=2*n ∧ score E=n*(n-3) :=
  SixTypeCounts.core_exists SixTypeCertificates.certificates n large

theorem maximum_even {n support : Nat} (large : 85≤support) (order : support≤n) :
    IsMaximum n (2*support) (support*(support-3)) := by
  obtain ⟨E,loopless,arcs,score⟩ := core_exists support large
  exact SparseAttainment.maximum_even_of_core (by omega) order E loopless arcs score

#print axioms winning
#print axioms core_exists
#print axioms maximum_even
end Delivery.SixTypeConstruction
