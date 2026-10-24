import LowBandPrefix
import LowBandCertificates

/-! Unconditional lower main-interval construction. The finite catalogue is
discharged by the 696 literal, kernel-checked local objectives. -/
namespace Delivery.LowBandConstruction
open FiniteGame Extremal

noncomputable def attainer (n : Nat) (large : 115≤n) (m : Nat) : Graph (Fin n) :=
  LowBandPrefix.attainer n large m

/-- The lexicographic optional-edge prefix has the prescribed budget and
attains every missing ordered pair through the stronger envelope endpoint. -/
theorem attainer_exact {n m : Nat} (large : 115≤n) (low : 2*n≤m)
    (high : m≤LowBandPrefix.top n) :
    Loopless (attainer n large m) ∧ arcCount (attainer n large m)=m ∧
      score (attainer n large m)=n*(n-1)-m :=
  LowBandPrefix.attainer_exact LowBandCertificates.certificates large low high

theorem maximum {n m : Nat} (large : 115≤n) (low : 2*n≤m)
    (high : m≤LowBandPrefix.top n) : IsMaximum n m (n*(n-1)-m) :=
  LowBandPrefix.maximum LowBandCertificates.certificates large low high

theorem low_band {n m : Nat} (large : 115≤n) (low : 2*n≤m)
    (high : m≤3*n) : IsMaximum n m (n*(n-1)-m) :=
  LowBandPrefix.low_band LowBandCertificates.certificates large low high

/-- The robust optional prefixes meet the pair-code interval at 3n. -/
theorem main_interval {n m : Nat} (large : 115≤n) (low : 2*n≤m)
    (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) :=
  LowBandPrefix.main_interval LowBandCertificates.certificates large low high

#print axioms attainer_exact
#print axioms main_interval
end Delivery.LowBandConstruction
