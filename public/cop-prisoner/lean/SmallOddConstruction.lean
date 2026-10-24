import SmallOddWitness13
import SmallOddWitness14
import SmallOddWitness15
import SmallOddWitness16
import SmallOddWitness17
import SmallOddWitness18
import SparseParity
import GraphPadding

/-! The retained six odd witnesses attain the unrestricted sparse parity
bound on their original supports and every larger host by isolated padding. -/
namespace Delivery.SmallOddConstruction
open FiniteGame Extremal

theorem maximum_of_exact {support host : Nat} (large : 6≤support)
    (order : support≤host) (E : Graph (Fin support)) (loops : Loopless E)
    (arrows : arcCount E=2*support-1)
    (value : score E=(support-1)*(support-4)+2) :
    IsMaximum host (2*support-1) ((support-1)*(support-4)+2) := by
  obtain ⟨F,loopF,arrowF,valueF⟩ := GraphPadding.pad_to_order E loops order
  refine ⟨?_,F,loopF,arrowF.trans arrows,valueF.trans value⟩
  intro G loopG budget
  have bound := SparseParity.odd_upper G loopG (k := support-1)
    (by omega) (by omega)
  simpa only [Nat.sub_sub] using bound

theorem maximum_odd {host support : Nat} (low : 13≤support)
    (high : support≤18) (order : support≤host) :
    IsMaximum host (2*support-1) ((support-1)*(support-4)+2) := by
  have cases : support=13 ∨ support=14 ∨ support=15 ∨
      support=16 ∨ support=17 ∨ support=18 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · exact maximum_of_exact (by decide) order SmallOddWitness13.edge
      SmallOddWitness13.loopless SmallOddWitness13.arrows
      SmallOddWitness13.exact_score
  · exact maximum_of_exact (by decide) order SmallOddWitness14.edge
      SmallOddWitness14.loopless SmallOddWitness14.arrows
      SmallOddWitness14.exact_score
  · exact maximum_of_exact (by decide) order SmallOddWitness15.edge
      SmallOddWitness15.loopless SmallOddWitness15.arrows
      SmallOddWitness15.exact_score
  · exact maximum_of_exact (by decide) order SmallOddWitness16.edge
      SmallOddWitness16.loopless SmallOddWitness16.arrows
      SmallOddWitness16.exact_score
  · exact maximum_of_exact (by decide) order SmallOddWitness17.edge
      SmallOddWitness17.loopless SmallOddWitness17.arrows
      SmallOddWitness17.exact_score
  · exact maximum_of_exact (by decide) order SmallOddWitness18.edge
      SmallOddWitness18.loopless SmallOddWitness18.arrows
      SmallOddWitness18.exact_score

#print axioms maximum_of_exact
#print axioms maximum_odd
end Delivery.SmallOddConstruction
