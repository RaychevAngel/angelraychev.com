import FiveVertexReduction
import FiveVertexPositive
import SmallBudgetEight
import FiveVertexWitness08
import FiveVertexWitness09
import FiveVertexWitness10
import FiveVertexWitness11
import FiveVertexWitness12
import FiveVertexWitness13
import FiveVertexWitness14

/-! The complete five-vertex table, with sharp unrestricted upper bounds
and retained literal attainers. All certificate premises are instantiated. -/
namespace Delivery.FiveVertexClassification
open FiniteGame Extremal

theorem middle_upper (E : Graph (Fin 5)) (loops : Loopless E)
    (budget : 9≤arcCount E ∧ arcCount E≤14) :
    score E≤if arcCount E≤11 then 3 else 2 :=
  FiveVertexReduction.upper_with_positive FiveVertexPositive.upper E loops budget

theorem maximum_8 : IsMaximum 5 8 4 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=8) : score E≤4 := SmallBudgetEight.upper E loops budget
  have hi := upper FiveVertexWitness08.edge FiveVertexWitness08.loopless FiveVertexWitness08.arrows
  have lo := FiveVertexWitness08.lower
  exact ⟨upper,FiveVertexWitness08.edge,FiveVertexWitness08.loopless,FiveVertexWitness08.arrows,by omega⟩

theorem maximum_9 : IsMaximum 5 9 3 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=9) : score E≤3 := by
      have h := middle_upper E loops (by omega)
      simpa [budget] using h
  have hi := upper FiveVertexWitness09.edge FiveVertexWitness09.loopless FiveVertexWitness09.arrows
  have lo := FiveVertexWitness09.lower
  exact ⟨upper,FiveVertexWitness09.edge,FiveVertexWitness09.loopless,FiveVertexWitness09.arrows,by omega⟩

theorem maximum_10 : IsMaximum 5 10 3 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=10) : score E≤3 := by
      have h := middle_upper E loops (by omega)
      simpa [budget] using h
  have hi := upper FiveVertexWitness10.edge FiveVertexWitness10.loopless FiveVertexWitness10.arrows
  have lo := FiveVertexWitness10.lower
  exact ⟨upper,FiveVertexWitness10.edge,FiveVertexWitness10.loopless,FiveVertexWitness10.arrows,by omega⟩

theorem maximum_11 : IsMaximum 5 11 3 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=11) : score E≤3 := by
      have h := middle_upper E loops (by omega)
      simpa [budget] using h
  have hi := upper FiveVertexWitness11.edge FiveVertexWitness11.loopless FiveVertexWitness11.arrows
  have lo := FiveVertexWitness11.lower
  exact ⟨upper,FiveVertexWitness11.edge,FiveVertexWitness11.loopless,FiveVertexWitness11.arrows,by omega⟩

theorem maximum_12 : IsMaximum 5 12 2 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=12) : score E≤2 := by
      have h := middle_upper E loops (by omega)
      simpa [budget] using h
  have hi := upper FiveVertexWitness12.edge FiveVertexWitness12.loopless FiveVertexWitness12.arrows
  have lo := FiveVertexWitness12.lower
  exact ⟨upper,FiveVertexWitness12.edge,FiveVertexWitness12.loopless,FiveVertexWitness12.arrows,by omega⟩

theorem maximum_13 : IsMaximum 5 13 2 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=13) : score E≤2 := by
      have h := middle_upper E loops (by omega)
      simpa [budget] using h
  have hi := upper FiveVertexWitness13.edge FiveVertexWitness13.loopless FiveVertexWitness13.arrows
  have lo := FiveVertexWitness13.lower
  exact ⟨upper,FiveVertexWitness13.edge,FiveVertexWitness13.loopless,FiveVertexWitness13.arrows,by omega⟩

theorem maximum_14 : IsMaximum 5 14 2 := by
  have upper (E : Graph (Fin 5)) (loops : Loopless E)
      (budget : arcCount E=14) : score E≤2 := by
      have h := middle_upper E loops (by omega)
      simpa [budget] using h
  have hi := upper FiveVertexWitness14.edge FiveVertexWitness14.loopless FiveVertexWitness14.arrows
  have lo := FiveVertexWitness14.lower
  exact ⟨upper,FiveVertexWitness14.edge,FiveVertexWitness14.loopless,FiveVertexWitness14.arrows,by omega⟩

/-- The stronger eight-arrow attainer needs only five host vertices. -/
theorem eight_padded {n : Nat} (order : 5≤n) : IsMaximum n 8 4 := by
  refine ⟨fun E loops budget => SmallBudgetEight.upper E loops budget,?_⟩
  obtain ⟨E,loops,arcs,score⟩ := maximum_8.2
  obtain ⟨F,fl,fa,fs⟩ := GraphPadding.pad_to_order E loops order
  exact ⟨F,fl,fa.trans arcs,fs.trans score⟩

def value (m : Nat) : Nat :=
  if m≤3 then 0 else if m≤5 then 1 else if m≤7 then 2
  else if m=8 then 4 else if m≤11 then 3 else if m≤14 then 2
  else if m=15 then 1 else 0

theorem maximum (m : Nat) (admissible : m≤20) : IsMaximum 5 m (value m) := by
  by_cases small : m≤3
  · simpa [value,small] using SmallBudgetsToFive.maximum_zero (n:=5) (m:=m) admissible small
  · by_cases five : m≤5
    · simpa [value,small,five] using
        (SmallBudgetsToFive.maximum_one (n:=5) (m:=m) (by decide) (by omega) five)
    · by_cases finite : m≤15
      · have cases : m=6 ∨ m=7 ∨ m=8 ∨ m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 := by omega
        rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · exact SmallBudgetSix.maximum (by decide)
        · exact SmallBudgetSeven.maximum (by decide)
        · exact maximum_8
        · exact maximum_9
        · exact maximum_10
        · exact maximum_11
        · exact maximum_12
        · exact maximum_13
        · exact maximum_14
        · exact FunctionalEndpoint.maximum_endpoint (by decide : 2≤5)
      · simpa [value,small,five,show ¬m≤7 by omega,show m≠8 by omega,
          show ¬m≤11 by omega,show ¬m≤14 by omega,show m≠15 by omega] using
            (DenseZero.maximum_zero (n:=5) (m:=m) (by omega) admissible)

#print axioms maximum
#print axioms eight_padded
end Delivery.FiveVertexClassification
