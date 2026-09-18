import FiniteGame

/-! Definitions and counting interfaces for the finite extremal problem.
No closed formula for the maximum is assumed by these definitions. -/
namespace Delivery.Extremal
open FiniteGame

def Loopless {V : Type} (E : Graph V) : Prop := ∀ v, ¬ E v v

def allPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun s => (List.finRange n).map fun t => (s,t)

def Indirect {V : Type} (E : Graph V) (s t : V) : Prop :=
  s ≠ t ∧ ¬ E s t ∧ Guaranteed E s t

noncomputable def arcCount {n : Nat} (E : Graph (Fin n)) : Nat := by
  classical
  exact ((allPairs n).filter fun p => decide (E p.1 p.2)).length

noncomputable def missingCount {n : Nat} (E : Graph (Fin n)) : Nat := by
  classical
  exact ((allPairs n).filter fun p => decide (p.1 ≠ p.2 ∧ ¬ E p.1 p.2)).length

noncomputable def score {n : Nat} (E : Graph (Fin n)) : Nat := by
  classical
  exact ((allPairs n).filter fun p => decide (Indirect E p.1 p.2)).length

theorem arcCount_eq {n : Nat} (E : Graph (Fin n)) [DecidableRel E] :
    arcCount E = ((allPairs n).filter fun p => decide (E p.1 p.2)).length := by
  unfold arcCount
  apply congrArg (fun p => ((allPairs n).filter p).length)
  funext p
  exact decide_eq_decide.mpr Iff.rfl

theorem missingCount_eq {n : Nat} (E : Graph (Fin n)) [DecidableRel E] :
    missingCount E =
      ((allPairs n).filter fun p => decide (p.1 ≠ p.2 ∧ ¬ E p.1 p.2)).length := by
  unfold missingCount
  apply congrArg (fun p => ((allPairs n).filter p).length)
  funext p
  exact decide_eq_decide.mpr Iff.rfl

/-- The exact maximum includes both an unrestricted upper bound and an
attaining loopless graph with precisely the prescribed number of arrows. -/
def IsMaximum (n m value : Nat) : Prop :=
  (∀ E : Graph (Fin n), Loopless E → arcCount E = m → score E ≤ value) ∧
  ∃ E : Graph (Fin n), Loopless E ∧ arcCount E = m ∧ score E = value

theorem filter_length_mono {α : Type} (xs : List α) (p q : α → Bool)
    (implies : ∀ x, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hp : p x = true
      · have hq := implies x hp
        simp [hp, hq]
        exact ih
      · simp only [Bool.not_eq_true] at hp
        cases hq : q x <;> simp [hp, hq] <;> omega

theorem score_le_missing {n : Nat} (E : Graph (Fin n)) :
    score E ≤ missingCount E := by
  classical
  apply filter_length_mono
  intro p hp
  simp only [decide_eq_true_eq] at *
  exact ⟨hp.1, hp.2.1⟩

theorem score_eq_zero {n : Nat} (E : Graph (Fin n))
    (blocked : ∀ s t, s ≠ t → ¬ E s t → ¬ Guaranteed E s t) : score E = 0 := by
  classical
  have noIndirect : ∀ p : Fin n × Fin n, ¬ Indirect E p.1 p.2 := by
    intro p h
    exact blocked p.1 p.2 h.1 h.2.1 h.2.2
  simp [score, noIndirect]

theorem score_eq_missing {n : Nat} (E : Graph (Fin n))
    (allGuaranteed : ∀ s t, s ≠ t → ¬ E s t → Guaranteed E s t) :
    score E = missingCount E := by
  classical
  have same : ∀ p : Fin n × Fin n,
      Indirect E p.1 p.2 ↔ p.1 ≠ p.2 ∧ ¬ E p.1 p.2 := by
    intro p
    exact ⟨fun h => ⟨h.1,h.2.1⟩,
      fun h => ⟨h.1,h.2,allGuaranteed p.1 p.2 h.1 h.2⟩⟩
  simp only [score, missingCount, same]

theorem maximum_unique {n m a b : Nat}
    (ha : IsMaximum n m a) (hb : IsMaximum n m b) : a = b := by
  obtain ⟨Ea, loopA, arcsA, scoreA⟩ := ha.2
  obtain ⟨Eb, loopB, arcsB, scoreB⟩ := hb.2
  have hab := hb.1 Ea loopA arcsA
  have hba := ha.1 Eb loopB arcsB
  omega

#print axioms score_le_missing
#print axioms score_eq_zero
#print axioms score_eq_missing
#print axioms maximum_unique
end Delivery.Extremal
