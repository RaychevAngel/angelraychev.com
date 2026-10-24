import SmallBudgetsToFive
import FunctionalEndpoint
import ExclusionCertificates

/-! Complete four-vertex joint table. Only the exceptional seven-arrow
upper bound needs a finite check: all twelve independent nonloop bits are
covered, and a stationary cop rules out all but at most one missing pair. -/
namespace Delivery.FourVertexClassification
open FiniteGame Extremal ExclusionCertificates

structure Bits4 where
  b01 : Bool
  b02 : Bool
  b03 : Bool
  b10 : Bool
  b12 : Bool
  b13 : Bool
  b20 : Bool
  b21 : Bool
  b23 : Bool
  b30 : Bool
  b31 : Bool
  b32 : Bool

def bit4 (b : Bits4) (s t : Fin 4) : Bool :=
  match s.val,t.val with
  | 0,1 => b.b01
  | 0,2 => b.b02
  | 0,3 => b.b03
  | 1,0 => b.b10
  | 1,2 => b.b12
  | 1,3 => b.b13
  | 2,0 => b.b20
  | 2,1 => b.b21
  | 2,3 => b.b23
  | 3,0 => b.b30
  | 3,1 => b.b31
  | 3,2 => b.b32
  | _,_ => false

def graph4 (b : Bits4) (s t : Fin 4) : Prop := bit4 b s t=true
instance (b : Bits4) : DecidableRel (graph4 b) := fun _ _ => inferInstanceAs (Decidable (_=true))
instance (b : Bits4) (s t : Fin 4) : Decidable (Legal (graph4 b) s t) :=
  inferInstanceAs (Decidable (_∨_))

def Candidate (b : Bits4) (s t : Fin 4) : Prop := s≠t ∧ ¬graph4 b s t ∧
  ∀ c : Fin 4, c≠s → ∃ z : Fin 4, graph4 b z t ∧ ¬Legal (graph4 b) c z
instance (b : Bits4) (s t : Fin 4) : Decidable (Candidate b s t) :=
  inferInstanceAs (Decidable (_∧_∧∀ _ : Fin 4,_→∃ _ : Fin 4,_∧_))

def candidateCount (b : Bits4) : Nat :=
  ((allPairs 4).filter fun p => decide (Candidate b p.1 p.2)).length

theorem graph4_complete (E : Graph (Fin 4)) (loops : Loopless E) :
    ∃ b, E=graph4 b := by
  classical
  let b : Bits4 := ⟨decide (E 0 1),decide (E 0 2),decide (E 0 3),decide (E 1 0),decide (E 1 2),decide (E 1 3),decide (E 2 0),decide (E 2 1),decide (E 2 3),decide (E 3 0),decide (E 3 1),decide (E 3 2)⟩
  refine ⟨b,?_⟩
  funext s t
  apply propext
  rcases s with ⟨s,hs⟩
  rcases t with ⟨t,ht⟩
  have sc : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
  have tc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases sc with rfl|rfl|rfl|rfl <;>
    rcases tc with rfl|rfl|rfl|rfl <;>
    simp [graph4,bit4,b,loops 0,loops 1,loops 2,loops 3]

theorem score_le_candidates (b : Bits4) : score (graph4 b)≤candidateCount b := by
  classical
  apply filter_length_mono
  intro p member
  simp only [decide_eq_true_eq] at *
  refine ⟨member.1,member.2.1,?_⟩
  intro c initial
  apply Classical.byContradiction
  intro absent
  have covers : ∀ z,graph4 b z p.2 → Legal (graph4 b) c z := by
    intro z edge
    apply Classical.byContradiction
    intro no
    exact absent ⟨z,edge,no⟩
  exact camping_not_guaranteed member.1 member.2.1 initial covers member.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seven_candidates (b : Bits4) :
    ((allPairs 4).filter fun p => decide (graph4 b p.1 p.2)).length=7 →
    candidateCount b≤1 := by
  rcases b with ⟨b01,b02,b03,b10,b12,b13,b20,b21,b23,b30,b31,b32⟩
  revert b01 b02 b03 b10 b12 b13 b20 b21 b23 b30 b31 b32
  decide +kernel

theorem seven_upper (E : Graph (Fin 4)) (loops : Loopless E)
    (budget : arcCount E=7) : score E≤1 := by
  obtain ⟨b,rfl⟩ := graph4_complete E loops
  rw [arcCount_eq] at budget
  exact Nat.le_trans (score_le_candidates b) (seven_candidates b budget)

def sevenGraph (s t : Fin 4) : Prop :=
  (s=0 ∧ (t=1 ∨ t=2)) ∨ (s=1 ∧ (t=0 ∨ t=2)) ∨
  (s=2 ∧ (t=0 ∨ t=3)) ∨ (s=3 ∧ t=1)
instance : DecidableRel sevenGraph := fun _ _ => inferInstanceAs (Decidable (_∨_∨_∨_))
instance (s t : Fin 4) : Decidable (Legal sevenGraph s t) := inferInstanceAs (Decidable (_∨_))
theorem seven_loopless : Loopless sevenGraph := by unfold Loopless; decide +kernel
theorem seven_arrows : arcCount sevenGraph=7 := by rw [arcCount_eq];decide +kernel

theorem seven_delivery : Guaranteed sevenGraph 2 1 := by
  have paths : ∀ c : Fin 4,c≠2 → ∃ z : Fin 4,
      sevenGraph 2 z ∧ sevenGraph z 1 ∧ ¬Legal sevenGraph c z := by decide +kernel
  intro c initial
  obtain ⟨z,first,last,safe⟩ := paths c initial
  exact ⟨2,DenseCounting.safe_intermediate_winning (Ne.symm initial) first last safe⟩

theorem seven_score : score sevenGraph=1 := by
  classical
  have upper := seven_upper sevenGraph seven_loopless seven_arrows
  have pair : Indirect sevenGraph 2 1 := ⟨by decide,by decide,seven_delivery⟩
  have member : (2,1)∈(allPairs 4).filter (fun p => decide (Indirect sevenGraph p.1 p.2)) := by
    simp [allPairs,List.mem_flatMap,List.mem_map,pair]
  have positive := List.length_pos_of_mem member
  change 0<score sevenGraph at positive
  omega

theorem maximum_seven : IsMaximum 4 7 1 :=
  ⟨seven_upper,sevenGraph,seven_loopless,seven_arrows,seven_score⟩

def value (m : Nat) : Nat := if m≤3 then 0 else if m=6 then 2 else if m≤8 then 1 else 0

theorem maximum (m : Nat) (admissible : m≤12) : IsMaximum 4 m (value m) := by
  by_cases small : m≤3
  · simpa [value,small] using SmallBudgetsToFive.maximum_zero (n:=4) (m:=m) admissible small
  · by_cases six : m=6
    · subst m
      exact SmallBudgetSix.maximum (by decide)
    · by_cases before : m≤5
      · simpa [value,small,six,show m≤8 by omega] using
          (SmallBudgetsToFive.maximum_one (n:=4) (m:=m) (by decide) (by omega) before)
      · by_cases seven : m=7
        · subst m
          exact maximum_seven
        · by_cases eight : m=8
          · subst m
            exact FunctionalEndpoint.maximum_endpoint (by decide : 2≤4)
          · simpa [value,small,six,show ¬m≤8 by omega] using
              (DenseZero.maximum_zero (n:=4) (m:=m) (by omega) admissible)

#print axioms seven_upper
#print axioms maximum
end Delivery.FourVertexClassification
