import SmallBudgetSix
import DenseCounting

/-! The first six arrow budgets, including prescribed attaining graphs.
The four-arrow diamond and its one-arrow extension suffice; no enumeration
of graphs or game states is required. -/
namespace Delivery.SmallBudgetsToFive
open FiniteGame Extremal SparseParity

theorem zero_upper {n m : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=m) (small : m≤3) : score E=0 := by
  have bound := SparseParity.upper E loops
  rw [budget] at bound
  have cases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [budgetBound] at bound <;> omega

theorem one_upper {n m : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=m) (small : m≤5) : score E≤1 := by
  have bound := SparseParity.upper E loops
  rw [budget] at bound
  have cases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [budgetBound] at bound <;> omega

def diamond (extra : Bool) (s t : Fin 4) : Prop :=
  (s=0 ∧ (t=1 ∨ t=2)) ∨ ((s=1 ∨ s=2) ∧ t=3) ∨
    (extra=true ∧ s=3 ∧ t=0)
instance (extra : Bool) : DecidableRel (diamond extra) :=
  fun _ _ => inferInstanceAs (Decidable (_∨_∨_))

instance (extra : Bool) (s t : Fin 4) : Decidable (Legal (diamond extra) s t) :=
  inferInstanceAs (Decidable (s=t ∨ diamond extra s t))

theorem diamond_loopless (extra : Bool) : Loopless (diamond extra) := by
  have finite : ∀ extra, Loopless (diamond extra) := by
    unfold Loopless
    decide +kernel
  exact finite extra

theorem diamond_arrows (extra : Bool) :
    arcCount (diamond extra)=4+(if extra then 1 else 0) := by
  rw [arcCount_eq]
  cases extra <;> decide +kernel

theorem diamond_delivery (extra : Bool) : Guaranteed (diamond extra) 0 3 := by
  have witnesses : ∀ extra (c : Fin 4), c≠0 →
      ∃ z : Fin 4, diamond extra 0 z ∧ diamond extra z 3 ∧
        ¬Legal (diamond extra) c z := by decide +kernel
  intro c initial
  obtain ⟨z,first,last,safe⟩ := witnesses extra c initial
  exact ⟨2,DenseCounting.safe_intermediate_winning (Ne.symm initial) first last safe⟩

theorem diamond_score (extra : Bool) : score (diamond extra)=1 := by
  classical
  have upper := one_upper (diamond extra) (diamond_loopless extra)
    (diamond_arrows extra) (by cases extra <;> decide)
  have pair : Indirect (diamond extra) 0 3 :=
    ⟨by decide,by cases extra <;> decide,diamond_delivery extra⟩
  have member : (0,3) ∈ (allPairs 4).filter
      (fun p => decide (Indirect (diamond extra) p.1 p.2)) := by
    simp [allPairs,List.mem_flatMap,List.mem_map,pair]
  have positive := List.length_pos_of_mem member
  change 0<score (diamond extra) at positive
  omega

theorem maximum_zero {n m : Nat} (admissible : m≤n*(n-1)) (small : m≤3) :
    IsMaximum n m 0 := by
  refine ⟨fun E loops arrows => Nat.le_of_eq (zero_upper E loops arrows small),
    DenseZero.initialGraph n m,DenseZero.initialGraph_loopless n m,
    DenseZero.initialGraph_arcCount admissible,?_⟩
  exact zero_upper _ (DenseZero.initialGraph_loopless n m)
    (DenseZero.initialGraph_arcCount admissible) small

theorem maximum_one {n m : Nat} (order : 4≤n) (low : 4≤m) (high : m≤5) :
    IsMaximum n m 1 := by
  have cases : m=4 ∨ m=5 := by omega
  rcases cases with rfl | rfl
  · obtain ⟨E,loops,arrows,value⟩ := GraphPadding.pad_to_order
      (diamond false) (diamond_loopless false) order
    refine ⟨fun F hF budget => one_upper F hF budget (by decide),E,loops,?_,?_⟩
    · simpa [diamond_arrows] using arrows
    · exact value.trans (diamond_score false)
  · obtain ⟨E,loops,arrows,value⟩ := GraphPadding.pad_to_order
      (diamond true) (diamond_loopless true) order
    refine ⟨fun F hF budget => one_upper F hF budget (by decide),E,loops,?_,?_⟩
    · simpa [diamond_arrows] using arrows
    · exact value.trans (diamond_score true)

#print axioms maximum_zero
#print axioms maximum_one
end Delivery.SmallBudgetsToFive
