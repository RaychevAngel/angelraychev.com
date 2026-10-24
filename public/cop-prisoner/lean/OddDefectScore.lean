import RowPrefixCutLoss
import SparseAttainment

/-! Counting the odd attaining family once, independently of its geometry.
Only the final delivery premise is left for the concrete local strategies. -/
namespace Delivery.OddDefectScore
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

theorem score_identity {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (u v : Fin n) (different : u≠v)
    (outOne : outdegree E u=1) (inOne : indegree E v=1)
    (missing : ¬E u v)
    (delivery : ∀ s t, s≠u → t≠v → s≠t → ¬E s t → Guaranteed E s t) :
    score E + (n-2) + arcCount E = (n-1)*(n-1)+2 := by
  classical
  let A := fun s => s≠u
  let B := fun t => t≠v
  have a : card A=n-1 := by
    have split := card_complement (fun x => x=u)
    rw [card_singleton] at split
    change 1+card A=n at split
    omega
  have b : card B=n-1 := by
    have split := card_complement (fun x => x=v)
    rw [card_singleton] at split
    change 1+card B=n at split
    omega
  have diagonal : card (fun s => A s ∧ B s)=n-2 := by
    have split := card_partition A (fun s => s=v)
    have one : card (fun s => A s ∧ s=v)=1 := by
      rw [card_congr (Q:=fun s => s=v) (by
        intro s
        constructor
        · exact And.right
        · intro same; subst s; exact ⟨Ne.symm different,rfl⟩)]
      exact card_singleton v
    rw [one,a] at split
    change 1+card (fun s => A s ∧ B s)=n-1 at split
    omega
  have live (s t) (pair : Indirect E s t) : A s ∧ B t := by
    constructor
    · intro same
      have degree := live_outdegree loops pair
      rw [same,outOne] at degree
      omega
    · intro same
      have degree := live_indegree pair
      rw [same,inOne] at degree
      omega
  let D := fun s t => A s ∧ B t ∧ s=t
  let F := fun s t => E s t ∧ A s ∧ B t
  have first := arcs_union (E:=Indirect E) (F:=D)
    (fun _ _ pair diag => pair.1 diag.2.2)
  have second := arcs_union (E:=fun s t => Indirect E s t ∨ D s t) (F:=F) (by
    intro s t pair arrow
    rcases pair with pair | diag
    · exact pair.2.1 arrow.1
    · exact loops s (diag.2.2.symm ▸ arrow.1))
  have rectangle : arcCount (fun s t => (Indirect E s t ∨ D s t) ∨ F s t)=
      card A*card B := by
    rw [←rectangle_count]
    apply arcs_congr
    intro s t
    constructor
    · rintro ((pair|diag)|arrow)
      · exact live s t pair
      · exact ⟨diag.1,diag.2.1⟩
      · exact arrow.2
    · rintro ⟨hs,ht⟩
      by_cases equal : s=t
      · exact Or.inl (Or.inr ⟨hs,ht,equal⟩)
      · by_cases edge : E s t
        · exact Or.inr ⟨edge,hs,ht⟩
        · exact Or.inl (Or.inl ⟨equal,edge,delivery s t hs ht equal edge⟩)
  have diagCount : arcCount D=n-2 := (diagonal_count A B).trans diagonal
  have scoreCount : arcCount (Indirect E)=score E := rfl
  have cutCount : arcCount F=cut E A B := rfl
  rw [a,b] at rectangle
  have full : score E+(n-2)+cut E A B=(n-1)*(n-1) := by omega
  have corner : cut E (fun s => ¬A s) (fun t => ¬B t)=0 := by
    change arcCount _=0
    apply Nat.le_antisymm _ (Nat.zero_le _)
    have eqFalse : arcCount (fun s t => E s t ∧ ¬A s ∧ ¬B t)=
        arcCount (fun _ _ : Fin n => False) := by
      apply arcs_congr
      intro s t
      constructor
      · rintro ⟨edge,hs,ht⟩
        have sameS : s=u := Classical.not_not.mp hs
        have sameT : t=v := Classical.not_not.mp ht
        exact missing (sameS ▸ sameT ▸ edge)
      · exact False.elim
    rw [eqFalse,arcCount_eq]
    simp
  have sourceCount : cut E (fun s => ¬A s) (fun _ => True)=1 := by
    have eqSource : cut E (fun s => ¬A s) (fun _ => True)=cut E (fun s => s=u) (fun _ => True) :=
      arcs_congr (fun _ _ => by simp only [A,ne_eq,Classical.not_not])
    rw [eqSource,single_source_cut,outOne]
  have targetCount : cut E (fun _ => True) (fun t => ¬B t)=1 := by
    have eqTarget : cut E (fun _ => True) (fun t => ¬B t)=cut E (fun _ => True) (fun t => t=v) :=
      arcs_congr (fun _ _ => by simp only [B,ne_eq,Classical.not_not])
    rw [eqTarget,single_target_cut,inOne]
  have partition := RowPrefix.cut_complement_identity E A B
  rw [corner,sourceCount,targetCount] at partition
  omega

theorem score_exact {n : Nat} (large : 6≤n) (E : Graph (Fin n))
    (loops : Loopless E) (budget : arcCount E=2*n-1)
    (u v : Fin n) (different : u≠v)
    (outOne : outdegree E u=1) (inOne : indegree E v=1) (missing : ¬E u v)
    (delivery : ∀ s t, s≠u → t≠v → s≠t → ¬E s t → Guaranteed E s t) :
    score E=(n-1)*(n-4)+2 := by
  have count := score_identity E loops u v different outOne inOne missing delivery
  rw [budget] at count
  have polynomial : (n-1)*(n-1)=(n-1)*(n-4)+3*(n-1) := by
    calc
      (n-1)*(n-1) = (n-1)*(n-4+3) := congrArg (fun x => (n-1)*x) (by omega)
      _ = (n-1)*(n-4)+3*(n-1) := by rw [Nat.mul_add,Nat.mul_comm (n-1) 3]
  rw [polynomial] at count
  omega

/-- Once the concrete family supplies delivery, the unrestricted optimum and
every larger host follow without any additional finite certificate. -/
theorem maximum_of_delivery {n host : Nat} (large : 6≤n) (order : n≤host)
    (E : Graph (Fin n)) (loops : Loopless E) (budget : arcCount E=2*n-1)
    (u v : Fin n) (different : u≠v)
    (outOne : outdegree E u=1) (inOne : indegree E v=1) (missing : ¬E u v)
    (delivery : ∀ s t, s≠u → t≠v → s≠t → ¬E s t → Guaranteed E s t) :
    IsMaximum host (2*n-1) ((n-1)*(n-4)+2) := by
  constructor
  · intro F loopsF arrowsF
    have bound := SparseParity.odd_upper F loopsF (k:=n-1) (by omega) (by omega)
    simpa only [Nat.sub_sub] using bound
  · obtain ⟨F,loopsF,arrowsF,valueF⟩ := GraphPadding.pad_to_order E loops order
    exact ⟨F,loopsF,arrowsF.trans budget,valueF.trans
      (score_exact large E loops budget u v different outOne inOne missing delivery)⟩

#print axioms score_identity
#print axioms score_exact
#print axioms maximum_of_delivery
end Delivery.OddDefectScore
