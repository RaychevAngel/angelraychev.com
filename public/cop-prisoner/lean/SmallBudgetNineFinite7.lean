import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
7 vertices with 9 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetNineFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f g : Nat) : Rows 7 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32,64]
  | 2 => [3,5,9,17,33,65,6,10,18,34,66,12,20,36,68,24,40,72,48,80,96]
  | 3 => [7,11,19,35,67,13,21,37,69,25,41,73,49,81,97,14,22,38,70,26,42,74,50,82,98,28,44,76,52,84,100,56,88,104,112]
  | 4 => [15,23,39,71,27,43,75,51,83,99,29,45,77,53,85,101,57,89,105,113,30,46,78,54,86,102,58,90,106,114,60,92,108,116,120]
  | 5 => [31,47,79,55,87,103,59,91,107,115,61,93,109,117,121,62,94,110,118,122,124]
  | 6 => [63,95,111,119,123,125,126]
  | 7 => [127]
  | _ => []

theorem cover (d : Fin 8) : RowCover 7 d.val (choices d.val) := by
  revert d
  decide +kernel

def catalogue : List (List Nat) := []

theorem catalogue_eq : hardProfiles 7 9 5 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 7 9 5 false) :
    Upper (n:=7) (D xs.reverse) (R xs.reverse) [] 5 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
theorem profile_upper (xs : List Nat) (member : xs∈profiles 7 false 7 0 9 9) :
    Upper (n:=7) (D xs.reverse) (R xs.reverse) [] 5 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 7)) (loops : Loopless E) (budget : arcCount E=9)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (false=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤5 := by
  have od (x) : SparseSupport.outdegree E x<7 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<7 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 7).map (SparseSupport.outdegree E)).sum=9 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 7).map (SparseSupport.indegree E)).sum=9 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetNineFinite7
