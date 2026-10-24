import RowPrefixTree
import IrregularFiveSevenProfile

/-! Complete finite exclusion for the sole possible positive five-vertex,
seven-arrow profile above two guarantees. Every row choice, symmetry route
and optimistic losing region is checked; the producer supplies only data. -/
namespace Delivery.IrregularFiveSeven
open FiniteGame Extremal RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def D (s : Fin 5) : Nat := if s.val<2 then 2 else 1
def R (t : Fin 5) : Nat := if 2≤t.val ∧ t.val<4 then 2 else 1

def rows (a b c d e : Nat) : Rows 5 := fun v =>
  match v.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

def choices (d : Nat) : List Nat := if d=2 then [3,5,9,17,6,10,18,12,20,24] else [1,2,4,8,16]
theorem cover_one : RowCover 5 1 (choices 1) := by decide +kernel
theorem cover_two : RowCover 5 2 (choices 2) := by decide +kernel
theorem complete (s : Fin 5) : RowCover 5 (D s) (choices (D s)) := by
  unfold D
  split
  · exact cover_two
  · exact cover_one

def tree : Tree 5 := .branch [6,12,18,20] (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id)) (fun mask => match mask with | 6 => .branch [5,9,12,17,20,24] (fun mask => (mask,id)) (fun mask => match mask with | 5 => .bound { allowed := (rows 8 8 0 0 0), upper := (rows 7 7 28 24 24), lower := (rows 7 7 4 8 16), losses := [] } | 9 => .bound { allowed := (rows 8 4 0 0 0), upper := (rows 7 11 28 28 28), lower := (rows 7 11 4 8 16), losses := [] } | 12 => .bound { allowed := (rows 8 0 0 0 0), upper := (rows 7 14 29 25 25), lower := (rows 7 14 4 8 16), losses := [] } | 17 => .branch [8] (fun mask => (mask,id)) (fun mask => match mask with | 8 => .branch [4] (fun mask => (mask,id)) (fun mask => match mask with | 4 => .bound { allowed := (rows 8 8 0 0 0), upper := (rows 7 19 12 12 24), lower := (rows 7 19 12 12 16), losses := [{ target := 2, region := (rows 1 3 0 8 28), good := (rows 19 19 24 24 16) }] } | _ => .invalid) | _ => .invalid) | 20 => .bound { allowed := (rows 8 8 0 0 0), upper := (rows 7 22 13 9 25), lower := (rows 7 22 4 8 16), losses := [] } | 24 => .bound { allowed := (rows 8 4 0 0 0), upper := (rows 7 26 13 13 29), lower := (rows 7 26 4 8 16), losses := [] } | _ => .invalid) | 12 => .bound { allowed := (rows 0 12 0 0 0), upper := (rows 13 31 31 31 31), lower := (rows 13 2 4 8 16), losses := [] } | 18 => .branch [5,12] (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id)) (fun mask => match mask with | 5 => .branch [8] (fun mask => (mask,id)) (fun mask => match mask with | 8 => .branch [4] (fun mask => (mask,id)) (fun mask => match mask with | 4 => .bound { allowed := (rows 8 8 0 0 0), upper := (rows 19 7 12 12 24), lower := (rows 19 7 12 12 16), losses := [{ target := 2, region := (rows 3 2 0 8 28), good := (rows 19 19 24 24 16) }] } | _ => .invalid) | _ => .invalid) | 12 => .bound { allowed := (rows 12 0 0 0 0), upper := (rows 19 14 13 13 29), lower := (rows 19 14 4 8 16), losses := [] } | _ => .invalid) | 20 => .branch [5,9,12] (fun mask => (mask,id)) (fun mask => match mask with | 5 => .bound { allowed := (rows 8 8 0 0 0), upper := (rows 21 7 14 10 26), lower := (rows 21 7 4 8 16), losses := [] } | 9 => .bound { allowed := (rows 8 4 0 0 0), upper := (rows 21 11 14 14 30), lower := (rows 21 11 4 8 16), losses := [] } | 12 => .bound { allowed := (rows 8 0 0 0 0), upper := (rows 21 14 15 11 27), lower := (rows 21 14 4 8 16), losses := [] } | _ => .invalid) | _ => .invalid)

theorem checked : tree.check D R choices 2 []=true := by decide +kernel

theorem canonical_upper : Upper D R [] 2 := Tree.sound D R choices complete 2 [] tree checked

/-- The upper bound applies to every actual positive-degree five-vertex graph
with seven arrows, including graphs not already in the literal labels. -/
theorem positive_upper (E : Graph (Fin 5)) (loopless : Loopless E)
    (budget : arcCount E=7)
    (positiveOut : ∀ x, 1≤SparseSupport.outdegree E x)
    (positiveIn : ∀ x, 1≤SparseSupport.indegree E x) : score E≤2 := by
  by_cases small : score E≤2
  · exact small
  · obtain ⟨F,⟨iso⟩,loops,outDegrees,inDegrees⟩ :=
      IrregularFiveSevenProfile.normalize E loopless budget positiveOut positiveIn (by omega)
    have prescribed : Prescribed D R F := ⟨loops,outDegrees,inDegrees⟩
    have bound := canonical_upper F prescribed (by intro s h; simp at h)
    rw [GraphRelabeling.score_eq iso]
    exact bound

#print axioms canonical_upper
#print axioms positive_upper
end Delivery.IrregularFiveSeven
