import DenseCombinatorics
import GraphRelabeling
import DenseCounting
import CyclicArithmetic

/-! An explicit two-type core for every even order at least ten.
We use line labels L'_i = L_(i-1) from the manuscript, so every shift is
forward: P_i misses L'_i,L'_(i+1), and L'_i misses P_(i+3),P_(i+5).
This is exactly the manuscript graph after the stated reindexing. -/
namespace Delivery.DenseTwoType
open FiniteGame Extremal DenseCombinatorics
open CyclicArithmetic

inductive Vertex (k : Nat) where
  | point : Fin k → Vertex k
  | line : Fin k → Vertex k
  deriving DecidableEq

def encode {k : Nat} : Vertex k → Fin (2*k)
  | .point i => ⟨i.val, by omega⟩
  | .line i => ⟨k+i.val, by omega⟩

def decode {k : Nat} (v : Fin (2*k)) : Vertex k :=
  if h : v.val < k then .point ⟨v.val,h⟩
  else .line ⟨v.val-k,by omega⟩

@[simp] theorem decode_encode {k : Nat} (v : Vertex k) : decode (encode v) = v := by
  cases v with
  | point i => simp [encode,decode,i.isLt]
  | line i =>
    have h : ¬ k + i.val < k := by omega
    simp [encode,decode,h]

@[simp] theorem encode_decode {k : Nat} (v : Fin (2*k)) : encode (decode v) = v := by
  unfold decode
  split
  · rfl
  · apply Fin.ext
    dsimp only [encode]
    omega

theorem encode_injective {k : Nat} {u v : Vertex k}
    (same : encode u = encode v) : u = v := by
  have equal := congrArg decode same
  simpa only [decode_encode] using equal

theorem card_two {n : Nat} (a b : Fin n) (different : a ≠ b) :
    card (fun t => t = a ∨ t = b) = 2 := by
  have perm := (List.perm_ext_iff_of_nodup (elems_nodup (fun t => t = a ∨ t = b))
    (show [a,b].Nodup by simp [different])).mpr (fun t => by simp)
  change (elems (fun t => t = a ∨ t = b)).length = 2
  exact perm.length_eq

def first {k : Nat} : Vertex k → Vertex k
  | .point i => .line i
  | .line i => .point (shift i 3)

def second {k : Nat} : Vertex k → Vertex k
  | .point i => .line (shift i 1)
  | .line i => .point (shift i 5)

def missing {k : Nat} (s t : Vertex k) : Prop := t = first s ∨ t = second s

def edge {k : Nat} : Graph (Vertex k) := DenseCounting.complement missing

instance {k : Nat} (s t : Vertex k) : Decidable (missing s t) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance {k : Nat} (s t : Vertex k) : Decidable (edge s t) :=
  inferInstanceAs (Decidable (s ≠ t ∧ ¬ missing s t))

theorem missing_loopless {k : Nat} (s : Vertex k) : ¬ missing s s := by
  cases s <;> simp [missing,first,second]

theorem neighbours_distinct {k : Nat} (hk : 5 ≤ k) (s : Vertex k) :
    first s ≠ second s := by
  cases s with
  | point i =>
    intro same
    have equal : i = shift i 1 := by simpa [first,second] using same
    exact shift_ne_self i (by omega) (by omega) equal.symm
  | line i =>
    intro same
    have equal : shift i 3 = shift i 5 := by simpa [first,second] using same
    exact shift_ne_of_lt_gap i (by omega) (by omega) equal

theorem unblocked {k : Nat} (hk : 5 ≤ k) (s t c : Vertex k)
    (pair : missing s t)
    (block0 : missing s (first c) ∨ missing (first c) t)
    (block1 : missing s (second c) ∨ missing (second c) t) : c = s := by
  cases s <;> cases c <;> cases t <;>
    simp [missing,first,second] at pair block0 block1
  · rename_i i j t
    exact congrArg Vertex.point (pair_subset_same j i (by omega) (by omega) block0 block1)
  · rename_i i j t
    simp only [shift_add] at block0 block1
    rcases block0 with h0 | h0 <;> rcases block1 with h1 | h1
    all_goals exact False.elim (shift_ne_of_lt_gap j (by omega) (by omega)
      (h0.symm.trans h1))
  · rename_i i j t
    simp only [shift_add] at block1
    rcases block0 with h0 | h0 <;> rcases block1 with h1 | h1
    · exact False.elim (shift_ne_of_lt_gap j (by omega) (by omega) (h0.symm.trans h1))
    · exact False.elim (shift_ne_of_lt_gap j (by omega) (by omega) (h0.symm.trans h1))
    · exact False.elim (shift_ne_of_lt_gap j (by omega) (by omega) (h1.symm.trans h0))
    · exact False.elim (shift_ne_of_lt_gap j (by omega) (by omega) (h0.symm.trans h1))
  · rename_i i j t
    have aligned : shift j 3 = shift i 3 := pair_subset_same (shift j 3) (shift i 3)
      (d := 2) (by omega) (by omega)
      (by simpa only [shift_add] using block0)
      (by simpa only [shift_add] using block1)
    exact congrArg Vertex.line (shift_injective aligned)

theorem safe_neighbor {k : Nat} (hk : 5 ≤ k) {s t c : Vertex k}
    (pair : missing s t) (initial : c ≠ s) :
    ∃ u, missing c u ∧ ¬ missing s u ∧ ¬ missing u t := by
  classical
  by_cases good0 : ¬ missing s (first c) ∧ ¬ missing (first c) t
  · exact ⟨first c, Or.inl rfl, good0⟩
  by_cases good1 : ¬ missing s (second c) ∧ ¬ missing (second c) t
  · exact ⟨second c, Or.inr rfl, good1⟩
  have block0 : missing s (first c) ∨ missing (first c) t := by
    by_cases h : missing s (first c)
    · exact Or.inl h
    · exact Or.inr (Classical.byContradiction (fun h' => good0 ⟨h,h'⟩))
  have block1 : missing s (second c) ∨ missing (second c) t := by
    by_cases h : missing s (second c)
    · exact Or.inl h
    · exact Or.inr (Classical.byContradiction (fun h' => good1 ⟨h,h'⟩))
  exact False.elim (initial (unblocked hk s t c pair block0 block1))

theorem two_move {k : Nat} (hk : 5 ≤ k) (s t : Vertex k) : Universal edge t 2 s := by
  classical
  intro c initial
  by_cases same : s = t
  · subst t
    exact Winning.delivered
  by_cases direct : edge s t
  · exact Winning.finish (Ne.symm initial) (Or.inr direct)
  have pair : missing s t := Classical.byContradiction (fun h => direct ⟨same,h⟩)
  obtain ⟨u, cu, su, ut⟩ := safe_neighbor hk pair initial
  have firstEdge : edge s u := ⟨fun eq => ut (eq ▸ pair), su⟩
  have lastEdge : edge u t := ⟨fun eq => su (eq ▸ pair), ut⟩
  exact DenseCounting.safe_intermediate_winning (Ne.symm initial) firstEdge lastEdge
    (DenseCounting.missing_arc_unreachable missing_loopless cu)

/-- The prescribed adjacency on the standard vertex set `Fin (2*k)`. -/
def graph (k : Nat) : Graph (Fin (2*k)) := fun s t => edge (decode s) (decode t)

instance (k : Nat) (s t : Fin (2*k)) : Decidable (graph k s t) :=
  inferInstanceAs (Decidable (edge (decode s) (decode t)))

def graphIso (k : Nat) : GraphRelabeling.Iso (@edge k) (graph k) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  edge_iff := fun s t => by simp [graph]

theorem graph_loopless (k : Nat) : Loopless (graph k) := by
  intro s edge
  exact edge.1 rfl

theorem graph_two_move {k : Nat} (hk : 5 ≤ k) (s t : Fin (2*k)) :
    Universal (graph k) t 2 s := by
  intro c initial
  have different : decode c ≠ decode s := by
    intro same
    exact initial (by simpa only [encode_decode] using congrArg encode same)
  have win := two_move hk (decode s) (decode t) (decode c) different
  have transported := (graphIso k).winning win
  simpa only [graphIso,encode_decode] using transported

theorem graph_missing_iff {k : Nat} (s t : Fin (2*k)) :
    s ≠ t ∧ ¬ graph k s t ↔
      t = encode (first (decode s)) ∨ t = encode (second (decode s)) := by
  classical
  have equivalence : s ≠ t ∧ ¬ graph k s t ↔ missing (decode s) (decode t) := by
    constructor
    · intro h
      apply Classical.byContradiction
      intro absent
      apply h.2
      refine ⟨?_,absent⟩
      intro same
      exact h.1 (by simpa only [encode_decode] using congrArg encode same)
    · intro h
      refine ⟨?_,fun edge => edge.2 h⟩
      intro same
      subst t
      exact missing_loopless _ h
  rw [equivalence]
  constructor
  · rintro (h | h)
    · exact Or.inl (by simpa only [encode_decode] using congrArg encode h)
    · exact Or.inr (by simpa only [encode_decode] using congrArg encode h)
  · rintro (h | h)
    · exact Or.inl (by simpa only [decode_encode] using congrArg decode h)
    · exact Or.inr (by simpa only [decode_encode] using congrArg decode h)

theorem graph_missingCount {k : Nat} (hk : 5 ≤ k) : missingCount (graph k) = 4*k := by
  classical
  have row (s : Fin (2*k)) :
      ((List.finRange (2*k)).filter fun t => decide (s ≠ t ∧ ¬ graph k s t)).length = 2 := by
    have same := filter_count_congr (List.finRange (2*k))
      (fun t => s ≠ t ∧ ¬ graph k s t)
      (fun t => t = encode (first (decode s)) ∨ t = encode (second (decode s)))
      (fun t => graph_missing_iff s t)
    rw [same, ← card_eq]
    exact card_two _ _ (fun eq => neighbours_distinct hk _ (encode_injective eq))
  rw [missingCount_eq]
  unfold allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,row]
  have constant (xs : List (Fin (2*k))) : (xs.map fun _ => 2).sum = xs.length * 2 := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  have total := constant (List.finRange (2*k))
  simp only [List.length_finRange] at total
  omega

theorem graph_arcCount {k : Nat} (hk : 5 ≤ k) :
    arcCount (graph k) = (2*k) * (2*k-3) := by
  have partition := arcCount_add_missingCount (graph k) (graph_loopless k)
  rw [graph_missingCount hk] at partition
  have identity : (2*k) * (2*k-1) = (2*k) * (2*k-3) + 4*k := by
    have subtract : 2*k-1 = (2*k-3)+2 := by omega
    rw [subtract,Nat.mul_add]
    omega
  omega

theorem graph_score {k : Nat} (hk : 5 ≤ k) : score (graph k) = 4*k := by
  rw [score_eq_missing (graph k) (fun s t _ _ =>
    universal_guaranteed (graph_two_move hk s t)), graph_missingCount hk]

/-- Exact dense boundary on every even order at least ten, including an
explicit graph and actual two-move delivery for every missing pair. -/
theorem maximum_even {k : Nat} (hk : 5 ≤ k) :
    IsMaximum (2*k) ((2*k)*(2*k-3)) (4*k) := by
  constructor
  · intro E loopless arrows
    have partition := arcCount_add_missingCount E loopless
    have bound := score_le_missing E
    have identity : (2*k) * (2*k-1) = (2*k) * (2*k-3) + 4*k := by
      have subtract : 2*k-1 = (2*k-3)+2 := by omega
      rw [subtract,Nat.mul_add]
      omega
    omega
  · exact ⟨graph k,graph_loopless k,graph_arcCount hk,graph_score hk⟩

#print axioms graph_two_move
#print axioms graph_missingCount
#print axioms maximum_even

end Delivery.DenseTwoType
