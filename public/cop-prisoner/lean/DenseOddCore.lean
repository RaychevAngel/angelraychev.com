import DenseTwoType

/-! Odd-order two-type core. In the line labels L'_i = L_(i-1), subdivide
P_0 → L'_1 and P_3 → L'_4 through a new hub. This is the manuscript's
odd construction, with its exact local two-move and counting proofs. -/
namespace Delivery.DenseOddCore
open FiniteGame Extremal DenseCombinatorics CyclicArithmetic

inductive Vertex (k : Nat) where
  | point : Fin k → Vertex k
  | line : Fin k → Vertex k
  | hub : Vertex k
  deriving DecidableEq

def first {k : Nat} (hk : 6 ≤ k) : Vertex k → Vertex k
  | .point i => .line i
  | .line i => .point (shift i 3)
  | .hub => .line ⟨1,by omega⟩

def second {k : Nat} (hk : 6 ≤ k) : Vertex k → Vertex k
  | .point i => if i.val = 0 ∨ i.val = 3 then .hub else .line (shift i 1)
  | .line i => .point (shift i 5)
  | .hub => .line ⟨4,by omega⟩

def missing {k : Nat} (hk : 6 ≤ k) : Graph (Vertex k)
  | .point i, .line j => j = i ∨ (¬ (i.val = 0 ∨ i.val = 3) ∧ j = shift i 1)
  | .point i, .hub => i.val = 0 ∨ i.val = 3
  | .line i, .point j => j = shift i 3 ∨ j = shift i 5
  | .hub, .line j => j = ⟨1,by omega⟩ ∨ j = ⟨4,by omega⟩
  | _, _ => False

def edge {k : Nat} (hk : 6 ≤ k) : Graph (Vertex k) :=
  DenseCounting.complement (missing hk)

instance {k : Nat} (hk : 6 ≤ k) (s t : Vertex k) : Decidable (missing hk s t) :=
  by cases s <;> cases t <;> unfold missing <;> infer_instance

instance {k : Nat} (hk : 6 ≤ k) (s t : Vertex k) : Decidable (edge hk s t) :=
  inferInstanceAs (Decidable (s ≠ t ∧ ¬ missing hk s t))

theorem shift_val_small {k d : Nat} (i : Fin k) (small : d < k) :
    (shift i d).val = if i.val + d < k then i.val + d else i.val + d - k := by
  simp only [shift, Nat.add_mod_eq_sub, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt small]
  split <;> simp

theorem missing_loopless {k : Nat} (hk : 6 ≤ k) (s : Vertex k) :
    ¬ missing hk s s := by
  cases s <;> simp [missing]

theorem neighbours_distinct {k : Nat} (hk : 6 ≤ k) (s : Vertex k) :
    first hk s ≠ second hk s := by
  cases s with
  | point i =>
    simp only [first,second]
    split
    · simp
    · intro same
      have equal : i = shift i 1 := by simpa using same
      exact shift_ne_self i (by omega) (by omega) equal.symm
  | line i =>
    intro same
    have equal : shift i 3 = shift i 5 := by simpa [first,second] using same
    exact shift_ne_of_lt_gap i (by omega) (by omega) equal
  | hub => simp [first,second,Fin.ext_iff]

theorem missing_iff {k : Nat} (hk : 6 ≤ k) (s t : Vertex k) :
    missing hk s t ↔ t = first hk s ∨ t = second hk s := by
  cases s with
  | point i =>
    by_cases modified : i.val = 0 ∨ i.val = 3
    all_goals cases t <;> simp [missing,first,second,modified]
  | line i => cases t <;> simp [missing,first,second]
  | hub => cases t <;> simp [missing,first,second]

set_option maxHeartbeats 1500000 in
set_option linter.unusedSimpArgs false in
theorem unblocked {k : Nat} (hk : 6 ≤ k) (s t c : Vertex k)
    (pair : missing hk s t)
    (block0 : missing hk s (first hk c) ∨ missing hk (first hk c) t)
    (block1 : missing hk s (second hk c) ∨ missing hk (second hk c) t) : c = s := by
  have sh1 (i : Fin k) := shift_val_small i (d := 1) (by omega : 1 < k)
  have sh3 (i : Fin k) := shift_val_small i (d := 3) (by omega : 3 < k)
  have sh5 (i : Fin k) := shift_val_small i (d := 5) (by omega : 5 < k)
  cases c with
  | point j =>
    by_cases modified : j.val = 0 ∨ j.val = 3
    all_goals cases s <;> cases t <;>
      simp_all [missing,first,second,Fin.ext_iff,sh1,sh3,sh5]
    all_goals try clear sh1 sh3 sh5
    all_goals repeat' (first | split at pair | split at block0 | split at block1)
    all_goals try simp_all
    all_goals omega
  | line j =>
    cases s <;> cases t <;>
      simp_all [missing,first,second,Fin.ext_iff,sh1,sh3,sh5]
    all_goals try clear sh1 sh3 sh5
    all_goals repeat' (first | split at pair | split at block0 | split at block1)
    all_goals try simp_all
    all_goals omega
  | hub =>
    cases s <;> cases t <;>
      simp_all [missing,first,second,Fin.ext_iff,sh1,sh3,sh5]
    all_goals try clear sh1 sh3 sh5
    all_goals repeat' (first | split at pair | split at block0 | split at block1)
    all_goals try simp_all
    all_goals omega

theorem safe_neighbor {k : Nat} (hk : 6 ≤ k) {s t c : Vertex k}
    (pair : missing hk s t) (initial : c ≠ s) :
    ∃ u, missing hk c u ∧ ¬ missing hk s u ∧ ¬ missing hk u t := by
  classical
  by_cases good0 : ¬ missing hk s (first hk c) ∧ ¬ missing hk (first hk c) t
  · exact ⟨first hk c, (missing_iff hk _ _).mpr (Or.inl rfl), good0⟩
  by_cases good1 : ¬ missing hk s (second hk c) ∧ ¬ missing hk (second hk c) t
  · exact ⟨second hk c, (missing_iff hk _ _).mpr (Or.inr rfl), good1⟩
  have block0 : missing hk s (first hk c) ∨ missing hk (first hk c) t := by
    by_cases h : missing hk s (first hk c)
    · exact Or.inl h
    · exact Or.inr (Classical.byContradiction (fun h' => good0 ⟨h,h'⟩))
  have block1 : missing hk s (second hk c) ∨ missing hk (second hk c) t := by
    by_cases h : missing hk s (second hk c)
    · exact Or.inl h
    · exact Or.inr (Classical.byContradiction (fun h' => good1 ⟨h,h'⟩))
  exact False.elim (initial (unblocked hk s t c pair block0 block1))

theorem two_move {k : Nat} (hk : 6 ≤ k) (s t : Vertex k) :
    Universal (edge hk) t 2 s := by
  classical
  intro c initial
  by_cases same : s = t
  · subst t
    exact Winning.delivered
  by_cases direct : edge hk s t
  · exact Winning.finish (Ne.symm initial) (Or.inr direct)
  have pair : missing hk s t := Classical.byContradiction (fun h => direct ⟨same,h⟩)
  obtain ⟨u, cu, su, ut⟩ := safe_neighbor hk pair initial
  have firstEdge : edge hk s u := ⟨fun eq => ut (eq ▸ pair), su⟩
  have lastEdge : edge hk u t := ⟨fun eq => su (eq ▸ pair), ut⟩
  exact DenseCounting.safe_intermediate_winning (Ne.symm initial) firstEdge lastEdge
    (DenseCounting.missing_arc_unreachable (missing_loopless hk) cu)

def encode {k : Nat} : Vertex k → Fin (2*k+1)
  | .point i => ⟨i.val,by omega⟩
  | .line i => ⟨k+i.val,by omega⟩
  | .hub => ⟨2*k,by omega⟩

def decode {k : Nat} (v : Fin (2*k+1)) : Vertex k :=
  if h : v.val < k then .point ⟨v.val,h⟩
  else if h' : v.val < 2*k then .line ⟨v.val-k,by omega⟩
  else .hub

@[simp] theorem decode_encode {k : Nat} (v : Vertex k) : decode (encode v) = v := by
  cases v with
  | point i => simp [encode,decode,i.isLt]
  | line i =>
    have h : ¬ k+i.val < k := by omega
    have h' : k+i.val < 2*k := by omega
    simp [encode,decode,h,h']
  | hub =>
    have h : ¬ 2*k < k := by omega
    simp [encode,decode,h]

@[simp] theorem encode_decode {k : Nat} (v : Fin (2*k+1)) : encode (decode v) = v := by
  unfold decode
  split
  · rfl
  · split
    · apply Fin.ext
      dsimp only [encode]
      omega
    · apply Fin.ext
      dsimp only [encode]
      omega

theorem encode_injective {k : Nat} {u v : Vertex k}
    (same : encode u = encode v) : u = v := by
  have equal := congrArg decode same
  simpa only [decode_encode] using equal

/-- The explicit odd-order adjacency on the standard finite vertex set. -/
def graph (k : Nat) (hk : 6 ≤ k) : Graph (Fin (2*k+1)) :=
  fun s t => edge hk (decode s) (decode t)

instance (k : Nat) (hk : 6 ≤ k) (s t : Fin (2*k+1)) : Decidable (graph k hk s t) :=
  inferInstanceAs (Decidable (edge hk (decode s) (decode t)))

def graphIso (k : Nat) (hk : 6 ≤ k) : GraphRelabeling.Iso (edge hk) (graph k hk) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  edge_iff := fun s t => by simp [graph]

theorem graph_loopless (k : Nat) (hk : 6 ≤ k) : Loopless (graph k hk) := by
  intro s edge
  exact edge.1 rfl

theorem graph_two_move {k : Nat} (hk : 6 ≤ k) (s t : Fin (2*k+1)) :
    Universal (graph k hk) t 2 s := by
  intro c initial
  have different : decode c ≠ decode s := by
    intro same
    exact initial (by simpa only [encode_decode] using congrArg encode same)
  have win := two_move hk (decode s) (decode t) (decode c) different
  have transported := (graphIso k hk).winning win
  simpa only [graphIso,encode_decode] using transported

theorem graph_missing_iff {k : Nat} (hk : 6 ≤ k) (s t : Fin (2*k+1)) :
    s ≠ t ∧ ¬ graph k hk s t ↔
      t = encode (first hk (decode s)) ∨ t = encode (second hk (decode s)) := by
  classical
  have equivalence : s ≠ t ∧ ¬ graph k hk s t ↔ missing hk (decode s) (decode t) := by
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
      exact missing_loopless hk _ h
  rw [equivalence,missing_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (by simpa only [encode_decode] using congrArg encode h)
    · exact Or.inr (by simpa only [encode_decode] using congrArg encode h)
  · rintro (h | h)
    · exact Or.inl (by simpa only [decode_encode] using congrArg decode h)
    · exact Or.inr (by simpa only [decode_encode] using congrArg decode h)

theorem graph_missingCount {k : Nat} (hk : 6 ≤ k) : missingCount (graph k hk) = 4*k+2 := by
  classical
  have row (s : Fin (2*k+1)) :
      ((List.finRange (2*k+1)).filter fun t => decide (s ≠ t ∧ ¬ graph k hk s t)).length = 2 := by
    have same := filter_count_congr (List.finRange (2*k+1))
      (fun t => s ≠ t ∧ ¬ graph k hk s t)
      (fun t => t = encode (first hk (decode s)) ∨ t = encode (second hk (decode s)))
      (fun t => graph_missing_iff hk s t)
    rw [same, ← card_eq]
    exact DenseTwoType.card_two _ _ (fun eq => neighbours_distinct hk _ (encode_injective eq))
  rw [missingCount_eq]
  unfold allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,row]
  have constant (xs : List (Fin (2*k+1))) : (xs.map fun _ => 2).sum = xs.length * 2 := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  have total := constant (List.finRange (2*k+1))
  simp only [List.length_finRange] at total
  omega

theorem graph_arcCount {k : Nat} (hk : 6 ≤ k) :
    arcCount (graph k hk) = (2*k+1) * (2*k-2) := by
  have partition := arcCount_add_missingCount (graph k hk) (graph_loopless k hk)
  rw [graph_missingCount hk] at partition
  have identity : (2*k+1) * (2*k+1-1) = (2*k+1) * (2*k-2) + (4*k+2) := by
    have subtract : 2*k+1-1 = (2*k-2)+2 := by omega
    rw [subtract,Nat.mul_add]
    omega
  omega

theorem graph_score {k : Nat} (hk : 6 ≤ k) : score (graph k hk) = 4*k+2 := by
  rw [score_eq_missing (graph k hk) (fun s t _ _ =>
    universal_guaranteed (graph_two_move hk s t)),graph_missingCount hk]

/-- Exact dense boundary on every odd order at least thirteen. -/
theorem maximum_odd {k : Nat} (hk : 6 ≤ k) :
    IsMaximum (2*k+1) ((2*k+1)*(2*k-2)) (4*k+2) := by
  constructor
  · intro E loopless arrows
    have partition := arcCount_add_missingCount E loopless
    have bound := score_le_missing E
    have identity : (2*k+1) * (2*k+1-1) = (2*k+1) * (2*k-2) + (4*k+2) := by
      have subtract : 2*k+1-1 = (2*k-2)+2 := by omega
      rw [subtract,Nat.mul_add]
      omega
    omega
  · exact ⟨graph k hk,graph_loopless k hk,graph_arcCount hk,graph_score hk⟩

#print axioms graph_two_move
#print axioms graph_missingCount
#print axioms maximum_odd
end Delivery.DenseOddCore
