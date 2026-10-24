import DenseEnvelope
import PrefixEnvelope

/-! Odd optional envelope, with the manuscript's subdivisions at P_0 and P_7.
The core's line numbering is L'_i=L_(i-1), so the hub misses L'_1,L'_8.
The optional targets have shifts +6,+4 and hub→P_2. -/
namespace Delivery.DenseOddEnvelope
open FiniteGame Extremal DenseCombinatorics CyclicArithmetic DenseOddCore

def first {k : Nat} (hk : 14 ≤ k) : Vertex k → Vertex k
  | .point i => .line i
  | .line i => .point (shift i 3)
  | .hub => .line ⟨1,by omega⟩

def second {k : Nat} (hk : 14 ≤ k) : Vertex k → Vertex k
  | .point i => if i.val = 0 ∨ i.val = 7 then .hub else .line (shift i 1)
  | .line i => .point (shift i 5)
  | .hub => .line ⟨8,by omega⟩

def third {k : Nat} (hk : 14 ≤ k) : Vertex k → Vertex k
  | .point i => .point (shift i 6)
  | .line i => .line (shift i 4)
  | .hub => .point ⟨2,by omega⟩

def base {k : Nat} (hk : 14 ≤ k) : Graph (Vertex k)
  | .point i, .line j => j = i ∨ (¬ (i.val = 0 ∨ i.val = 7) ∧ j = shift i 1)
  | .point i, .hub => i.val = 0 ∨ i.val = 7
  | .line i, .point j => j = shift i 3 ∨ j = shift i 5
  | .hub, .line j => j = ⟨1,by omega⟩ ∨ j = ⟨8,by omega⟩
  | _, _ => False

def full {k : Nat} (hk : 14 ≤ k) (s t : Vertex k) : Prop := base hk s t ∨ t = third hk s

def selected {k : Nat} (hk : 14 ≤ k) (take : Vertex k → Prop) (s t : Vertex k) : Prop :=
  base hk s t ∨ (take s ∧ t = third hk s)

def edge {k : Nat} (hk : 14 ≤ k) (take : Vertex k → Prop) : Graph (Vertex k) :=
  DenseCounting.complement (selected hk take)

theorem base_loopless {k : Nat} (hk : 14 ≤ k) (s : Vertex k) : ¬ base hk s s := by
  cases s <;> simp [base]

theorem full_loopless {k : Nat} (hk : 14 ≤ k) (s : Vertex k) : ¬ full hk s s := by
  rintro (h | h)
  · exact base_loopless hk s h
  · cases s with
    | point i => exact shift_ne_self (d := 6) i (by omega) (by omega) (by simpa [third] using h.symm)
    | line i => exact shift_ne_self (d := 4) i (by omega) (by omega) (by simpa [third] using h.symm)
    | hub => simp [third] at h

theorem base_rows {k : Nat} (hk : 14 ≤ k) (s t : Vertex k) :
    base hk s t ↔ t = first hk s ∨ t = second hk s := by
  cases s with
  | point i =>
    by_cases modified : i.val = 0 ∨ i.val = 7
    all_goals cases t <;> simp [base,first,second,modified]
  | line i => cases t <;> simp [base,first,second]
  | hub => cases t <;> simp [base,first,second]

set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
theorem unblocked {k : Nat} (hk : 14 ≤ k) (range : k = 14 ∨ 16 ≤ k)
    (s t c : Vertex k) (pair : full hk s t)
    (block0 : full hk s (first hk c) ∨ full hk (first hk c) t)
    (block1 : full hk s (second hk c) ∨ full hk (second hk c) t) : c = s := by
  have sh1 (i : Fin k) := shift_val_small i (d := 1) (by omega : 1 < k)
  have sh3 (i : Fin k) := shift_val_small i (d := 3) (by omega : 3 < k)
  have sh4 (i : Fin k) := shift_val_small i (d := 4) (by omega : 4 < k)
  have sh5 (i : Fin k) := shift_val_small i (d := 5) (by omega : 5 < k)
  have sh6 (i : Fin k) := shift_val_small i (d := 6) (by omega : 6 < k)
  have casesPair : t = first hk s ∨ t = second hk s ∨ t = third hk s := by
    rcases pair with b | extra
    · rcases (base_rows hk s t).mp b with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr extra)
  clear pair
  rcases casesPair with pair | pair | pair
  all_goals subst t
  all_goals cases s with
    | point i =>
      by_cases modified : i.val = 0 ∨ i.val = 7
      all_goals cases c with
        | point j =>
          by_cases modifiedCop : j.val = 0 ∨ j.val = 7
          all_goals simp_all [full,base,first,second,third,modified,modifiedCop,
            Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
        | line j =>
          simp_all [full,base,first,second,third,modified,Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
        | hub =>
          simp_all [full,base,first,second,third,modified,Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
    | line i =>
      cases c with
        | point j =>
          by_cases modifiedCop : j.val = 0 ∨ j.val = 7
          all_goals simp_all [full,base,first,second,third,modifiedCop,
            Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
        | line j =>
          simp_all [full,base,first,second,third,Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
        | hub =>
          simp_all [full,base,first,second,third,Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
    | hub =>
      cases c with
        | point j =>
          by_cases modifiedCop : j.val = 0 ∨ j.val = 7
          all_goals simp_all [full,base,first,second,third,modifiedCop,
            Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
        | line j =>
          simp_all [full,base,first,second,third,Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
          all_goals clear sh1 sh3 sh4 sh5 sh6
          all_goals repeat' (first | split at block0 | split at block1)
          all_goals omega
        | hub => rfl


theorem safe_neighbor {k : Nat} (hk : 14 ≤ k) (range : k = 14 ∨ 16 ≤ k)
    {s t c : Vertex k} (pair : full hk s t) (initial : c ≠ s) :
    ∃ u, base hk c u ∧ ¬ full hk s u ∧ ¬ full hk u t := by
  classical
  by_cases good0 : ¬ full hk s (first hk c) ∧ ¬ full hk (first hk c) t
  · exact ⟨first hk c,(base_rows hk _ _).mpr (Or.inl rfl),good0⟩
  by_cases good1 : ¬ full hk s (second hk c) ∧ ¬ full hk (second hk c) t
  · exact ⟨second hk c,(base_rows hk _ _).mpr (Or.inr rfl),good1⟩
  have block0 : full hk s (first hk c) ∨ full hk (first hk c) t := by grind
  have block1 : full hk s (second hk c) ∨ full hk (second hk c) t := by grind
  exact False.elim (initial (unblocked hk range s t c pair block0 block1))

theorem witnesses {k : Nat} (hk : 14 ≤ k) (range : k = 14 ∨ 16 ≤ k) :
    RobustTwoMove.Witnesses (DenseCounting.complement (full hk))
      (DenseCounting.complement (base hk)) := by
  classical
  intro s t c different initial absent
  have pair : full hk s t := Classical.byContradiction (fun h => absent ⟨different,h⟩)
  obtain ⟨u,cu,su,ut⟩ := safe_neighbor hk range pair initial
  refine ⟨u,⟨fun eq => ut (eq ▸ pair),su⟩,⟨fun eq => su (eq ▸ pair),ut⟩,?_,?_⟩
  · intro same; subst u; exact base_loopless hk c cu
  · intro present; exact present.2 cu

/-- Every optional row subset satisfies the same two-move strategy. -/
theorem two_move {k : Nat} (hk : 14 ≤ k) (range : k = 14 ∨ 16 ≤ k)
    (take : Vertex k → Prop) (s t : Vertex k) : Universal (edge hk take) t 2 s := by
  apply RobustTwoMove.envelope_universal (B := DenseCounting.complement (full hk))
    (E := DenseCounting.complement (base hk)) ?_ ?_ (witnesses hk range) s t
  · intro x y h
    refine ⟨h.1,?_⟩
    rintro (b | ⟨_,extra⟩)
    · exact h.2 (Or.inl b)
    · exact h.2 (Or.inr extra)
  · intro x y h
    exact ⟨h.1,fun b => h.2 (Or.inl b)⟩

theorem neighbours_distinct {k : Nat} (hk : 14 ≤ k) (s : Vertex k) :
    first hk s ≠ second hk s := by
  cases s with
  | point i =>
    simp only [first,second]
    split
    · simp
    · intro same
      exact shift_ne_self (d := 1) i (by omega) (by omega) (by simpa using same.symm)
  | line i =>
    intro same
    exact shift_ne_of_lt_gap i (a := 3) (b := 5) (by omega) (by omega)
      (by simpa [first,second] using same)
  | hub => simp [first,second,Fin.ext_iff]

theorem third_distinct {k : Nat} (hk : 14 ≤ k) (s : Vertex k) :
    first hk s ≠ third hk s ∧ second hk s ≠ third hk s := by
  cases s with
  | point i => by_cases modified : i.val = 0 ∨ i.val = 7 <;> simp [first,second,third,modified]
  | line i => simp [first,second,third]
  | hub => simp [first,second,third]

/-- Delivery graph with all optional missing arcs. -/
def lowerGraph (k : Nat) (hk : 14 ≤ k) : Graph (Fin (2*k+1)) :=
  fun s t => DenseCounting.complement (full hk) (decode s) (decode t)

/-- Delivery graph with only the compulsory missing arcs. -/
def upperGraph (k : Nat) (hk : 14 ≤ k) : Graph (Fin (2*k+1)) :=
  fun s t => DenseCounting.complement (base hk) (decode s) (decode t)

theorem subset {k : Nat} (hk : 14 ≤ k) :
    RobustTwoMove.Subgraph (lowerGraph k hk) (upperGraph k hk) :=
  fun _ _ h => ⟨h.1,fun b => h.2 (Or.inl b)⟩

theorem upper_loopless {k : Nat} (hk : 14 ≤ k) : Loopless (upperGraph k hk) :=
  fun _ h => h.1 rfl

theorem lower_loopless {k : Nat} (hk : 14 ≤ k) : Loopless (lowerGraph k hk) :=
  fun _ h => h.1 rfl

theorem graph_witnesses {k : Nat} (hk : 14 ≤ k) (range : k = 14 ∨ 16 ≤ k) :
    RobustTwoMove.Witnesses (lowerGraph k hk) (upperGraph k hk) := by
  intro s t c different initial absent
  have distinct : decode s ≠ decode t := fun same =>
    different (by simpa only [encode_decode] using congrArg encode same)
  have start : decode c ≠ decode s := fun same =>
    initial (by simpa only [encode_decode] using congrArg encode same)
  obtain ⟨u,su,ut,uc,cu⟩ := witnesses hk range (decode s) (decode t) (decode c)
    distinct start absent
  refine ⟨encode u,?_,?_,?_,?_⟩
  · simpa only [lowerGraph,decode_encode] using su
  · simpa only [lowerGraph,decode_encode] using ut
  · intro same
    exact uc (by simpa only [decode_encode] using congrArg decode same)
  · simpa only [upperGraph,decode_encode] using cu

theorem decode_eq_iff {k : Nat} (s : Fin (2*k+1)) (t : Vertex k) :
    decode s = t ↔ s = encode t := by
  constructor
  · intro h; simpa only [encode_decode] using congrArg encode h
  · intro h; subst s; exact decode_encode t

theorem lifted_missing_iff {k : Nat} (M : Graph (Vertex k))
    (noLoops : ∀ s, ¬ M s s) (s t : Fin (2*k+1)) :
    (s ≠ t ∧ ¬ DenseCounting.complement M (decode s) (decode t)) ↔ M (decode s) (decode t) := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro absent
    exact h.2 ⟨fun same => h.1 (by simpa only [encode_decode] using congrArg encode same),absent⟩
  · intro h
    exact ⟨fun same => noLoops _ (same ▸ h),fun edge => edge.2 h⟩

theorem upper_missingCount {k : Nat} (hk : 14 ≤ k) :
    missingCount (upperGraph k hk) = 2*(2*k+1) := by
  classical
  have row (s : Fin (2*k+1)) : card (fun t => s ≠ t ∧ ¬ upperGraph k hk s t) = 2 := by
    change card (fun t => s ≠ t ∧ ¬ DenseCounting.complement (base hk) (decode s) (decode t)) = 2
    rw [card_congr (lifted_missing_iff (base hk) (base_loopless hk) s)]
    rw [card_congr (fun t => base_rows hk (decode s) (decode t))]
    rw [card_congr (Q := fun t => t = encode (first hk (decode s)) ∨ t = encode (second hk (decode s)))
      (fun t => by simp only [decode_eq_iff])]
    exact DenseTwoType.card_two _ _ (fun eq => neighbours_distinct hk _ (encode_injective eq))
  rw [ConstructionCounts.missing_rows]
  simp only [row]
  have constant (xs : List (Fin (2*k+1))) : (xs.map fun _ => 2).sum = xs.length * 2 := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  simpa only [List.length_finRange,Nat.mul_comm] using constant (List.finRange (2*k+1))

theorem lower_missingCount {k : Nat} (hk : 14 ≤ k) :
    missingCount (lowerGraph k hk) = 3*(2*k+1) := by
  classical
  have singleton (a : Fin (2*k+1)) : card (fun t => t = a) = 1 := by
    rw [card_eq]
    simp [List.filter_eq,(List.nodup_finRange (2*k+1)).count]
  have row (s : Fin (2*k+1)) : card (fun t => s ≠ t ∧ ¬ lowerGraph k hk s t) = 3 := by
    change card (fun t => s ≠ t ∧ ¬ DenseCounting.complement (full hk) (decode s) (decode t)) = 3
    rw [card_congr (lifted_missing_iff (full hk) (full_loopless hk) s)]
    have shape (t : Fin (2*k+1)) : full hk (decode s) (decode t) ↔
        (t = encode (first hk (decode s)) ∨ t = encode (second hk (decode s))) ∨
        t = encode (third hk (decode s)) := by
      simp only [full,base_rows,decode_eq_iff]
    rw [card_congr shape,card_disjoint_union]
    · rw [DenseTwoType.card_two _ _ (fun eq => neighbours_distinct hk _ (encode_injective eq)),singleton]
    · intro t pair extra
      rcases pair with pair | pair
      · exact (third_distinct hk (decode s)).1 (encode_injective (pair.symm.trans extra))
      · exact (third_distinct hk (decode s)).2 (encode_injective (pair.symm.trans extra))
  rw [ConstructionCounts.missing_rows]
  simp only [row]
  have constant (xs : List (Fin (2*k+1))) : (xs.map fun _ => 3).sum = xs.length * 3 := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  simpa only [List.length_finRange,Nat.mul_comm] using constant (List.finRange (2*k+1))

/-- Exact attainment at order 29 and every odd order at least 33. The
attaining graph is PrefixEnvelope.graph with the two literal graphs above. -/
theorem maximum {k h : Nat} (hk : 14 ≤ k) (range : k = 14 ∨ 16 ≤ k)
    (low : 2*(2*k+1) ≤ h) (high : h ≤ 3*(2*k+1)) :
    IsMaximum (2*k+1) ((2*k+1)*(2*k)-h) h := by
  have lowerCount := arcCount_add_missingCount (lowerGraph k hk) (lower_loopless hk)
  have upperCount := arcCount_add_missingCount (upperGraph k hk) (upper_loopless hk)
  rw [lower_missingCount hk] at lowerCount
  rw [upper_missingCount hk] at upperCount
  simp only [Nat.add_sub_cancel] at lowerCount upperCount
  have capacity : h ≤ (2*k+1)*(2*k) := by
    have mul := Nat.mul_le_mul_left (2*k+1) (show 3 ≤ 2*k by omega)
    omega
  have result := PrefixEnvelope.maximum_at (lowerGraph k hk) (upperGraph k hk)
    (subset hk) (upper_loopless hk) (graph_witnesses hk range)
    (m := (2*k+1)*(2*k)-h) (by omega) (by omega)
  have subtract : (2*k+1)*(2*k+1-1)-((2*k+1)*(2*k)-h) = h := by
    rw [Nat.add_sub_cancel]
    omega
  simpa only [subtract] using result

#print axioms graph_witnesses
#print axioms lower_missingCount
#print axioms maximum

end Delivery.DenseOddEnvelope
