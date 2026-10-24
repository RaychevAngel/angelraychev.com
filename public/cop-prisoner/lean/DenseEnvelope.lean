import DenseOddCore
import RobustTwoMove
import ConstructionCounts

/-! Even two-type envelope. The line numbering L'_i=L_(i-1) is inherited
from DenseTwoType; the optional same-type shifts remain +6 and +4.
Every optional subset has a two-move strategy. A literal prefix supplies
all missing-arc budgets between 2n and 3n. -/
namespace Delivery.DenseEnvelope
open FiniteGame Extremal DenseCombinatorics CyclicArithmetic DenseTwoType

def third {k : Nat} : Vertex k → Vertex k
  | .point i => .point (shift i 6)
  | .line i => .line (shift i 4)

def full {k : Nat} (s t : Vertex k) : Prop := missing s t ∨ t = third s

def selected {k : Nat} (take : Vertex k → Prop) (s t : Vertex k) : Prop :=
  missing s t ∨ (take s ∧ t = third s)

def edge {k : Nat} (take : Vertex k → Prop) : Graph (Vertex k) :=
  DenseCounting.complement (selected take)

theorem full_loopless {k : Nat} (hk : 11 ≤ k) (s : Vertex k) : ¬ full s s := by
  intro h
  rcases h with base | extra
  · exact missing_loopless s base
  · cases s with
    | point i => exact shift_ne_self (d := 6) i (by omega) (by omega) (by simpa [third] using extra.symm)
    | line i => exact shift_ne_self (d := 4) i (by omega) (by omega) (by simpa [third] using extra.symm)

set_option maxHeartbeats 3000000 in
set_option linter.unusedSimpArgs false in
theorem unblocked {k : Nat} (hk : 11 ≤ k) (s t c : Vertex k)
    (pair : full s t)
    (block0 : full s (first c) ∨ full (first c) t)
    (block1 : full s (second c) ∨ full (second c) t) : c = s := by
  have sh1 (i : Fin k) := DenseOddCore.shift_val_small i (d := 1) (by omega : 1 < k)
  have sh3 (i : Fin k) := DenseOddCore.shift_val_small i (d := 3) (by omega : 3 < k)
  have sh4 (i : Fin k) := DenseOddCore.shift_val_small i (d := 4) (by omega : 4 < k)
  have sh5 (i : Fin k) := DenseOddCore.shift_val_small i (d := 5) (by omega : 5 < k)
  have sh6 (i : Fin k) := DenseOddCore.shift_val_small i (d := 6) (by omega : 6 < k)
  rcases pair with (pair | pair) | pair
  all_goals subst t
  all_goals cases s <;> cases c <;>
    simp_all [full,missing,first,second,third,Fin.ext_iff,sh1,sh3,sh4,sh5,sh6]
  all_goals clear sh1 sh3 sh4 sh5 sh6
  all_goals repeat' (first | split at block0 | split at block1)
  all_goals try simp_all
  all_goals omega

theorem safe_neighbor {k : Nat} (hk : 11 ≤ k) {s t c : Vertex k}
    (pair : full s t) (initial : c ≠ s) :
    ∃ u, missing c u ∧ ¬ full s u ∧ ¬ full u t := by
  classical
  by_cases good0 : ¬ full s (first c) ∧ ¬ full (first c) t
  · exact ⟨first c,Or.inl rfl,good0⟩
  by_cases good1 : ¬ full s (second c) ∧ ¬ full (second c) t
  · exact ⟨second c,Or.inr rfl,good1⟩
  have block0 : full s (first c) ∨ full (first c) t := by grind
  have block1 : full s (second c) ∨ full (second c) t := by grind
  exact False.elim (initial (unblocked hk s t c pair block0 block1))

/-- Full missing envelope versus compulsory missing rows: all witnesses are
literal compulsory neighbors, safe even against every optional choice. -/
theorem witnesses {k : Nat} (hk : 11 ≤ k) :
    RobustTwoMove.Witnesses (DenseCounting.complement (@full k)) DenseTwoType.edge := by
  classical
  intro s t c different initial absent
  have pair : full s t := Classical.byContradiction (fun h => absent ⟨different,h⟩)
  obtain ⟨u,cu,su,ut⟩ := safe_neighbor hk pair initial
  refine ⟨u,⟨fun eq => ut (eq ▸ pair),su⟩,⟨fun eq => su (eq ▸ pair),ut⟩,?_,?_⟩
  · intro same; subst u; exact missing_loopless c cu
  · intro present; exact present.2 cu

/-- Arbitrary subsets, not only prefixes, retain the two-move bound. -/
theorem two_move {k : Nat} (hk : 11 ≤ k) (take : Vertex k → Prop) (s t : Vertex k) :
    Universal (edge take) t 2 s := by
  apply RobustTwoMove.envelope_universal (B := DenseCounting.complement (@full k))
    (E := DenseTwoType.edge) ?_ ?_ (witnesses hk) s t
  · intro x y h
    refine ⟨h.1,?_⟩
    rintro (base | ⟨_,extra⟩)
    · exact h.2 (Or.inl base)
    · exact h.2 (Or.inr extra)
  · intro x y h
    exact ⟨h.1,fun base => h.2 (Or.inl base)⟩


/-- Standard finite labels; a predicate chooses which optional rows to add. -/
def graph (k : Nat) (take : Fin (2*k) → Prop) : Graph (Fin (2*k)) :=
  fun s t => edge (fun v => take (encode v)) (decode s) (decode t)

instance {k : Nat} (take : Fin (2*k) → Prop) [DecidablePred take]
    (s t : Fin (2*k)) : Decidable (graph k take s t) := by
  unfold graph edge DenseCounting.complement selected
  cases decode s <;> cases decode t <;> unfold missing first second third <;> infer_instance

def graphIso (k : Nat) (take : Fin (2*k) → Prop) :
    GraphRelabeling.Iso (edge (fun v => take (encode v))) (graph k take) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  edge_iff := fun s t => by simp [graph]

theorem graph_loopless (k : Nat) (take : Fin (2*k) → Prop) : Loopless (graph k take) :=
  fun _ edge => edge.1 rfl

theorem graph_two_move {k : Nat} (hk : 11 ≤ k) (take : Fin (2*k) → Prop)
    (s t : Fin (2*k)) : Universal (graph k take) t 2 s := by
  intro c initial
  have different : decode c ≠ decode s := by
    intro same
    exact initial (by simpa only [encode_decode] using congrArg encode same)
  have win := two_move hk (fun v => take (encode v)) (decode s) (decode t) (decode c) different
  simpa only [graphIso,encode_decode] using (graphIso k take).winning win

theorem decode_eq_iff {k : Nat} (t : Fin (2*k)) (v : Vertex k) :
    decode t = v ↔ t = encode v := by
  constructor
  · intro h; simpa only [encode_decode] using congrArg encode h
  · intro h; subst t; exact decode_encode v

theorem graph_missing_iff {k : Nat} (hk : 11 ≤ k) (take : Fin (2*k) → Prop)
    (s t : Fin (2*k)) :
    (s ≠ t ∧ ¬ graph k take s t) ↔
      ((t = encode (first (decode s)) ∨ t = encode (second (decode s))) ∨
        (take s ∧ t = encode (third (decode s)))) := by
  classical
  have equivalence : (s ≠ t ∧ ¬ graph k take s t) ↔
      selected (fun v => take (encode v)) (decode s) (decode t) := by
    constructor
    · intro h
      apply Classical.byContradiction
      intro absent
      exact h.2 ⟨fun same => h.1 (by simpa only [encode_decode] using congrArg encode same),absent⟩
    · intro h
      have fullPair : full (decode s) (decode t) := by
        rcases h with base | extra
        · exact Or.inl base
        · exact Or.inr extra.2
      exact ⟨fun same => full_loopless hk _ (same ▸ fullPair),fun edge => edge.2 h⟩
  rw [equivalence]
  simp only [selected,missing,decode_eq_iff,encode_decode]

theorem third_distinct {k : Nat} (s : Vertex k) :
    first s ≠ third s ∧ second s ≠ third s := by
  cases s <;> simp [first,second,third]

/-- Exact counting for every optional subset. -/
theorem graph_missingCount {k : Nat} (hk : 11 ≤ k) (take : Fin (2*k) → Prop) :
    missingCount (graph k take) = 4*k + card take := by
  classical
  have singleton (a : Fin (2*k)) : card (fun t => t = a) = 1 := by
    rw [card_eq]
    simp [List.filter_eq,(List.nodup_finRange (2*k)).count]
  have row (s : Fin (2*k)) : card (fun t => s ≠ t ∧ ¬ graph k take s t) =
      2 + (if take s then 1 else 0) := by
    rw [card_congr (graph_missing_iff hk take s),card_disjoint_union]
    · rw [DenseTwoType.card_two _ _ (fun same =>
        neighbours_distinct (by omega : 5 ≤ k) _ (encode_injective same))]
      by_cases chosen : take s
      · rw [if_pos chosen]
        rw [card_congr (Q := fun t => t = encode (third (decode s))) (fun t => by simp only [chosen,true_and])]
        exact congrArg (fun x => 2+x) (singleton _)
      · rw [if_neg chosen]
        have zero : card (fun t => take s ∧ t = encode (third (decode s))) = 0 := by
          apply card_eq_zero.mpr
          intro t h; exact chosen h.1
        rw [zero]
    · intro t base extra
      rcases base with base | base
      · exact (third_distinct (decode s)).1 (encode_injective (base.symm.trans extra.2))
      · exact (third_distinct (decode s)).2 (encode_injective (base.symm.trans extra.2))
  rw [ConstructionCounts.missing_rows]
  simp only [row]
  have total := ConstructionCounts.weighted_indicators (List.finRange (2*k))
    (fun _ => True) take 2 1
  simp only [ite_true,decide_true,Nat.one_mul] at total
  have all : (List.finRange (2*k)).filter (fun _ => true) = List.finRange (2*k) :=
    List.filter_eq_self.mpr (by intros; rfl)
  rw [all,List.length_finRange,← card_eq take] at total
  omega

theorem graph_score {k : Nat} (hk : 11 ≤ k) (take : Fin (2*k) → Prop) :
    score (graph k take) = 4*k + card take := by
  rw [score_eq_missing (graph k take) (fun s t _ _ =>
    universal_guaranteed (graph_two_move hk take s t)),graph_missingCount hk]

theorem prefix_count {N q : Nat} (hq : q ≤ N) :
    card (fun s : Fin N => s.val < q) = q := by
  let embed : Fin q → Fin N := fun i => ⟨i.val,by omega⟩
  apply ConstructionCounts.card_image embed
  · intro i j same
    apply Fin.ext
    have equal : (embed i).val = (embed j).val := congrArg Fin.val same
    exact equal
  · intro s
    constructor
    · intro small
      exact ⟨⟨s.val,small⟩,rfl⟩
    · rintro ⟨i,same⟩
      have equal := congrArg Fin.val same
      dsimp [embed] at equal
      omega

/-- The first q vertices in the displayed point/line numbering receive
optional missing arcs. This is an executable adjacency recipe. -/
def prefixGraph (k q : Nat) : Graph (Fin (2*k)) := graph k (fun s => s.val < q)

instance (k q : Nat) (s t : Fin (2*k)) : Decidable (prefixGraph k q s t) :=
  inferInstanceAs (Decidable (graph k (fun s => s.val < q) s t))

theorem prefix_missingCount {k q : Nat} (hk : 11 ≤ k) (hq : q ≤ 2*k) :
    missingCount (prefixGraph k q) = 4*k+q := by
  rw [prefixGraph,graph_missingCount hk,prefix_count hq]

theorem prefix_score {k q : Nat} (hk : 11 ≤ k) (hq : q ≤ 2*k) :
    score (prefixGraph k q) = 4*k+q := by
  rw [prefixGraph,graph_score hk,prefix_count hq]

theorem prefix_arcCount {k q : Nat} (hk : 11 ≤ k) (hq : q ≤ 2*k) :
    arcCount (prefixGraph k q) = (2*k)*(2*k-1)-(4*k+q) := by
  have partition := arcCount_add_missingCount (prefixGraph k q)
    (graph_loopless k (fun s => s.val < q))
  rw [prefix_missingCount hk hq] at partition
  omega

/-- Every missing budget h in [2n,3n] is exactly attained for even n≥22. -/
theorem maximum {k h : Nat} (hk : 11 ≤ k) (low : 4*k ≤ h) (high : h ≤ 6*k) :
    IsMaximum (2*k) ((2*k)*(2*k-1)-h) h := by
  have optional : h-4*k ≤ 2*k := by omega
  have exactMissing : 4*k+(h-4*k) = h := by omega
  have capacity : h ≤ (2*k)*(2*k-1) := by
    have mul := Nat.mul_le_mul_left (2*k) (show 3 ≤ 2*k-1 by omega)
    omega
  constructor
  · intro E noLoops arrows
    have partition := arcCount_add_missingCount E noLoops
    have bound := score_le_missing E
    omega
  · refine ⟨prefixGraph k (h-4*k),graph_loopless _ _,?_,?_⟩
    · simpa only [exactMissing] using prefix_arcCount hk optional
    · simpa only [exactMissing] using prefix_score hk optional

#print axioms graph_two_move
#print axioms graph_missingCount
#print axioms maximum

end Delivery.DenseEnvelope
