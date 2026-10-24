import DenseZero
import DenseCounting
import DenseCombinatorics

/-! The dense staircase upper bound from the actual directed graph.
The degree-one missing rows supply two camping obstructions. Their finite
image counts, rather than a supplied counting premise, force the losses. -/
namespace Delivery.DenseStaircase
open FiniteGame Extremal
open DenseCombinatorics

def Missing {V : Type} (E : Graph V) (s t : V) : Prop := s ≠ t ∧ ¬ E s t

def One {V : Type} (E : Graph V) (s : V) : Prop :=
  ∃ t, Missing E s t ∧ ∀ u, Missing E s u → u = t

noncomputable def next {V : Type} (E : Graph V) (s : V) : V := by
  classical
  exact if h : One E s then Classical.choose h else s

theorem next_missing {V : Type} {E : Graph V} {s : V} (one : One E s) :
    Missing E s (next E s) := by
  classical
  simp only [next, dif_pos one]
  exact (Classical.choose_spec one).1

theorem next_unique {V : Type} {E : Graph V} {s t : V} (one : One E s)
    (missing : Missing E s t) : t = next E s := by
  classical
  simp only [next, dif_pos one]
  exact (Classical.choose_spec one).2 t missing

def Image {V : Type} (E : Graph V) (t : V) : Prop :=
  ∃ s, One E s ∧ next E s = t

def Survivor {V : Type} (E : Graph V) (s : V) : Prop :=
  One E s ∧ ¬ Image E s ∧ ∀ c, One E c → next E c = next E s → c = s

theorem one_covers {V : Type} {E : Graph V} {c y : V}
    (one : One E c) (different : y ≠ next E c) : Legal E c y := by
  classical
  by_cases same : c = y
  · exact Or.inl same
  · apply Or.inr
    apply Classical.byContradiction
    intro missing
    exact different (next_unique one ⟨same, missing⟩)

/-- Every missing pair leaving the image of a degree-one missing row loses.
The pursuer camps at that row and intercepts each nonwaiting departure. -/
theorem image_source_blocked {V : Type} {E : Graph V} (loopless : Loopless E)
    {s t : V} (image : Image E s) (missing : Missing E s t) :
    ¬ Guaranteed E s t := by
  obtain ⟨c, one, image⟩ := image
  have different : c ≠ s := by
    simpa only [image] using (next_missing one).1
  intro guaranteed
  obtain ⟨k, win⟩ := guaranteed c different
  apply VertexBound.source_camping missing.1 missing.2 _ k win
  intro z edge
  apply one_covers one
  rw [image]
  intro same
  subst z
  exact loopless s edge

/-- A second degree-one missing row with the same image blocks the first. -/
theorem repeated_image_blocked {V : Type} {E : Graph V} {s c : V}
    (oneS : One E s) (oneC : One E c) (different : c ≠ s)
    (same : next E c = next E s) : ¬ Guaranteed E s (next E s) := by
  intro guaranteed
  obtain ⟨k, win⟩ := guaranteed c different
  have missing := next_missing oneS
  apply VertexBound.source_camping missing.1 missing.2 _ k win
  intro z edge
  apply one_covers oneC
  rw [same]
  intro equal
  exact missing.2 (equal ▸ edge)

theorem nonsurvivor_blocked {V : Type} {E : Graph V} (loopless : Loopless E)
    {s t : V} (one : One E s) (outside : ¬ Survivor E s)
    (missing : Missing E s t) : ¬ Guaranteed E s t := by
  classical
  by_cases image : Image E s
  · exact image_source_blocked loopless image missing
  · have repeated : ∃ c, One E c ∧ next E c = next E s ∧ c ≠ s := by
      apply Classical.byContradiction
      intro none
      apply outside
      refine ⟨one, image, ?_⟩
      intro c oneC same
      apply Classical.byContradiction
      intro different
      exact none ⟨c, oneC, same, different⟩
    obtain ⟨c, oneC, same, different⟩ := repeated
    rw [next_unique one missing]
    exact repeated_image_blocked one oneC different same

/-- Unique-image survivors have pairwise distinct images. -/
theorem survivor_injective {V : Type} {E : Graph V} {s c : V}
    (hs : Survivor E s) (hc : Survivor E c) (same : next E s = next E c) :
    s = c := hc.2.2 s hs.1 same

/-- If the image stays among the degree-one rows, two distinct image vertices
cannot be images of survivors. Two consecutive images suffice; no cycle
enumeration is needed. -/
theorem two_excluded_images {V : Type} {E : Graph V}
    (inhabited : ∃ s, One E s) (closed : ∀ s, Image E s → One E s) :
    ∃ y z, y ≠ z ∧ Image E y ∧ Image E z ∧
      (∀ s, Survivor E s → next E s ≠ y) ∧
      (∀ s, Survivor E s → next E s ≠ z) := by
  obtain ⟨s, hs⟩ := inhabited
  let x := next E s
  have hx : Image E x := ⟨s, hs, rfl⟩
  have ox := closed x hx
  let y := next E x
  have hy : Image E y := ⟨x, ox, rfl⟩
  have oy := closed y hy
  let z := next E y
  have hz : Image E z := ⟨y, oy, rfl⟩
  refine ⟨y, z, (next_missing oy).1, hy, hz, ?_, ?_⟩
  · intro c hc same
    have xc : x = c := hc.2.2 x ox same.symm
    exact hc.2.1 (xc ▸ hx)
  · intro c hc same
    have yc : y = c := hc.2.2 y oy same.symm
    exact hc.2.1 (yc ▸ hy)

noncomputable def rowMissing {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Nat := by
  classical
  exact ((List.finRange n).filter fun t => decide (Missing E s t)).length

noncomputable def rowLoss {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Nat := by
  classical
  exact ((List.finRange n).filter fun t =>
    decide (Missing E s t ∧ ¬ Guaranteed E s t)).length

theorem one_iff_rowMissing {n : Nat} (E : Graph (Fin n)) (s : Fin n) :
    One E s ↔ rowMissing E s = 1 := by
  classical
  constructor
  · intro one
    have member : next E s ∈ (List.finRange n).filter
        (fun t => decide (Missing E s t)) := by
      simp [next_missing one]
    have positive := List.length_pos_of_mem member
    have bound := List.Nodup.length_le_of_subset ((List.nodup_finRange n).filter
      (fun t => decide (Missing E s t)))
      (l₂ := [next E s]) (by
        intro t ht
        simp only [List.mem_filter, decide_eq_true_eq] at ht
        simp [next_unique one ht.2])
    simp only [List.length_cons, List.length_nil] at bound
    unfold rowMissing
    omega
  · intro one
    obtain ⟨t, single⟩ := List.length_eq_one_iff.mp one
    have ht : Missing E s t := by
      have member : t ∈ (List.finRange n).filter
          (fun t => decide (Missing E s t)) := by rw [single]; simp
      simpa using member
    refine ⟨t, ht, ?_⟩
    intro u hu
    have member : u ∈ (List.finRange n).filter
        (fun t => decide (Missing E s t)) := by simp [hu]
    simpa only [single, List.mem_cons, List.not_mem_nil, or_false] using member

theorem positive_score_has_indirect {n : Nat} {E : Graph (Fin n)}
    (positive : 0 < score E) : ∃ s t, Indirect E s t := by
  classical
  obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos positive
  exact ⟨p.1, p.2, of_decide_eq_true (List.mem_filter.mp hp).2⟩

theorem rowMissing_positive {n : Nat} {E : Graph (Fin n)}
    (positive : 0 < score E) (s : Fin n) : 1 ≤ rowMissing E s := by
  classical
  obtain ⟨a, b, hab⟩ := positive_score_has_indirect positive
  obtain ⟨t, different, absent⟩ := DenseZero.indirect_missing_each_row hab s
  apply List.length_pos_of_mem (a := t)
  simp [Missing, different, absent]

theorem rowMissing_two {n : Nat} {E : Graph (Fin n)}
    (positive : 0 < score E) {s : Fin n} (multiple : ¬ One E s) :
    2 ≤ rowMissing E s := by
  have lower := rowMissing_positive positive s
  have notone : rowMissing E s ≠ 1 := fun h => multiple ((one_iff_rowMissing E s).mpr h)
  omega

theorem image_rowLoss {n : Nat} {E : Graph (Fin n)} (loopless : Loopless E)
    {s : Fin n} (image : Image E s) : rowLoss E s = rowMissing E s := by
  classical
  unfold rowLoss rowMissing
  congr 2
  funext t
  apply decide_eq_decide.mpr
  exact ⟨And.left, fun missing => ⟨missing, image_source_blocked loopless image missing⟩⟩

theorem nonsurvivor_rowLoss {n : Nat} {E : Graph (Fin n)} (loopless : Loopless E)
    {s : Fin n} (one : One E s) (outside : ¬ Survivor E s) :
    rowLoss E s = 1 := by
  classical
  have same : rowLoss E s = rowMissing E s := by
    unfold rowLoss rowMissing
    congr 2
    funext t
    apply decide_eq_decide.mpr
    exact ⟨And.left, fun missing =>
      ⟨missing, nonsurvivor_blocked loopless one outside missing⟩⟩
  exact same.trans ((one_iff_rowMissing E s).mp one)

/-- Distinct classes of rows contribute disjoint losses. -/
theorem weighted_rows {α : Type} (xs : List α) (P Q : α → Prop) (w : α → Nat)
    [DecidablePred P] [DecidablePred Q]
    (disjoint : ∀ x, P x → ¬ Q x)
    (one : ∀ x, x ∈ xs → P x → 1 ≤ w x)
    (two : ∀ x, x ∈ xs → Q x → 2 ≤ w x) :
    (xs.filter (fun x => decide (P x))).length +
      2 * (xs.filter (fun x => decide (Q x))).length ≤ (xs.map w).sum := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y hy => one y (by simp [hy]))
      (fun y hy => two y (by simp [hy]))
    have hp := one x (by simp)
    have hq := two x (by simp)
    by_cases p : P x <;> by_cases q : Q x
    · exact False.elim (disjoint x p q)
    all_goals simp only [p, q, true_implies, false_implies] at hp hq
    all_goals simp only [List.filter_cons, List.map_cons, List.sum_cons]
    all_goals simp only [p, q, decide_true, decide_false, Bool.false_eq_true,
      if_false, if_true, List.length_cons]
    all_goals omega

theorem pair_filter_rows {n : Nat} (P : Fin n → Fin n → Prop) [DecidableRel P] :
    ((allPairs n).filter fun p => decide (P p.1 p.2)).length =
      ((List.finRange n).map fun s =>
        ((List.finRange n).filter fun t => decide (P s t)).length).sum := by
  unfold allPairs
  rw [List.filter_flatMap, List.length_flatMap]
  simp only [List.filter_map, List.length_map, Function.comp_def]

theorem missingCount_rows {n : Nat} (E : Graph (Fin n)) :
    missingCount E = ((List.finRange n).map (rowMissing E)).sum := by
  classical
  unfold missingCount allPairs
  rw [List.filter_flatMap, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [List.filter_map, List.length_map]
  unfold rowMissing
  congr 2
  funext t
  exact decide_eq_decide.mpr Iff.rfl

theorem degree_count {n : Nat} (E : Graph (Fin n)) (positive : 0 < score E) :
    2 * n ≤ missingCount E +
      ((List.finRange n).filter fun s => @decide (One E s) (Classical.propDecidable _)).length := by
  classical
  have bound := weighted_rows (List.finRange n) (One E) (fun s => ¬ One E s)
    (rowMissing E) (fun s hs hn => hn hs)
    (fun s _ _ => rowMissing_positive positive s)
    (fun s _ hs => rowMissing_two positive hs)
  have partition := VertexBound.filter_partition (List.finRange n)
    (fun s => decide (One E s))
  have same : (fun s => !(decide (One E s))) = (fun s => decide (¬ One E s)) := by
    funext s
    by_cases h : One E s <;> simp [h]
  rw [same, List.length_finRange] at partition
  rw [← missingCount_rows E] at bound
  omega

theorem loss_count {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (positive : 0 < score E) :
    card (One E) + 2 * card (fun s => Image E s ∧ ¬ One E s) ≤
      ((List.finRange n).map (rowLoss E)).sum + card (Survivor E) := by
  classical
  have lower := weighted_rows (List.finRange n)
    (fun s => One E s ∧ ¬ Survivor E s)
    (fun s => Image E s ∧ ¬ One E s) (rowLoss E)
    (fun s hs hq => hq.2 hs.1)
    (fun s _ hs => by
      rw [nonsurvivor_rowLoss loopless hs.1 hs.2]
      exact Nat.le_refl 1)
    (fun s _ hs => by
      rw [image_rowLoss loopless hs.1]
      exact rowMissing_two positive hs.2)
  have partition := card_partition (One E) (Survivor E)
  have same : card (fun s => One E s ∧ Survivor E s) = card (Survivor E) :=
    card_congr (fun s => ⟨And.right, fun h => ⟨h.1, h⟩⟩)
  have lower' : card (fun s => One E s ∧ ¬ Survivor E s) +
      2 * card (fun s => Image E s ∧ ¬ One E s) ≤
      ((List.finRange n).map (rowLoss E)).sum := by
    rw [card_eq, card_eq]
    exact lower
  omega

theorem image_counts {n : Nat} (E : Graph (Fin n))
    (inhabited : ∃ s, One E s) :
    card (Survivor E) + card (fun s => Image E s ∧ One E s) ≤ card (One E) ∧
    card (Survivor E) ≤ card (fun s => Image E s ∧ One E s) +
      card (fun s => Image E s ∧ ¬ One E s) ∧
    (card (fun s => Image E s ∧ ¬ One E s) = 0 →
      card (Survivor E) + 2 ≤ card (fun s => Image E s ∧ One E s)) := by
  have partition := card_partition (Image E) (One E)
  have union := card_disjoint_union (P := Survivor E)
    (Q := fun s => Image E s ∧ One E s) (fun s hs hq => hs.2.1 hq.1)
  have sub := card_mono (P := fun s => Survivor E s ∨ (Image E s ∧ One E s))
    (Q := One E) (fun s h => h.elim (fun h => h.1) And.right)
  have injection := card_injection (P := Survivor E) (Q := Image E) (next E)
    (fun s hs => ⟨s, hs.1, rfl⟩)
    (fun s c hs hc eq => survivor_injective hs hc eq)
  refine ⟨by omega, by omega, ?_⟩
  intro empty
  have closed : ∀ s, Image E s → One E s := by
    intro s hs
    apply Classical.byContradiction
    intro outside
    exact card_eq_zero.mp empty s ⟨hs, outside⟩
  obtain ⟨y, z, different, hy, hz, excludeY, excludeZ⟩ :=
    two_excluded_images inhabited closed
  have two := card_injection_two_excluded (P := Survivor E) (Q := Image E) (next E)
    (fun s hs => ⟨s, hs.1, rfl⟩)
    (fun s c hs hc eq => survivor_injective hs hc eq)
    y z hy hz different excludeY excludeZ
  omega

theorem lossCount_rows {n : Nat} (E : Graph (Fin n)) :
    lossCount E = ((List.finRange n).map (rowLoss E)).sum := by
  classical
  unfold lossCount allPairs
  rw [List.filter_flatMap, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [List.filter_map, List.length_map]
  unfold rowLoss
  congr 2
  funext t
  exact decide_eq_decide.mpr Iff.rfl

/-- All five counting premises of the numerical staircase theorem follow
from the graph and its actual guaranteed pairs. -/
theorem counts_if_positive {n r : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) (positive : 0 < score E)
    (hr : 1 ≤ r) (band : missingCount E + r = 2 * n) :
    ∃ ell a b rho : Nat,
      r ≤ ell ∧ ell + 2*b ≤ lossCount E + rho ∧ rho + a ≤ ell ∧
      rho ≤ a + b ∧ (b = 0 → rho + 2 ≤ a) := by
  have degree := degree_count E positive
  change 2 * n ≤ missingCount E + card (One E) at degree
  have nonempty : ∃ s, One E s := card_positive.mp (by omega)
  have losses := loss_count E loopless positive
  rw [← lossCount_rows E] at losses
  obtain ⟨outside, distinct, excluded⟩ := image_counts E nonempty
  exact ⟨card (One E), card (fun s => Image E s ∧ One E s),
    card (fun s => Image E s ∧ ¬ One E s), card (Survivor E),
    by omega, losses, outside, distinct, excluded⟩

/-- Unconditional staircase upper bound in missing-arrow coordinates. -/
theorem bound_missing {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (hn : 2 ≤ n) (low : n ≤ missingCount E) (high : missingCount E < 2 * n) :
    score E ≤ missingCount E - DenseCounting.ceilHalf (2 * n - missingCount E) - 1 := by
  apply DenseCounting.final_band_bound_subtracted
    (D := lossCount E) hn (by omega) (by omega) (by omega)
    (score_add_lossCount E)
  intro positive
  exact counts_if_positive E loopless positive (by omega) (by omega)

/-- The equivalent additive bound is convenient at exact budgets. -/
theorem bound_missing_add {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (hn : 2 ≤ n) (low : n ≤ missingCount E) (high : missingCount E < 2 * n) :
    score E + DenseCounting.ceilHalf (2 * n - missingCount E) + 1 ≤ missingCount E := by
  apply DenseCounting.final_band_bound
    (D := lossCount E) hn (by omega) (by omega) (by omega)
    (score_add_lossCount E)
  intro positive
  exact counts_if_positive E loopless positive (by omega) (by omega)

/-- Staircase upper bound at the usual offset above `n*(n-3)` arrows. -/
theorem bound_at_offset {n r : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (hn : 3 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (arrows : arcCount E = n * (n - 3) + r) :
    score E ≤ 2 * n - r - DenseCounting.ceilHalf r - 1 := by
  have total := arcCount_add_missingCount E loopless
  have identity : n * (n - 1) = n * (n - 3) + 2 * n := by
    have subtract : n - 1 = (n - 3) + 2 := by omega
    rw [subtract, Nat.mul_add, Nat.mul_comm n 2]
  rw [identity, arrows] at total
  have band : missingCount E + r = 2 * n := by omega
  have low : n ≤ missingCount E := by omega
  have high : missingCount E < 2 * n := by omega
  have bound := bound_missing E loopless (by omega) low high
  have missing : missingCount E = 2 * n - r := by omega
  have offset : 2 * n - missingCount E = r := by omega
  rw [offset, missing] at bound
  exact bound

/-- No cardinality hypotheses: the graph's actual arrow count determines
the bound throughout the final nonzero-density band. -/
theorem bound_arcs {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (lower : n * (n - 3) < arcCount E)
    (upper : arcCount E ≤ n * (n - 2)) :
    score E ≤ 2 * n - (arcCount E - n * (n - 3)) -
      DenseCounting.ceilHalf (arcCount E - n * (n - 3)) - 1 := by
  have hn : 3 ≤ n := by
    by_cases h : 3 ≤ n
    · exact h
    · have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases cases with rfl | rfl | rfl <;> simp at lower upper <;> omega
  have upperIdentity : n * (n - 2) = n * (n - 3) + n := by
    have subtract : n - 2 = (n - 3) + 1 := by omega
    rw [subtract, Nat.mul_add, Nat.mul_one]
  rw [upperIdentity] at upper
  exact bound_at_offset E loopless hn (by omega) (by omega) (by omega)

#print axioms bound_arcs
#print axioms bound_at_offset
#print axioms counts_if_positive
#print axioms bound_missing
#print axioms nonsurvivor_blocked
#print axioms two_excluded_images
#print axioms image_counts
end Delivery.DenseStaircase
