import DenseZero

/-! Finite cardinality and finite-map counting for the dense staircase.
All counts are literal filtered-list lengths. No graph-count premise or
functional-cycle existence is introduced as an axiom. -/
namespace Delivery.DenseCombinatorics
open FiniteGame Extremal

noncomputable def elems {n : Nat} (P : Fin n → Prop) : List (Fin n) := by
  classical
  exact (List.finRange n).filter fun x => decide (P x)

noncomputable def card {n : Nat} (P : Fin n → Prop) : Nat := (elems P).length

theorem card_eq {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    card P = ((List.finRange n).filter fun x => decide (P x)).length := by
  unfold card elems
  apply congrArg (fun p => ((List.finRange n).filter p).length)
  funext x
  exact decide_eq_decide.mpr Iff.rfl

@[simp] theorem mem_elems {n : Nat} {P : Fin n → Prop} {x : Fin n} :
    x ∈ elems P ↔ P x := by
  classical
  simp [elems]

theorem elems_nodup {n : Nat} (P : Fin n → Prop) : (elems P).Nodup := by
  classical
  exact (List.nodup_finRange n).filter _

theorem card_congr {n : Nat} {P Q : Fin n → Prop}
    (same : ∀ x, P x ↔ Q x) : card P = card Q := by
  have h : P = Q := funext fun x => propext (same x)
  rw [h]

theorem card_mono {n : Nat} {P Q : Fin n → Prop}
    (subset : ∀ x, P x → Q x) : card P ≤ card Q := by
  exact (elems_nodup P).length_le_of_subset (fun x hx =>
    mem_elems.mpr (subset x (mem_elems.mp hx)))

@[simp] theorem card_false (n : Nat) : card (fun _ : Fin n => False) = 0 := by
  classical
  simp [card,elems]

@[simp] theorem card_true (n : Nat) : card (fun _ : Fin n => True) = n := by
  classical
  unfold card elems
  rw [List.filter_eq_self.mpr (by intro x _; simp)]
  exact List.length_finRange

theorem card_eq_zero {n : Nat} {P : Fin n → Prop} :
    card P = 0 ↔ ∀ x, ¬ P x := by
  constructor
  · intro h x hx
    have hp := List.length_pos_of_mem (mem_elems.mpr hx)
    change 0 < card P at hp
    omega
  · intro h
    have hc : card P = card (fun _ => False) := card_congr (fun x => by simp [h x])
    simpa using hc

theorem card_positive {n : Nat} {P : Fin n → Prop} :
    0 < card P ↔ ∃ x, P x := by
  change 0 < (elems P).length ↔ _
  simpa using (List.length_pos_iff_exists_mem (l := elems P))

theorem filter_partition_prop {α : Type} (xs : List α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    ((xs.filter fun x => decide (P x ∧ Q x)).length) +
    ((xs.filter fun x => decide (P x ∧ ¬ Q x)).length) =
    ((xs.filter fun x => decide (P x)).length) := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hp : P x <;> by_cases hq : Q x <;> simp_all <;> omega

theorem card_partition {n : Nat} (P Q : Fin n → Prop) :
    card (fun x => P x ∧ Q x) + card (fun x => P x ∧ ¬ Q x) = card P := by
  classical
  rw [card_eq,card_eq,card_eq]
  exact filter_partition_prop (List.finRange n) P Q

theorem card_disjoint_union {n : Nat} {P Q : Fin n → Prop}
    (disjoint : ∀ x, P x → Q x → False) :
    card (fun x => P x ∨ Q x) = card P + card Q := by
  have partition := card_partition (fun x => P x ∨ Q x) P
  have left : card (fun x => (P x ∨ Q x) ∧ P x) = card P :=
    card_congr (fun _ => ⟨fun h => h.2,fun h => ⟨Or.inl h,h⟩⟩)
  have right : card (fun x => (P x ∨ Q x) ∧ ¬ P x) = card Q := by
    apply card_congr
    intro x
    constructor
    · intro h; exact h.1.resolve_left h.2
    · intro h; exact ⟨Or.inr h,fun hp => disjoint x hp h⟩
  omega

theorem card_injection {n m : Nat} {P : Fin n → Prop} {Q : Fin m → Prop}
    (f : Fin n → Fin m) (target : ∀ x, P x → Q (f x))
    (injective : ∀ x y, P x → P y → f x = f y → x = y) :
    card P ≤ card Q := by
  have nodup : ((elems P).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply (elems_nodup P).imp_of_mem
    intro x y hx hy different equal
    exact different (injective x y (mem_elems.mp hx) (mem_elems.mp hy) equal)
  have subset : (elems P).map f ⊆ elems Q := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact mem_elems.mpr (target x (mem_elems.mp hx))
  change (elems P).length ≤ (elems Q).length
  simpa only [List.length_map] using nodup.length_le_of_subset subset

theorem card_injection_two_excluded {n m : Nat} {P : Fin n → Prop}
    {Q : Fin m → Prop} (f : Fin n → Fin m)
    (target : ∀ x, P x → Q (f x))
    (injective : ∀ x y, P x → P y → f x = f y → x = y)
    (a b : Fin m) (ha : Q a) (hb : Q b) (different : a ≠ b)
    (exclude_a : ∀ x, P x → f x ≠ a) (exclude_b : ∀ x, P x → f x ≠ b) :
    card P + 2 ≤ card Q := by
  have mapped : ((elems P).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply (elems_nodup P).imp_of_mem
    intro x y hx hy hne heq
    exact hne (injective x y (mem_elems.mp hx) (mem_elems.mp hy) heq)
  have na : a ∉ (elems P).map f := by
    intro h; obtain ⟨x,hx,hf⟩ := List.mem_map.mp h
    exact exclude_a x (mem_elems.mp hx) hf
  have nb : b ∉ (elems P).map f := by
    intro h; obtain ⟨x,hx,hf⟩ := List.mem_map.mp h
    exact exclude_b x (mem_elems.mp hx) hf
  have nodup : (a :: b :: (elems P).map f).Nodup := by
    simp [List.nodup_cons,different,na,nb,mapped]
  have subset : a :: b :: (elems P).map f ⊆ elems Q := by
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · exact mem_elems.mpr ha
    · exact mem_elems.mpr hb
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact mem_elems.mpr (target x (mem_elems.mp hx))
  have length := nodup.length_le_of_subset subset
  simp only [List.length_cons,List.length_map] at length
  change card P + 1 + 1 ≤ card Q at length
  omega

/-- A pointwise logical equivalence preserves a literal filtered-list count. -/
theorem filter_count_congr {α : Type} (xs : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (same : ∀ x, P x ↔ Q x) :
    (xs.filter fun x => decide (P x)).length =
    (xs.filter fun x => decide (Q x)).length := by
  apply congrArg (fun p => (xs.filter p).length)
  funext x
  exact decide_eq_decide.mpr (same x)

/-- Missing nonloop pairs that are not guaranteed. This is an actual
finite graph count, not an independent numerical loss parameter. -/
noncomputable def lossCount {n : Nat} (E : Graph (Fin n)) : Nat := by
  classical
  exact ((allPairs n).filter fun p =>
    decide ((p.1 ≠ p.2 ∧ ¬ E p.1 p.2) ∧ ¬ Guaranteed E p.1 p.2)).length

theorem lossCount_eq {n : Nat} (E : Graph (Fin n)) [DecidableRel E]
    [DecidableRel (Guaranteed E)] :
    lossCount E = ((allPairs n).filter fun p =>
      decide ((p.1 ≠ p.2 ∧ ¬ E p.1 p.2) ∧ ¬ Guaranteed E p.1 p.2)).length := by
  unfold lossCount
  apply congrArg (fun p => ((allPairs n).filter p).length)
  funext p
  exact decide_eq_decide.mpr Iff.rfl

/-- Every missing nonloop pair is exactly one of a guarantee or a loss. -/
theorem score_add_lossCount {n : Nat} (E : Graph (Fin n)) :
    score E + lossCount E = missingCount E := by
  classical
  have partition := filter_partition_prop (allPairs n)
    (fun p => p.1 ≠ p.2 ∧ ¬ E p.1 p.2) (fun p => Guaranteed E p.1 p.2)
  have successful : score E = ((allPairs n).filter fun p =>
      decide ((p.1 ≠ p.2 ∧ ¬ E p.1 p.2) ∧ Guaranteed E p.1 p.2)).length := by
    unfold score
    apply filter_count_congr
    intro p
    exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,
      fun h => ⟨h.1.1,h.1.2,h.2⟩⟩
  rw [successful,lossCount_eq,missingCount_eq]
  exact partition

/-- The missing pairs and arrows partition all nonloop ordered pairs. -/
theorem arcCount_add_missingCount {n : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) :
    arcCount E + missingCount E = n * (n - 1) := by
  classical
  have partition := filter_partition_prop (allPairs n)
    (fun p => p.1 ≠ p.2) (fun p => E p.1 p.2)
  have present : ((allPairs n).filter fun p =>
      decide (p.1 ≠ p.2 ∧ E p.1 p.2)).length = arcCount E := by
    rw [arcCount_eq]
    apply filter_count_congr
    intro p
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_,h⟩
      intro equal
      exact loopless p.1 (equal ▸ h)
  rw [present] at partition
  rw [missingCount_eq]
  calc
    _ = ((allPairs n).filter fun p => decide (p.1 ≠ p.2)).length := partition
    _ = n * (n - 1) := DenseZero.nonloopPairs_length n

#print axioms card_partition
#print axioms card_injection_two_excluded
#print axioms score_add_lossCount
#print axioms arcCount_add_missingCount
end Delivery.DenseCombinatorics
