import LadderCounters
import LadderGeometry

/-! Finite cardinalities connecting arbitrary column beliefs to the exact
counter lower bound. Cardinals count a predicate over the full `Fin` list.
-/

namespace Princess.LadderCardinality

open Princess.LadderGeometry

noncomputable def cardOn {α : Type} (xs : List α) (P : α → Prop) : Nat := by
  classical
  exact xs.countP (fun x => decide (P x))

theorem cardOn_cons {α : Type} (a : α) (xs : List α) (P : α → Prop) [Decidable (P a)] :
    cardOn (a :: xs) P = cardOn xs P + if P a then 1 else 0 := by
  classical
  by_cases h : P a <;> simp [cardOn, h]

theorem cardOn_append {α : Type} (xs ys : List α) (P : α → Prop) :
    cardOn (xs ++ ys) P = cardOn xs P + cardOn ys P := by
  simp only [cardOn, List.countP_append]

theorem cardOn_map {α β : Type} (xs : List α) (f : α → β) (P : β → Prop) :
    cardOn (xs.map f) P = cardOn xs (fun x => P (f x)) := by
  simp only [cardOn, List.countP_map]
  rfl

theorem cardOn_congr {α : Type} (xs : List α) (P Q : α → Prop)
    (h : ∀ x ∈ xs, P x ↔ Q x) : cardOn xs P = cardOn xs Q := by
  classical
  apply List.countP_congr
  intro x hx
  simpa using h x hx

theorem cardOn_mono {α : Type} (xs : List α) (P Q : α → Prop)
    (h : ∀ x ∈ xs, P x → Q x) : cardOn xs P ≤ cardOn xs Q := by
  classical
  apply List.countP_mono_left
  intro x hx hp
  simpa using h x hx (of_decide_eq_true hp)

theorem cardOn_split {α : Type} (xs : List α) (P Q : α → Prop) :
    cardOn xs P = cardOn xs (fun x => P x ∧ Q x) +
      cardOn xs (fun x => P x ∧ ¬ Q x) := by
  classical
  induction xs with
  | nil => simp [cardOn]
  | cons a xs ih =>
      rw [cardOn_cons, cardOn_cons, cardOn_cons]
      by_cases hp : P a <;> by_cases hq : Q a <;> simp only [hp, hq, and_true,
        and_false, not_true_eq_false, not_false_eq_true,
        ↓reduceIte] <;> omega

theorem cardOn_pos {α : Type} (xs : List α) (P : α → Prop) :
    0 < cardOn xs P ↔ ∃ x ∈ xs, P x := by
  classical
  simp only [cardOn, List.countP_pos_iff, decide_eq_true_eq]

theorem cardOn_strict {α : Type} (xs : List α) (P Q : α → Prop)
    (h : ∀ x ∈ xs, P x → Q x) (extra : ∃ x ∈ xs, Q x ∧ ¬ P x) :
    cardOn xs P < cardOn xs Q := by
  have split := cardOn_split xs Q P
  have same : cardOn xs (fun x => Q x ∧ P x) = cardOn xs P := by
    apply cardOn_congr
    intro x hx
    exact ⟨And.right, fun hp => ⟨h x hx hp, hp⟩⟩
  have positive := (cardOn_pos xs (fun x => Q x ∧ ¬ P x)).mpr extra
  omega

noncomputable def card {n : Nat} (P : ColumnSet n) : Nat := cardOn (List.finRange n) P

theorem card_le {n : Nat} (P : ColumnSet n) : card P ≤ n := by
  classical
  simpa only [card, cardOn, List.length_finRange] using
    (List.countP_le_length (p := fun x => decide (P x)) (l := List.finRange n))

theorem card_pos {n : Nat} (P : ColumnSet n) : 0 < card P ↔ ∃ x, P x := by
  rw [card, cardOn_pos]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, List.mem_finRange x, hx⟩

theorem card_mono {n : Nat} (P Q : ColumnSet n) (h : ∀ x, P x → Q x) :
    card P ≤ card Q := cardOn_mono _ _ _ (fun x _ => h x)

theorem card_full_iff {n : Nat} (P : ColumnSet n) : card P = n ↔ ∀ x, P x := by
  classical
  have h := List.countP_eq_length (p := fun x => decide (P x)) (l := List.finRange n)
  change List.countP (fun x => decide (P x)) (List.finRange n) = n ↔ ∀ x, P x
  simpa only [List.length_finRange, decide_eq_true_eq, List.mem_finRange,
    forall_const] using h

def close {n : Nat} (P : ColumnSet n) : ColumnSet n :=
  fun j => ∃ i, P i ∧ closedPathAdj i j

theorem included_close {n : Nat} (P : ColumnSet n) (x : Fin n) : P x → close P x := by
  intro h
  exact ⟨x, h, Or.inl rfl⟩

/-- Any nonempty proper path subset has an exterior neighboring vertex. -/
theorem path_boundary {n : Nat} (P : ColumnSet n)
    (nonempty : ∃ a, P a) (proper : ∃ b, ¬ P b) :
    ∃ b, ¬ P b ∧ close P b := by
  classical
  apply Classical.byContradiction
  intro absent
  have closed : ∀ a b, P a → closedPathAdj a b → P b := by
    intro a b ha edge
    apply Classical.byContradiction
    intro hb
    exact absent ⟨b, hb, a, ha, edge⟩
  cases n with
  | zero =>
      obtain ⟨a, _⟩ := nonempty
      exact Fin.elim0 a
  | succ n =>
      have constant : ∀ a : Fin (n + 1), P a ↔ P 0 := by
        intro a
        induction a using Fin.induction with
        | zero => rfl
        | succ a ih =>
            constructor
            · intro h
              apply ih.mp
              exact closed a.succ a.castSucc h (Or.inr (Or.inr rfl))
            · intro h
              exact closed a.castSucc a.succ (ih.mpr h) (Or.inr (Or.inl rfl))
      obtain ⟨a, ha⟩ := nonempty
      obtain ⟨b, hb⟩ := proper
      exact hb ((constant b).mpr ((constant a).mp ha))

theorem close_expands {n : Nat} (P : ColumnSet n)
    (positive : 0 < card P) (proper : card P < n) : card P + 1 ≤ card (close P) := by
  classical
  have nonempty := (card_pos P).mp positive
  have notfull : ¬ ∀ x, P x := by
    intro h
    have := (card_full_iff P).mpr h
    omega
  have exterior : ∃ x, ¬ P x := Classical.not_forall.mp notfull
  obtain ⟨x, hx, he⟩ := path_boundary P nonempty exterior
  have strict := cardOn_strict (List.finRange n) P (close P)
    (fun i _ => included_close P i) ⟨x, List.mem_finRange x, he, hx⟩
  exact strict

theorem probes_remove_at_most {n : Nat} (B S : ColumnSet n) :
    card B ≤ card (fun x => B x ∧ ¬ S x) + card S := by
  have partition := cardOn_split (List.finRange n) B S
  have overlap := card_mono (fun x => B x ∧ S x) S (fun _ h => h.2)
  change card B = card (fun x => B x ∧ S x) + card (fun x => B x ∧ ¬ S x) at partition
  omega

/-- The counter lower bound holds for arbitrary actual column belief/probe
sets, not just suffixes or a presumed optimal family. -/
theorem column_count_lower {n : Nat} (B S : ColumnSet n) :
    Princess.Ladder.next n (card B) (card S) ≤ card (columnStep B S) := by
  let R : ColumnSet n := fun x => B x ∧ ¬ S x
  have removed := probes_remove_at_most B S
  have included := card_mono R (close R) (included_close R)
  have bounded := card_le R
  change Princess.Ladder.next n (card B) (card S) ≤ card (close R)
  change card B ≤ card R + card S at removed
  by_cases small : card B ≤ card S
  · simp only [Princess.Ladder.next, if_pos small]
    omega
  · have positive : 0 < card R := by omega
    by_cases full : card R = n
    · have nextBound := Princess.Ladder.next_le n (card B) (card S)
      omega
    · have expansion := close_expands R positive (by omega)
      have cap : min n (card B - card S + 1) ≤ card B - card S + 1 := Nat.min_le_right _ _
      simp only [Princess.Ladder.next, if_neg small]
      omega

theorem card_threshold (n k : Nat) :
    card (fun x : Fin n => k ≤ x.val) = n - k := by
  classical
  induction n with
  | zero => simp [card, cardOn]
  | succ n ih =>
      unfold card
      rw [List.finRange_succ_last, cardOn_append, cardOn_map, cardOn_cons]
      have same : cardOn (List.finRange n) (fun x : Fin n => k ≤ x.castSucc.val) =
          card (fun x : Fin n => k ≤ x.val) := by
        apply cardOn_congr
        intro x hx
        rfl
      rw [same, ih]
      simp only [cardOn, List.countP_nil, Fin.val_last]
      by_cases h : k ≤ n <;> simp only [h, ↓reduceIte] <;> omega

def suffix {n : Nat} (b : Nat) : ColumnSet n := fun x => n - b ≤ x.val

def cut {n : Nat} (b p : Nat) : ColumnSet n :=
  fun x => n - b ≤ x.val ∧ x.val < n - b + p

theorem suffix_card {n b : Nat} (hb : b ≤ n) : card (suffix (n := n) b) = b := by
  have h := card_threshold n (n - b)
  change card (suffix (n := n) b) = n - (n - b) at h
  omega

theorem cut_card_le {n b p : Nat} : card (cut (n := n) b p) ≤ p := by
  have partition := cardOn_split (List.finRange n)
    (fun x => n - b ≤ x.val) (fun x => n - b + p ≤ x.val)
  have both : card (fun x : Fin n => n - b ≤ x.val ∧ n - b + p ≤ x.val) =
      card (fun x : Fin n => n - b + p ≤ x.val) := by
    apply cardOn_congr
    intro x hx
    constructor
    · exact And.right
    · intro h
      exact ⟨by omega, h⟩
  have difference : card (fun x : Fin n => n - b ≤ x.val ∧ ¬ n - b + p ≤ x.val) =
      card (cut (n := n) b p) := by
    apply cardOn_congr
    intro x hx
    unfold cut
    omega
  change card (fun x : Fin n => n - b ≤ x.val) =
    card (fun x : Fin n => n - b ≤ x.val ∧ n - b + p ≤ x.val) +
    card (fun x : Fin n => n - b ≤ x.val ∧ ¬ n - b + p ≤ x.val) at partition
  rw [both, difference, card_threshold, card_threshold] at partition
  omega

/-- Suffix probing attains the counter transition as an exact equality of
actual finite column sets. -/
theorem suffix_step {n b p : Nat} (hb : b ≤ n) (x : Fin n) :
    columnStep (suffix b) (cut b p) x ↔ suffix (Princess.Ladder.next n b p) x := by
  by_cases killed : b ≤ p
  · have nextZero : Princess.Ladder.next n b p = 0 := by simp [Princess.Ladder.next, killed]
    rw [nextZero]
    constructor
    · intro h
      obtain ⟨y, ⟨hy, hm⟩, he⟩ := h
      unfold suffix at hy
      unfold cut at hm
      have := y.isLt
      omega
    · intro h
      unfold suffix at h
      have := x.isLt
      omega
  · have countPositive : 0 < b - p := by omega
    have value : n - Princess.Ladder.next n b p = n - (b - p + 1) := by
      simp only [Princess.Ladder.next, if_neg killed, Nat.min_def]
      split <;> omega
    change columnStep (suffix b) (cut b p) x ↔ n - Princess.Ladder.next n b p ≤ x.val
    rw [value]
    constructor
    · intro h
      obtain ⟨y, ⟨hy, hm⟩, he⟩ := h
      unfold suffix at hy
      unfold cut at hm
      rcases he with same | forward | backward
      · subst y
        omega
      · omega
      · omega
    · intro hx
      by_cases beyond : n - b + p ≤ x.val
      · refine ⟨x, ⟨?_, ?_⟩, Or.inl rfl⟩
        · unfold suffix
          omega
        · unfold cut
          omega
      · have inside : x.val + 1 < n := by omega
        let y : Fin n := ⟨x.val + 1, inside⟩
        refine ⟨y, ⟨?_, ?_⟩, Or.inr (Or.inr rfl)⟩
        · change n - b ≤ x.val + 1
          omega
        · change ¬ (n - b ≤ x.val + 1 ∧ x.val + 1 < n - b + p)
          omega

noncomputable def roomCard {n : Nat} (S : RoomSet n) : Nat :=
  card (probeColumns S false) + card (probeColumns S true)

theorem budget_split {n : Nat} (S : RoomSet n) (color : Bool) :
    card (probeColumns S color) + card (probeColumns S (!color)) = roomCard S := by
  cases color <;> unfold roomCard <;> simp only [Bool.not_false, Bool.not_true] <;> omega

theorem recolor_card_on {n : Nat} (xs : List (Fin n)) (S : RoomSet n) :
    cardOn xs (fun x => S (recolor (x, false))) +
      cardOn xs (fun x => S (recolor (x, true))) =
    cardOn xs (fun x => S (x, false)) + cardOn xs (fun x => S (x, true)) := by
  classical
  induction xs with
  | nil => simp [cardOn]
  | cons a xs ih =>
      simp only [cardOn_cons]
      simp only [recolor, Bool.false_xor, Bool.true_xor] at ih
      cases h : columnParity a <;> by_cases hf : S (a, false) <;> by_cases ht : S (a, true)
      all_goals simp only [recolor, h, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, hf, ht, ↓reduceIte]
      all_goals omega

/-- The coordinate isomorphism preserves the actual number of inspected rooms. -/
theorem recolor_roomCard {n : Nat} (S : RoomSet n) :
    roomCard (fun x => S (recolor x)) = roomCard S := by
  exact recolor_card_on (List.finRange n) S

end Princess.LadderCardinality

#print axioms Princess.LadderCardinality.path_boundary
#print axioms Princess.LadderCardinality.close_expands
#print axioms Princess.LadderCardinality.column_count_lower
#print axioms Princess.LadderCardinality.suffix_step
#print axioms Princess.LadderCardinality.recolor_roomCard
