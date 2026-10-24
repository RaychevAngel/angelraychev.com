import VertexBound
import ConstructionCounts
import SparseSupport

/-! Equality rigidity for the unrestricted vertex bound. Counts refer to the
actual `Indirect` game predicate; no degree premise is hidden in the bound. -/
namespace Delivery.VertexEquality
open FiniteGame Extremal DenseCombinatorics ConstructionCounts

theorem sum_const {α : Type} (xs : List α) (b : Nat) :
    (xs.map fun _ => b).sum = xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem sum_bounded {α : Type} (xs : List α) (f : α → Nat) (b : Nat)
    (bounds : ∀ x, x ∈ xs → f x ≤ b) :
    (xs.map f).sum ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have h := bounds x (by simp)
      have tail := ih (fun y hy => bounds y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem sum_at_max {α : Type} (xs : List α) (f : α → Nat) (b : Nat)
    (bounds : ∀ x, x ∈ xs → f x ≤ b)
    (total : (xs.map f).sum = xs.length * b) :
    ∀ x, x ∈ xs → f x = b := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      have hy := bounds y (by simp)
      have tailbound : (ys.map f).sum ≤ ys.length * b := by
        exact sum_bounded ys f b (fun x hx => bounds x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at total
      have equal : f y = b := by omega
      have tailsum : (ys.map f).sum = ys.length * b := by omega
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact equal
      · exact ih (fun z hz => bounds z (by simp [hz])) tailsum x hx

theorem sum_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem double_sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
    (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil]; rw [sum_const]; simp
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [sum_add,ih]

theorem card_indicators {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    card P = ((List.finRange n).map fun x => if P x then 1 else 0).sum := by
  rw [card_eq]
  generalize List.finRange n = xs
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases h : P x <;> simp [h,ih] <;> omega

theorem score_columns {n : Nat} (E : Graph (Fin n)) :
    score E = ((List.finRange n).map fun t => card (fun s => Indirect E s t)).sum := by
  classical
  rw [score_rows]
  simp only [card_indicators]
  exact double_sum_swap _ _ _

theorem rows_at_equality {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (equality : score E = n * (n-3)) :
    ∀ s, card (Indirect E s) = n-3 := by
  intro s
  apply sum_at_max (List.finRange n) (fun s => card (Indirect E s)) (n-3) ?_ ?_ s
    (List.mem_finRange s)
  · intro s _
    classical
    simpa only [card_eq,VertexBound.rowScore] using VertexBound.row_bound E loopless s
  · simpa only [List.length_finRange,←score_rows] using equality

theorem column_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (t : Fin n) : card (fun s => Indirect E s t) ≤ n-3 := by
  classical
  by_cases live : ∃ s, Indirect E s t
  · obtain ⟨s,hs⟩ := live
    obtain ⟨a,b,ea,eb,different⟩ := SparseSupport.live_recipient_two_predecessors hs
    have ta : t ≠ a := by intro h; subst a; exact loopless t ea
    have tb : t ≠ b := by intro h; subst b; exact loopless t eb
    rw [card_eq]
    apply VertexBound.three_excluded (fun s => decide (Indirect E s t)) t a b
      ta tb different
    · simp [Indirect]
    · simp [Indirect,ea]
    · simp [Indirect,eb]
  · have zero : card (fun s => Indirect E s t) = 0 :=
      card_eq_zero.mpr (fun s hs => live ⟨s,hs⟩)
    omega

theorem columns_at_equality {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (equality : score E = n * (n-3)) :
    ∀ t, card (fun s => Indirect E s t) = n-3 := by
  intro t
  apply sum_at_max (List.finRange n) (fun t => card (fun s => Indirect E s t))
    (n-3) ?_ ?_ t (List.mem_finRange t)
  · intro t _; exact column_bound E loopless t
  · simpa only [List.length_finRange,←score_columns] using equality

theorem card_except {n : Nat} (s : Fin n) : card (fun t => t ≠ s) = n-1 := by
  classical
  have one : card (fun t => t = s) = 1 := by
    rw [card_eq]
    simp [List.filter_eq, (List.nodup_finRange n).count]
  have split := card_partition (fun _ : Fin n => True) (fun t => t = s)
  have left : card (fun t => True ∧ t = s) = card (fun t => t = s) :=
    card_congr (fun _ => by simp)
  have right : card (fun t => True ∧ t ≠ s) = card (fun t => t ≠ s) :=
    card_congr (fun _ => by simp)
  rw [left,right,one,card_true] at split
  omega

theorem disjoint_card_cap {n : Nat} (s : Fin n) (P Q : Fin n → Prop)
    (apart : ∀ t, P t → Q t → False)
    (omitP : ¬P s) (omitQ : ¬Q s) : card P + card Q ≤ n-1 := by
  rw [←card_disjoint_union apart]
  calc
    _ ≤ card (fun t => t ≠ s) := card_mono (fun t h same => by
      subst t
      exact h.elim omitP omitQ)
    _ = _ := card_except s

/-- Saturating the vertex bound forces every outgoing and incoming degree to
be exactly two. The assumption `4 ≤ n` ensures every extremal row/column is live. -/
theorem degree_two_of_equality {n : Nat} (hn : 4 ≤ n)
    (E : Graph (Fin n)) (loopless : Loopless E)
    (equality : score E = n * (n-3)) :
    (∀ s, card (E s) = 2) ∧ (∀ t, card (fun s => E s t) = 2) := by
  have rows := rows_at_equality E loopless equality
  have columns := columns_at_equality E loopless equality
  constructor
  · intro s
    have positive : 0 < card (Indirect E s) := by rw [rows s]; omega
    obtain ⟨t,ht⟩ := card_positive.mp positive
    have lower := SparseSupport.live_outdegree loopless ht
    change 2 ≤ card (E s) at lower
    have cap := disjoint_card_cap s (Indirect E s) (E s)
      (fun _ hi he => hi.2.1 he) (fun hi => hi.1 rfl) (loopless s)
    rw [rows s] at cap
    omega
  · intro t
    have positive : 0 < card (fun s => Indirect E s t) := by rw [columns t]; omega
    obtain ⟨s,hs⟩ := card_positive.mp positive
    have lower := SparseSupport.live_indegree hs
    change 2 ≤ card (fun s => E s t) at lower
    have cap := disjoint_card_cap t (fun s => Indirect E s t) (fun s => E s t)
      (fun _ hi he => hi.2.1 he) (fun hi => hi.1 rfl) (loopless t)
    rw [columns t] at cap
    omega

#print axioms column_bound
#print axioms degree_two_of_equality
end Delivery.VertexEquality
