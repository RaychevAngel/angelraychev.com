import DenseCombinatorics

/-! Counting literal finite construction rows. -/
namespace Delivery.ConstructionCounts
open FiniteGame Extremal DenseCombinatorics

theorem card_image {m n : Nat} (f : Fin m → Fin n) (P : Fin n → Prop)
    (injective : ∀ i j, f i = f j → i = j)
    (image : ∀ s, P s ↔ ∃ i, f i = s) : card P = m := by
  have nd : ((List.finRange m).map f).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange m).imp (fun h same => h (injective _ _ same))
  have perm := (List.perm_ext_iff_of_nodup (elems_nodup P) nd).mpr
    (fun s => by simp only [mem_elems,List.mem_map,List.mem_finRange,true_and]; exact image s)
  simpa only [card,List.length_map,List.length_finRange] using perm.length_eq

theorem score_rows {n : Nat} (E : Graph (Fin n)) :
    score E = ((List.finRange n).map fun s => card (Indirect E s)).sum := by
  classical
  unfold score allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,card_eq]

theorem missing_rows {n : Nat} (E : Graph (Fin n)) :
    missingCount E = ((List.finRange n).map fun s =>
      card (fun t => s ≠ t ∧ ¬ E s t)).sum := by
  classical
  unfold missingCount allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,card_eq]

theorem sum_mono {α : Type} (xs : List α) {f g : α → Nat}
    (pointwise : ∀ x, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; have := pointwise x; omega

theorem weighted_indicators {α : Type} (xs : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (a b : Nat) :
    (xs.map fun x => (if P x then a else 0) + (if Q x then b else 0)).sum =
      a*(xs.filter fun x => decide (P x)).length +
      b*(xs.filter fun x => decide (Q x)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases p : P x <;> by_cases q : Q x <;>
      simp [p,q,ih,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem one_or_two {α : Type} (xs : List α) (Q : α → Prop) [DecidablePred Q] :
    (xs.map fun x => if Q x then 2 else 1).sum =
      xs.length + (xs.filter fun x => decide (Q x)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases q : Q x <;> simp [q,ih] <;> omega

#print axioms card_image
end Delivery.ConstructionCounts
