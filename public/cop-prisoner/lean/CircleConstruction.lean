import CircleGuarded
import CircleCounting
import GuaranteedPrefix

/-! Exact circulant counts and literal optional-prefix attainment for the
five-offset families. Counts come from injective cyclic translation. -/
namespace Delivery.CircleConstruction
open FiniteGame Extremal DenseCombinatorics CyclicArithmetic CirclePropagation CircleEnvelope

private theorem card_image_pred {n : Nat} (P : Fin n → Prop) (f : Fin n → Fin n)
    (injective : ∀ x y, f x=f y → x=y) :
    card (fun t => ∃ d, P d ∧ f d=t) = card P := by
  have nodup : ((elems P).map f).Nodup := by
    apply List.pairwise_map.mpr
    exact (elems_nodup P).imp (fun different same => different (injective _ _ same))
  have perm := (List.perm_ext_iff_of_nodup
    (elems_nodup (fun t => ∃ d, P d ∧ f d=t)) nodup).mpr (fun t => by
      simp only [mem_elems,List.mem_map])
  simpa only [card,List.length_map] using perm.length_eq

private theorem shift_offsets_injective {n : Nat} (s : Fin n) (a b : Fin n)
    (same : shift s a.val=shift s b.val) : a=b := by
  apply Fin.ext
  have equal := (shift_eq_iff s _ _).mp same
  simpa only [Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt b.isLt] using equal

theorem arc_rows {n : Nat} (E : Graph (Fin n)) :
    arcCount E = ((List.finRange n).map fun s => card (E s)).sum := by
  classical
  rw [arcCount_eq]
  unfold allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,card_eq]

private theorem constant_sum {n v : Nat} (xs : List (Fin n)) :
    (xs.map fun _ => v).sum = xs.length*v := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem compulsory_count {n h : Nat} (hh : 7 ≤ h) (room : h+2<n) :
    card (fun d : Fin n => Compulsory h d.val) = 5 := by
  let ds : List (Fin n) := [⟨1,by omega⟩,⟨h-3,by omega⟩,⟨h-2,by omega⟩,
    ⟨h,by omega⟩,⟨h+2,by omega⟩]
  have nodup : ds.Nodup := by
    simp [ds,Fin.ext_iff]
    omega
  have perm := (List.perm_ext_iff_of_nodup
    (elems_nodup (fun d : Fin n => Compulsory h d.val)) nodup).mpr (fun d => by
      simp only [mem_elems,Compulsory,ds,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff])
  exact perm.length_eq

theorem base_arcCount {n h : Nat} (hh : 7 ≤ h) (room : h+2<n) :
    arcCount (Base (n := n) h) = 5*n := by
  have row (s : Fin n) : card (Base h s) = 5 := by
    have shape (t : Fin n) : Base h s t ↔
        ∃ d : Fin n, Compulsory h d.val ∧ shift s d.val=t := by
      constructor
      · rintro ⟨d,member,same⟩
        have small : d<n := by rcases member with rfl | rfl | rfl | rfl | rfl <;> omega
        exact ⟨⟨d,small⟩,member,same.symm⟩
      · rintro ⟨d,member,same⟩
        exact ⟨d.val,member,same.symm⟩
    rw [card_congr shape,card_image_pred _ _ (shift_offsets_injective s),compulsory_count hh room]
  rw [arc_rows]
  simp only [row]
  simpa only [List.length_finRange,Nat.mul_comm] using constant_sum (v := 5) (List.finRange n)

theorem envelope_arcCount {n : Nat} (A : Nat → Prop) (bounded : ∀ d, A d → d<n)
    (zero : A 0) : arcCount (Envelope (n := n) A) = n*(card (fun d : Fin n => A d.val)-1) := by
  have positive : 0<n := bounded 0 zero
  have one : card (fun d : Fin n => A d.val ∧ d.val=0)=1 := by
    rw [card_congr (Q := fun d : Fin n => d.val=0)]
    · exact CircleCounting.singleton_count positive
    · intro d
      exact ⟨And.right,fun h => ⟨h ▸ zero,h⟩⟩
  have partition := card_partition (fun d : Fin n => A d.val) (fun d => d.val=0)
  rw [one] at partition
  change 1 + card (fun d : Fin n => A d.val ∧ d.val≠0) = card (fun d : Fin n => A d.val) at partition
  have nonzero : card (fun d : Fin n => A d.val ∧ d.val≠0) = card (fun d : Fin n => A d.val)-1 := by omega
  have row (s : Fin n) : card (Envelope A s) = card (fun d : Fin n => A d.val)-1 := by
    have shape (t : Fin n) : Envelope A s t ↔
        ∃ d : Fin n, (A d.val ∧ d.val≠0) ∧ shift s d.val=t := by
      constructor
      · rintro ⟨different,d,inside,same⟩
        refine ⟨⟨d,bounded d inside⟩,⟨inside,?_⟩,same.symm⟩
        intro zeroD
        change d=0 at zeroD
        rw [zeroD,shift_zero] at same
        exact different same.symm
      · rintro ⟨d,inside,same⟩
        refine ⟨?_,d.val,inside.1,same.symm⟩
        intro equal
        exact shift_ne_self s (by have := inside.2; omega) d.isLt (same.trans equal.symm)
    rw [card_congr shape,card_image_pred _ _ (shift_offsets_injective s),nonzero]
  rw [arc_rows]
  simp only [row]
  simpa only [List.length_finRange] using constant_sum
    (v := card (fun d : Fin n => A d.val)-1) (List.finRange n)

theorem full_arcCount {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2≤n) (four : n%4=0) :
    arcCount (Envelope (n := n) (CircleEnvelope.Allowed n h)) = n*(n/2-1) := by
  rw [envelope_arcCount _ (fun _ h => h.1) (CircleEnvelope.zero_allowed hh room)]
  have count := CircleCounting.allowed_count four hh residue room
  have equal := card_congr (P := fun d : Fin n => CircleEnvelope.Allowed n h d.val)
    (Q := CircleCounting.allowed h) (fun d => by
      simp only [CircleEnvelope.Allowed,CircleCounting.allowed,CircleCounting.periodic,d.isLt,true_and,or_assoc])
  rw [equal,count]

/-- The full modulo-four family realizes every budget in its exact interval. -/
theorem full_maximum {n h m : Nat} (hh : 7≤h) (residue : h%4=3)
    (room : 2*h+2≤n) (four : n%4=0) (coprime : Nat.Coprime n h)
    (low : 5*n≤m) (high : m≤n*(n/2-1)) : IsMaximum n m (n*(n-1)-m) := by
  apply GuaranteedPrefix.maximum (Base h) (Envelope (CircleEnvelope.Allowed n h))
    (CircleEnvelope.base_subset hh residue room) (fun _ e => e.1 rfl) ?_ ?_ ?_
  · intro G lower upper s t
    exact universal_guaranteed (CircleEnvelope.universal hh residue room four coprime lower upper t s)
  · rw [base_arcCount hh (by omega)]; exact low
  · rw [full_arcCount hh residue room four]; exact high

/-- The guarded family has the same literal prefix recipe, with its exact
finite arithmetic count as the endpoint. No game premise is left exposed. -/
theorem guarded_maximum {n h m : Nat} (hh : 7≤h) (residue : h%4=3)
    (room : 2*h+2≤n) (coprime : Nat.Coprime n h)
    (low : 5*n≤m)
    (high : m≤n*(card (fun d : Fin n => CircleGuarded.Allowed n h d.val)-1)) :
    IsMaximum n m (n*(n-1)-m) := by
  apply GuaranteedPrefix.maximum (Base h) (Envelope (CircleGuarded.Allowed n h))
    (CircleGuarded.base_subset hh residue room) (fun _ e => e.1 rfl) ?_ ?_ ?_
  · intro G lower upper s t
    exact universal_guaranteed (CircleGuarded.universal hh residue room coprime lower upper t s)
  · rw [base_arcCount hh (by omega)]; exact low
  · rw [envelope_arcCount _ (fun _ h => h.1.1) (CircleGuarded.zero_allowed hh room)]
    exact high

#print axioms base_arcCount
#print axioms full_maximum
#print axioms guarded_maximum
end Delivery.CircleConstruction
