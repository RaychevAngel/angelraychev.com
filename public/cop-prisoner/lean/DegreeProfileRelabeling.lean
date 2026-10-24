import IrregularTenProfile

/-! A bijection between finite labelled sets with the same fibre sizes.
This supplies graph relabelings from degree histograms without enumerating
permutations or assuming a canonical representative exists. -/
namespace Delivery.DegreeProfileRelabeling
open DenseCombinatorics

theorem index_get {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (i : Fin xs.length) :
    xs.idxOf xs[i.val] = i.val := by
  have bound := List.idxOf_lt_length_of_mem (List.getElem_mem i.isLt)
  exact (List.getElem_inj nodup).mp (List.getElem_idxOf bound)

noncomputable def transfer {n : Nat} {α : Type} (a b : Fin n → α)
    (counts : ∀ label, card (fun x => a x=label)=card (fun x => b x=label))
    (x : Fin n) : Fin n :=
  (elems (fun y => a y=b x))[(elems (fun y => b y=b x)).idxOf x]'(by
    have member : x ∈ elems (fun y => b y=b x) := mem_elems.mpr rfl
    have bound := List.idxOf_lt_length_of_mem member
    have equal := counts (b x)
    change (elems (fun y => a y=b x)).length=(elems (fun y => b y=b x)).length at equal
    omega)

theorem transfer_label {n : Nat} {α : Type} (a b : Fin n → α)
    (counts : ∀ label, card (fun x => a x=label)=card (fun x => b x=label))
    (x : Fin n) : a (transfer a b counts x)=b x := by
  unfold transfer
  exact (mem_elems (P:=fun y => a y=b x)).mp (List.getElem_mem _)

theorem transfer_inverse {n : Nat} {α : Type} (a b : Fin n → α)
    (counts : ∀ label, card (fun x => a x=label)=card (fun x => b x=label))
    (x : Fin n) :
    transfer b a (fun label => (counts label).symm) (transfer a b counts x)=x := by
  generalize hv : transfer a b counts x = v
  have label : a v=b x := by rw [←hv]; exact transfer_label a b counts x
  unfold transfer
  simp only [label]
  have index : (elems (fun y => a y=b x)).idxOf v=
      (elems (fun y => b y=b x)).idxOf x := by
    rw [←hv]
    unfold transfer
    exact index_get (elems (fun y => a y=b x)) (elems_nodup _)
      ⟨(elems (fun y => b y=b x)).idxOf x,by
        have member : x ∈ elems (fun y => b y=b x) := mem_elems.mpr rfl
        have bound := List.idxOf_lt_length_of_mem member
        have equal := counts (b x)
        change (elems (fun y => a y=b x)).length=(elems (fun y => b y=b x)).length at equal
        omega⟩
  simp only [index]
  exact List.getElem_idxOf _

theorem labelled_bijection {n : Nat} {α : Type} (a b : Fin n → α)
    (counts : ∀ label, card (fun x => a x=label)=card (fun x => b x=label)) :
    ∃ f g : Fin n → Fin n,
      (∀ x, g (f x)=x) ∧ (∀ x, f (g x)=x) ∧ (∀ x, a (f x)=b x) := by
  exact ⟨transfer a b counts,transfer b a (fun l => (counts l).symm),
    transfer_inverse a b counts,transfer_inverse b a (fun l => (counts l).symm),
    transfer_label a b counts⟩

#print axioms labelled_bijection
end Delivery.DegreeProfileRelabeling
