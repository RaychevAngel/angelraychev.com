import IrregularTenProfile

namespace Delivery.IrregularFiveSevenProfile
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport
open IrregularTenProfile (degree_rigidity card_pullback)

/-- Above two guarantees, the two active sets have size two, are
disjoint, and all degrees are exactly one or two. -/
theorem rigid (E : Graph (Fin 5)) (loopless : Loopless E)
    (budget : arcCount E = 7)
    (positiveOut : ∀ x, 1 ≤ outdegree E x)
    (positiveIn : ∀ x, 1 ≤ indegree E x) (large : 2 < score E) :
    card (ActiveOut E) = 2 ∧ card (ActiveIn E) = 2 ∧
    (∀ x, ¬ (ActiveOut E x ∧ ActiveIn E x)) ∧
    (∀ x, outdegree E x = if ActiveOut E x then 2 else 1) ∧
    (∀ x, indegree E x = if ActiveIn E x then 2 else 1) := by
  have counts := positive_support_counts E positiveOut positiveIn
  have rect := eligible_rectangle E loopless
  have qa : card (ActiveOut E) ≤ 2 := by omega
  have qb : card (ActiveIn E) ≤ 2 := by omega
  have qa' : card (ActiveOut E) = 2 := by
    apply Classical.byContradiction
    intro h
    have small : card (ActiveOut E) ≤ 1 := by omega
    have product := Nat.mul_le_mul small qb
    omega
  have qb' : card (ActiveIn E) = 2 := by
    apply Classical.byContradiction
    intro h
    have small : card (ActiveIn E) ≤ 1 := by omega
    have product := Nat.mul_le_mul qa small
    omega
  have noOverlap : card (fun x => ActiveOut E x ∧ ActiveIn E x) = 0 := by
    rw [qa', qb'] at counts rect
    omega
  have outSum : ((List.finRange 5).map (outdegree E)).sum =
      5 + card (ActiveOut E) := by
    have rows := arc_rows E
    change arcCount E = ((List.finRange 5).map (outdegree E)).sum at rows
    omega
  have inSum : ((List.finRange 5).map (indegree E)).sum =
      5 + card (ActiveIn E) := by
    have cols := arc_columns E
    change arcCount E = ((List.finRange 5).map (indegree E)).sum at cols
    omega
  exact ⟨qa', qb', card_eq_zero.mp noOverlap,
    degree_rigidity (outdegree E) positiveOut outSum,
    degree_rigidity (indegree E) positiveIn inSum⟩

theorem block_enumeration (A B : Fin 5 → Prop)
    (a : card A = 2) (b : card B = 2)
    (disjoint : ∀ x, ¬ (A x ∧ B x)) :
    ∃ f g : Fin 5 → Fin 5,
      (∀ x, g (f x)=x) ∧ (∀ x, f (g x)=x) ∧
      (∀ i, (A (f i) ↔ i.val<2) ∧ (B (f i) ↔ 2≤i.val ∧ i.val<4)) := by
  classical
  let C := fun x => ¬ A x ∧ ¬ B x
  have c : card C = 1 := by
    have union := card_disjoint_union (P:=A) (Q:=B)
      (fun x ha hb => disjoint x ⟨ha,hb⟩)
    have comp := card_complement (fun x => A x ∨ B x)
    have equal : card C = card (fun x => ¬ (A x ∨ B x)) :=
      card_congr (fun x => by simp [C, not_or])
    omega
  let L := elems A ++ (elems B ++ elems C)
  have la : (elems A).length=2 := a
  have lb : (elems B).length=2 := b
  have lc : (elems C).length=1 := c
  have length : L.length=5 := by simp [L,la,lb,lc]
  have nodup : L.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨elems_nodup A,?_,?_⟩
    · apply List.nodup_append.mpr
      refine ⟨elems_nodup B,elems_nodup C,?_⟩
      intro x hx y hy same
      subst y
      exact (mem_elems.mp hy).2 (mem_elems.mp hx)
    · intro x hx y hy same
      subst y
      rcases List.mem_append.mp hy with hb | hc
      · exact disjoint x ⟨mem_elems.mp hx,mem_elems.mp hb⟩
      · exact (mem_elems.mp hc).1 (mem_elems.mp hx)
  have every (x : Fin 5) : x ∈ L := by
    simp only [L,List.mem_append,mem_elems]
    by_cases ha : A x
    · exact Or.inl ha
    · by_cases hb : B x
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr ⟨ha,hb⟩)
  let f : Fin 5 → Fin 5 := fun i => L[i.val]'(by omega)
  let g : Fin 5 → Fin 5 := fun x => ⟨L.idxOf x, by
    have h := List.idxOf_lt_length_iff.mpr (every x); omega⟩
  have right (x : Fin 5) : f (g x)=x := by
    exact List.getElem_idxOf _
  have left (x : Fin 5) : g (f x)=x := by
    apply Fin.ext
    exact (List.getElem_inj nodup).mp (right (f x))
  refine ⟨f,g,left,right,?_⟩
  intro i
  have ilt := i.isLt
  have allLength : (elems A ++ (elems B ++ elems C)).length=5 := length
  by_cases hi : i.val<2
  · have ha : A (f i) := by
      apply mem_elems.mp
      change (elems A ++ (elems B ++ elems C))[i.val] ∈ elems A
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem _
    have hb : ¬ B (f i) := fun hb => disjoint (f i) ⟨ha,hb⟩
    exact ⟨⟨fun _ => hi,fun _ => ha⟩,by simp [hb]; omega⟩
  · by_cases hj : i.val<4
    · have hb : B (f i) := by
        apply mem_elems.mp
        change (elems A ++ (elems B ++ elems C))[i.val] ∈ elems B
        rw [List.getElem_append_right (by omega)]
        rw [List.getElem_append_left (by omega)]
        exact List.getElem_mem _
      have ha : ¬ A (f i) := fun ha => disjoint (f i) ⟨ha,hb⟩
      exact ⟨by simp [ha,hi],⟨fun _ => ⟨by omega,hj⟩,fun _ => hb⟩⟩
    · have hc : C (f i) := by
        apply mem_elems.mp
        change (elems A ++ (elems B ++ elems C))[i.val] ∈ elems C
        rw [List.getElem_append_right (by omega)]
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_mem _
      exact ⟨by simp [hc.1,hi],by simp [hc.2,hj]⟩

/-- Every prospective counterexample relabels into the one fixed 2+2+1
joint-degree profile. The bound for that profile is a separate certificate. -/
theorem normalize (E : Graph (Fin 5)) (loopless : Loopless E)
    (budget : arcCount E = 7)
    (positiveOut : ∀ x, 1 ≤ outdegree E x)
    (positiveIn : ∀ x, 1 ≤ indegree E x) (large : 2 < score E) :
    ∃ F : Graph (Fin 5), Nonempty (GraphRelabeling.Iso E F) ∧ Loopless F ∧
      (∀ i, outdegree F i = if i.val<2 then 2 else 1) ∧
      (∀ i, indegree F i = if 2≤i.val ∧ i.val<4 then 2 else 1) := by
  obtain ⟨a,b,disjoint,outDeg,inDeg⟩ := rigid E loopless budget positiveOut positiveIn large
  obtain ⟨f,g,left,right,blocks⟩ := block_enumeration (ActiveOut E) (ActiveIn E) a b disjoint
  let F : Graph (Fin 5) := fun s t => E (f s) (f t)
  let iso : GraphRelabeling.Iso F E := ⟨f,g,left,right,fun _ _ => Iff.rfl⟩
  refine ⟨F,⟨iso.symm⟩,iso.symm.loopless loopless,?_,?_⟩
  · intro i
    have counted := card_pullback f g left right (E (f i))
    change outdegree F i = outdegree E (f i) at counted
    rw [counted,outDeg]
    simp only [(blocks i).1]
  · intro i
    have counted := card_pullback f g left right (fun s => E s (f i))
    change indegree F i = indegree E (f i) at counted
    rw [counted,inDeg]
    simp only [(blocks i).2]

#print axioms normalize
end Delivery.IrregularFiveSevenProfile
