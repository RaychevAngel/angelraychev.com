import DenseCombinatorics

/-! Finite matchings from Hall's condition, using explicit filtered-list
cardinalities. This is the combinatorial normalization layer; graph factorization
and permutation cycle normalization are separate theorem obligations. -/
namespace Delivery.FiniteHall
open DenseCombinatorics

/-- Neighbors in the permitted target set. -/
def Neighborhood {n : Nat} (E : Fin n → Fin n → Prop)
    (A Q : Fin n → Prop) (y : Fin n) : Prop :=
  Q y ∧ ∃ x, A x ∧ E x y

def Hall {n : Nat} (E : Fin n → Fin n → Prop) (P Q : Fin n → Prop) : Prop :=
  ∀ A : Fin n → Prop, (∀ x, A x → P x) → card A ≤ card (Neighborhood E A Q)

/-- The matching function is required to be injective only on its source set. -/
def Matching {n : Nat} (E : Fin n → Fin n → Prop) (P Q : Fin n → Prop) : Prop :=
  ∃ f : Fin n → Fin n,
    (∀ x, P x → Q (f x) ∧ E x (f x)) ∧
    (∀ x y, P x → P y → f x = f y → x = y)

theorem card_singleton {n : Nat} (x : Fin n) : card (fun y => y = x) = 1 := by
  classical
  rw [card_eq]
  simp [List.filter_eq, (List.nodup_finRange n).count]

theorem card_difference {n : Nat} {P A : Fin n → Prop}
    (subset : ∀ x, A x → P x) : card (fun x => P x ∧ ¬ A x) + card A = card P := by
  have partition := card_partition P A
  have intersection : card (fun x => P x ∧ A x) = card A :=
    card_congr (fun x => ⟨And.right,fun h => ⟨subset x h,h⟩⟩)
  omega

theorem neighborhood_target_difference {n : Nat} (E : Fin n → Fin n → Prop)
    (A Q B : Fin n → Prop) :
    card (Neighborhood E A Q) ≤ card (Neighborhood E A (fun y => Q y ∧ ¬ B y)) + card B := by
  have partition := card_partition (Neighborhood E A Q) B
  have inside := card_mono (P := fun y => Neighborhood E A Q y ∧ B y)
    (Q := B) (fun y h => h.2)
  have outside : card (fun y => Neighborhood E A Q y ∧ ¬ B y) =
      card (Neighborhood E A (fun y => Q y ∧ ¬ B y)) := by
    apply card_congr
    intro y
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,
      fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
  omega

/-- Hall's condition restricted to a source subset and all its neighbors. -/
theorem hall_on_subset {n : Nat} {E : Fin n → Fin n → Prop} {P Q A : Fin n → Prop}
    (hall : Hall E P Q) (subset : ∀ x, A x → P x) :
    Hall E A (Neighborhood E A Q) := by
  intro C contained
  have bound := hall C (fun x hx => subset x (contained x hx))
  have same : card (Neighborhood E C Q) = card (Neighborhood E C (Neighborhood E A Q)) := by
    apply card_congr
    intro y
    constructor
    · rintro ⟨hq,x,hx,edge⟩
      exact ⟨⟨hq,x,contained x hx,edge⟩,x,hx,edge⟩
    · exact fun h => ⟨h.1.1,h.2⟩
  omega

/-- A tight source set can be removed together with precisely its neighbors. -/
theorem hall_after_tight {n : Nat} {E : Fin n → Fin n → Prop} {P Q A : Fin n → Prop}
    (hall : Hall E P Q) (subset : ∀ x, A x → P x)
    (tight : card (Neighborhood E A Q) = card A) :
    Hall E (fun x => P x ∧ ¬ A x) (fun y => Q y ∧ ¬ Neighborhood E A Q y) := by
  intro C contained
  have bound := hall (fun x => A x ∨ C x) (fun x h =>
    h.elim (subset x) (fun hc => (contained x hc).1))
  have sources := card_disjoint_union (P := A) (Q := C)
    (fun x ha hc => (contained x hc).2 ha)
  have targets := card_disjoint_union (P := Neighborhood E A Q)
    (Q := Neighborhood E C (fun y => Q y ∧ ¬ Neighborhood E A Q y))
    (fun y ha hc => hc.1.2 ha)
  have same : card (Neighborhood E (fun x => A x ∨ C x) Q) =
      card (fun y => Neighborhood E A Q y ∨
        Neighborhood E C (fun y => Q y ∧ ¬ Neighborhood E A Q y) y) := by
    apply card_congr
    intro y
    constructor
    · rintro ⟨hq,x,ha | hc,edge⟩
      · exact Or.inl ⟨hq,x,ha,edge⟩
      · by_cases inside : Neighborhood E A Q y
        · exact Or.inl inside
        · exact Or.inr ⟨⟨hq,inside⟩,x,hc,edge⟩
    · rintro (⟨hq,x,ha,edge⟩ | ⟨⟨hq,_⟩,x,hc,edge⟩)
      · exact ⟨hq,x,Or.inl ha,edge⟩
      · exact ⟨hq,x,Or.inr hc,edge⟩
  omega

/-- Strict Hall slack on every proper nonempty subset permits deleting one
source and any one target. -/
theorem hall_after_one {n : Nat} {E : Fin n → Fin n → Prop} {P Q : Fin n → Prop}
    (x y : Fin n) (hx : P x)
    (strict : ∀ C : Fin n → Prop, (∀ z, C z → P z) →
      0 < card C → card C < card P → card C < card (Neighborhood E C Q)) :
    Hall E (fun z => P z ∧ z ≠ x) (fun z => Q z ∧ z ≠ y) := by
  intro C contained
  by_cases empty : card C = 0
  · omega
  · have sourceCount := card_difference (P := P) (A := fun z => z = x)
      (fun z hz => hz ▸ hx)
    rw [card_singleton] at sourceCount
    change card (fun z => P z ∧ z ≠ x) + 1 = card P at sourceCount
    have subsetCount := card_mono (P := C) (Q := fun z => P z ∧ z ≠ x) contained
    have slack := strict C (fun z hz => (contained z hz).1) (by omega) (by omega)
    have removed := neighborhood_target_difference E C Q (fun z => z = y)
    rw [card_singleton] at removed
    change card (Neighborhood E C Q) ≤
      card (Neighborhood E C (fun z => Q z ∧ z ≠ y)) + 1 at removed
    omega

/-- Matchings on two disjoint source pieces combine when their targets
lie in disjoint target pieces. -/
theorem matching_join {n : Nat} {E : Fin n → Fin n → Prop} {P Q A B : Fin n → Prop}
    (targetSubset : ∀ y, B y → Q y) (left : Matching E A B)
    (right : Matching E (fun x => P x ∧ ¬ A x) (fun y => Q y ∧ ¬ B y)) :
    Matching E P Q := by
  classical
  obtain ⟨f,ftarget,finj⟩ := left
  obtain ⟨g,gtarget,ginj⟩ := right
  let h (x : Fin n) := if A x then f x else g x
  refine ⟨h,?_,?_⟩
  · intro x hx
    by_cases inside : A x
    · have hf := ftarget x inside
      exact ⟨by simpa [h,inside] using targetSubset (f x) hf.1,
        by simpa [h,inside] using hf.2⟩
    · have hg := gtarget x ⟨hx,inside⟩
      exact ⟨by simpa [h,inside] using hg.1.1,
        by simpa [h,inside] using hg.2⟩
  · intro x y hx hy same
    by_cases ax : A x <;> by_cases ay : A y
    · apply finj x y ax ay
      simpa [h,ax,ay] using same
    · have fg : f x = g y := by simpa [h,ax,ay] using same
      exact False.elim ((gtarget y ⟨hy,ay⟩).1.2 (fg ▸ (ftarget x ax).1))
    · have gf : g x = f y := by simpa [h,ax,ay] using same
      exact False.elim ((gtarget x ⟨hx,ax⟩).1.2 (gf.symm ▸ (ftarget y ay).1))
    · apply ginj x y ⟨hx,ax⟩ ⟨hy,ay⟩
      simpa [h,ax,ay] using same

/-- Finite Hall marriage theorem, proved on actual predicate cardinalities. -/
theorem exists_matching {n : Nat} (E : Fin n → Fin n → Prop) (P Q : Fin n → Prop)
    (hall : Hall E P Q) : Matching E P Q := by
  classical
  have main : ∀ m : Nat, ∀ P Q : Fin n → Prop, card P = m →
      Hall E P Q → Matching E P Q := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro P Q size hall
      by_cases empty : card P = 0
      · refine ⟨id,?_,?_⟩
        · intro x hx
          exact False.elim (card_eq_zero.mp empty x hx)
        · intro x y hx
          exact False.elim (card_eq_zero.mp empty x hx)
      · by_cases tightExists : ∃ A : Fin n → Prop,
          (∀ x, A x → P x) ∧ 0 < card A ∧ card A < card P ∧
          card (Neighborhood E A Q) = card A
        · obtain ⟨A,subset,positive,proper,tight⟩ := tightExists
          have left := ih (card A) (by omega) A (Neighborhood E A Q) rfl
            (hall_on_subset hall subset)
          have split := card_difference subset
          have right := ih (card (fun x => P x ∧ ¬ A x)) (by omega)
            (fun x => P x ∧ ¬ A x) (fun y => Q y ∧ ¬ Neighborhood E A Q y) rfl
            (hall_after_tight hall subset tight)
          exact matching_join (fun y hy => hy.1) left right
        · obtain ⟨x,hx⟩ := card_positive.mp (show 0 < card P by omega)
          have singleHall := hall (fun z => z = x) (fun z hz => hz ▸ hx)
          rw [card_singleton] at singleHall
          obtain ⟨y,hy,source,sourceEq,edge⟩ := card_positive.mp
            (show 0 < card (Neighborhood E (fun z => z = x) Q) by omega)
          have edgeXY : E x y := sourceEq ▸ edge
          have strict : ∀ C : Fin n → Prop, (∀ z, C z → P z) →
              0 < card C → card C < card P → card C < card (Neighborhood E C Q) := by
            intro C subset positive proper
            have bound := hall C subset
            have notTight : card (Neighborhood E C Q) ≠ card C :=
              fun equal => tightExists ⟨C,subset,positive,proper,equal⟩
            omega
          have split := card_difference (P := P) (A := fun z => z = x)
            (fun z hz => hz ▸ hx)
          rw [card_singleton] at split
          change card (fun z => P z ∧ z ≠ x) + 1 = card P at split
          have right := ih (card (fun z => P z ∧ z ≠ x)) (by omega)
            (fun z => P z ∧ z ≠ x) (fun z => Q z ∧ z ≠ y) rfl
            (hall_after_one x y hx strict)
          have left : Matching E (fun z => z = x) (fun z => z = y) := by
            refine ⟨fun _ => y,?_,?_⟩
            · intro z hz
              exact ⟨rfl,hz ▸ edgeXY⟩
            · intro u v hu hv _
              exact hu.trans hv.symm
          exact matching_join (P := P) (Q := Q)
            (A := fun z => z = x) (B := fun z => z = y) (fun z hz => hz ▸ hy) left right
  exact main (card P) P Q rfl hall

theorem flatMap_length_fixed {α β : Type} (xs : List α) (row : α → List β)
    (d : Nat) (fixed : ∀ x, x ∈ xs → (row x).length = d) :
    (xs.flatMap row).length = xs.length * d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,fixed x (by simp),
      ih (fun y hy => fixed y (by simp [hy])),List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Counting incident pairs proves Hall directly for a two-in/two-out relation. -/
theorem hall_of_two_regular {n : Nat} (E : Fin n → Fin n → Prop)
    (outdegree : ∀ s, card (E s) = 2)
    (indegree : ∀ t, card (fun s => E s t) = 2) :
    Hall E (fun _ => True) (fun _ => True) := by
  intro A _
  let N := Neighborhood E A (fun _ => True)
  let outgoing := (elems A).flatMap fun s => (elems (E s)).map fun t => (s,t)
  let incoming := (elems N).flatMap fun t => (elems (fun s => E s t)).map fun s => (s,t)
  have nd : outgoing.Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro s _
      apply List.pairwise_map.mpr
      exact (elems_nodup (E s)).imp (fun h eq => h (congrArg Prod.snd eq))
    · apply (elems_nodup A).imp
      intro s t different a ha b hb equal
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
      exact different (congrArg Prod.fst equal)
  have subset : outgoing ⊆ incoming := by
    intro p hp
    obtain ⟨s,hs,row⟩ := List.mem_flatMap.mp hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp row
    apply List.mem_flatMap.mpr
    refine ⟨t,mem_elems.mpr ⟨trivial,s,mem_elems.mp hs,mem_elems.mp ht⟩,?_⟩
    exact List.mem_map.mpr ⟨s,mem_elems.mpr (mem_elems.mp ht),rfl⟩
  have outSize : outgoing.length = card A * 2 := by
    apply flatMap_length_fixed
    intro s _
    simpa only [List.length_map,card] using outdegree s
  have inSize : incoming.length = card N * 2 := by
    apply flatMap_length_fixed
    intro t _
    simpa only [List.length_map,card] using indegree t
  have bound := nd.length_le_of_subset subset
  rw [outSize,inSize] at bound
  change card A ≤ card N
  omega

/-- An injective endomap on the explicit finite vertex set is onto. -/
theorem injective_surjective {n : Nat} (f : Fin n → Fin n)
    (injective : ∀ x y, f x = f y → x = y) : ∀ y, ∃ x, f x = y := by
  classical
  intro y
  apply Classical.byContradiction
  intro absent
  have injection := card_injection (P := fun _ => True) (Q := fun z => z ≠ y) f
    (fun x _ same => absent ⟨x,same⟩) (fun x z _ _ same => injective x z same)
  have split := card_partition (fun _ : Fin n => True) (fun z => z = y)
  have sameOne : card (fun z => True ∧ z = y) = 1 := by
    rw [card_congr (P := fun z => True ∧ z = y) (Q := fun z => z = y)
      (fun _ => ⟨And.right,fun h => ⟨trivial,h⟩⟩)]
    exact card_singleton y
  have sameRest : card (fun z => True ∧ ¬ z = y) = card (fun z => z ≠ y) :=
    card_congr (fun _ => ⟨And.right,fun h => ⟨trivial,h⟩⟩)
  rw [card_true] at injection split
  omega

theorem unique_of_card_one {n : Nat} {P : Fin n → Prop} (one : card P = 1) :
    ∃ x, P x ∧ ∀ y, P y → y = x := by
  change (elems P).length = 1 at one
  obtain ⟨x,single⟩ := List.length_eq_one_iff.mp one
  refine ⟨x,?_,?_⟩
  · exact mem_elems.mp (by rw [single]; simp)
  · intro y hy
    have member := mem_elems.mpr hy
    simpa only [single,List.mem_cons,List.not_mem_nil,or_false] using member

theorem no_three_of_card_two {n : Nat} {P : Fin n → Prop}
    (two : card P = 2) {x y z : Fin n} (hx : P x) (hy : P y) (hz : P z)
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) : False := by
  have nd : [x,y,z].Nodup := by simp [xy,xz,yz]
  have subset : [x,y,z] ⊆ elems P := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact mem_elems.mpr (by assumption)
  have bound := nd.length_le_of_subset subset
  change 3 ≤ card P at bound
  omega

/-- Every two-in/two-out finite relation is the union of two disjoint
permutation graphs. Looplessness is not needed for factorization itself. -/
theorem two_permutation_factors {n : Nat} (E : Fin n → Fin n → Prop)
    (outdegree : ∀ s, card (E s) = 2)
    (indegree : ∀ t, card (fun s => E s t) = 2) :
    ∃ a b : Fin n → Fin n,
      (∀ x y, a x = a y → x = y) ∧
      (∀ x y, b x = b y → x = y) ∧
      (∀ s, a s ≠ b s) ∧
      (∀ s t, E s t ↔ t = a s ∨ t = b s) := by
  classical
  obtain ⟨a,target,injective⟩ := exists_matching E (fun _ => True) (fun _ => True)
    (hall_of_two_regular E outdegree indegree)
  have aedge : ∀ s, E s (a s) := fun s => (target s trivial).2
  have ainj : ∀ x y, a x = a y → x = y := fun x y => injective x y trivial trivial
  have onto := injective_surjective a ainj
  have remaining : ∀ s, ∃ t, (E s t ∧ t ≠ a s) ∧
      ∀ u, E s u ∧ u ≠ a s → u = t := by
    intro s
    have split := card_difference (P := E s) (A := fun t => t = a s)
      (fun t ht => ht ▸ aedge s)
    rw [card_singleton,outdegree s] at split
    have one : card (fun t => E s t ∧ t ≠ a s) = 1 := by
      change card (fun t => E s t ∧ t ≠ a s) + 1 = 2 at split
      omega
    exact unique_of_card_one one
  let b (s : Fin n) := Classical.choose (remaining s)
  have bspec (s : Fin n) : (E s (b s) ∧ b s ≠ a s) ∧
      ∀ t, E s t ∧ t ≠ a s → t = b s := Classical.choose_spec (remaining s)
  refine ⟨a,b,ainj,?_,?_,?_⟩
  · intro s t equal
    apply Classical.byContradiction
    intro different
    obtain ⟨r,ar⟩ := onto (b s)
    have rs : s ≠ r := by
      intro same
      exact (bspec s).1.2 (ar.symm.trans (congrArg a same.symm))
    have rt : t ≠ r := by
      intro same
      exact (bspec t).1.2 (equal.symm.trans (ar.symm.trans (congrArg a same.symm)))
    exact no_three_of_card_two (indegree (b s)) (bspec s).1.1
      (equal ▸ (bspec t).1.1) (ar ▸ aedge r) different rs rt
  · intro s
    exact Ne.symm (bspec s).1.2
  · intro s t
    constructor
    · intro edge
      by_cases first : t = a s
      · exact Or.inl first
      · exact Or.inr ((bspec s).2 t ⟨edge,first⟩)
    · rintro (rfl | rfl)
      · exact aedge s
      · exact (bspec s).1.1

/-- In a loopless relation both permutation factors are fixed-point-free. -/
theorem loopless_two_permutation_factors {n : Nat} (E : Fin n → Fin n → Prop)
    (loopless : Extremal.Loopless E)
    (outdegree : ∀ s, card (E s) = 2)
    (indegree : ∀ t, card (fun s => E s t) = 2) :
    ∃ a b : Fin n → Fin n,
      (∀ x y, a x = a y → x = y) ∧
      (∀ x y, b x = b y → x = y) ∧
      (∀ s, a s ≠ s ∧ b s ≠ s ∧ b s ≠ a s) ∧
      (∀ s t, E s t ↔ t = a s ∨ t = b s) := by
  obtain ⟨a,b,ainj,binj,distinct,edges⟩ := two_permutation_factors E outdegree indegree
  refine ⟨a,b,ainj,binj,?_,edges⟩
  intro s
  refine ⟨?_,?_,Ne.symm (distinct s)⟩
  · intro same
    exact loopless s ((edges s s).mpr (Or.inl same.symm))
  · intro same
    exact loopless s ((edges s s).mpr (Or.inr same.symm))

#print axioms exists_matching
#print axioms hall_of_two_regular
#print axioms two_permutation_factors
#print axioms loopless_two_permutation_factors
end Delivery.FiniteHall
