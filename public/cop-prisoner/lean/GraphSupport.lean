import DegreeProfileRelabeling
import GraphRestriction
import SparseDeletion
import GraphPadding

/-! Removal and enumeration of isolated vertices for upper-bound reductions. -/
namespace Delivery.GraphSupport
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport

def Support {n : Nat} (E : Graph (Fin n)) (x : Fin n) : Prop :=
  (∃ y, E x y) ∨ ∃ y, E y x

noncomputable def embed {n : Nat} (P : Fin n → Prop) (i : Fin (card P)) : Fin n :=
  (elems P)[i.val]'(i.isLt)

theorem embed_mem {n : Nat} (P : Fin n → Prop) (i : Fin (card P)) : P (embed P i) :=
  mem_elems.mp (List.getElem_mem _)

theorem embed_injective {n : Nat} (P : Fin n → Prop) {i j : Fin (card P)}
    (same : embed P i=embed P j) : i=j := by
  apply Fin.ext
  exact (List.getElem_inj (elems_nodup P)).mp same

noncomputable def index {n : Nat} (P : Fin n → Prop) (x : Fin n) (inside : P x) : Fin (card P) :=
  ⟨(elems P).idxOf x,List.idxOf_lt_length_of_mem (mem_elems.mpr inside)⟩

theorem embed_index {n : Nat} (P : Fin n → Prop) (x : Fin n) (inside : P x) :
    embed P (index P x inside)=x := List.getElem_idxOf _

theorem index_embed {n : Nat} (P : Fin n → Prop) (x : Fin (card P)) :
    index P (embed P x) (embed_mem P x)=x := by
  apply embed_injective P
  exact embed_index P _ _

noncomputable def graph {n : Nat} (E : Graph (Fin n)) : Graph (Fin (card (Support E))) :=
  fun s t => E (embed (Support E) s) (embed (Support E) t)

noncomputable def iso {n : Nat} (E : Graph (Fin n)) :
    GraphRelabeling.Iso (graph E) (GraphRestriction.induced E (Support E)) where
  toFun := fun i => ⟨embed (Support E) i,embed_mem _ i⟩
  invFun := fun x => index (Support E) x.val x.property
  left_inv := index_embed _
  right_inv := fun x => Subtype.ext (embed_index _ _ _)
  edge_iff := fun _ _ => Iff.rfl

theorem loopless {n : Nat} (E : Graph (Fin n)) (loops : Loopless E) : Loopless (graph E) :=
  fun s edge => loops _ edge

theorem card_pullback {n : Nat} (P Q : Fin n → Prop) (subset : ∀x,Q x→P x) :
    card (fun i : Fin (card P) => Q (embed P i))=card Q := by
  apply Nat.le_antisymm
  · exact card_injection (embed P) (fun _ h => h) (fun _ _ _ _ h => embed_injective P h)
  · classical
    -- Use a list bijection; no arbitrary value is needed when the support is empty.
    by_cases empty : card P=0
    · have zero : card Q=0 := card_eq_zero.mpr (fun x hx => (card_eq_zero.mp empty) x (subset x hx))
      omega
    · let f : Fin n → Fin (card P) := fun x => if h : Q x then index P x (subset x h) else ⟨0,by omega⟩
      apply card_injection f
      · intro x hx
        simpa [f,hx,embed_index] using hx
      · intro x y hx hy same
        have eq := congrArg (embed P) same
        simpa [f,hx,hy,embed_index] using eq

 theorem outdegree_eq {n : Nat} (E : Graph (Fin n)) (s : Fin (card (Support E))) :
    outdegree (graph E) s=outdegree E (embed (Support E) s) :=
  card_pullback (Support E) (E (embed (Support E) s)) (fun t edge => Or.inr ⟨_,edge⟩)

 theorem indegree_eq {n : Nat} (E : Graph (Fin n)) (t : Fin (card (Support E))) :
    indegree (graph E) t=indegree E (embed (Support E) t) :=
  card_pullback (Support E) (fun s => E s (embed (Support E) t)) (fun s edge => Or.inl ⟨_,edge⟩)

noncomputable def pairMap {n : Nat} (E : Graph (Fin n))
    (p : Fin (card (Support E)) × Fin (card (Support E))) : Fin n × Fin n :=
  (embed (Support E) p.1,embed (Support E) p.2)

theorem pair_injective {n : Nat} (E : Graph (Fin n)) {p q}
    (same : pairMap E p=pairMap E q) : p=q :=
  Prod.ext (embed_injective _ (congrArg Prod.fst same))
    (embed_injective _ (congrArg Prod.snd same))

theorem arcCount_eq {n : Nat} (E : Graph (Fin n)) : arcCount (graph E)=arcCount E := by
  classical
  let L := (allPairs (card (Support E))).filter fun st => decide (graph E st.1 st.2)
  let K := (allPairs n).filter fun st => decide (E st.1 st.2)
  have nodup : (L.map (pairMap E)).Nodup := by
    apply List.pairwise_map.mpr
    exact ((DenseZero.allPairs_nodup _).filter _).imp (fun different same => different (pair_injective E same))
  have perm : (L.map (pairMap E)).Perm K := by
    apply (List.perm_ext_iff_of_nodup nodup ((DenseZero.allPairs_nodup n).filter _)).mpr
    intro p
    simp only [L,K,List.mem_map,List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq]
    constructor
    · rintro ⟨q,edge,rfl⟩; exact edge
    · intro edge
      have hs : Support E p.1 := Or.inl ⟨p.2,edge⟩
      have ht : Support E p.2 := Or.inr ⟨p.1,edge⟩
      refine ⟨(index (Support E) p.1 hs,index (Support E) p.2 ht),?_,?_⟩
      · change E (embed (Support E) (index (Support E) p.1 hs)) (embed (Support E) (index (Support E) p.2 ht))
        rw [embed_index,embed_index]
        exact edge
      · exact Prod.ext (embed_index (Support E) p.1 hs) (embed_index (Support E) p.2 ht)
  rw [Extremal.arcCount_eq,Extremal.arcCount_eq]
  simpa only [List.length_map] using perm.length_eq

theorem indirect_support {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    {s t} (pair : Indirect E s t) : Support E s ∧ Support E t := by
  have out := live_outdegree loops pair
  have inc := live_indegree pair
  exact ⟨Or.inl (card_positive.mp (show 0<outdegree E s by omega)),Or.inr (card_positive.mp (show 0<indegree E t by omega))⟩

theorem indirect_index {n : Nat} (E : Graph (Fin n)) {s t}
    (hs : Support E s) (ht : Support E t) (pair : Indirect E s t) :
    Indirect (graph E) (index (Support E) s hs) (index (Support E) t ht) := by
  have small := GraphRestriction.indirect_forward (E:=E) (P:=Support E)
    (fun _ _ _ edge => Or.inr ⟨_,edge⟩) ⟨s,hs⟩ ⟨t,ht⟩ pair
  exact ((iso E).symm.indirect_iff _ _).mp small

theorem score_le {n : Nat} (E : Graph (Fin n)) (loops : Loopless E) : score E≤score (graph E) := by
  classical
  let L := (allPairs (card (Support E))).filter fun st => decide (Indirect (graph E) st.1 st.2)
  let K := (allPairs n).filter fun st => decide (Indirect E st.1 st.2)
  have subset : K⊆L.map (pairMap E) := by
    intro p hp
    have pair : Indirect E p.1 p.2 := of_decide_eq_true (List.mem_filter.mp hp).2
    obtain ⟨hs,ht⟩ := indirect_support E loops pair
    apply List.mem_map.mpr
    refine ⟨(index (Support E) p.1 hs,index (Support E) p.2 ht),?_,?_⟩
    · exact List.mem_filter.mpr ⟨GraphRelabeling.allPairs_mem _,decide_eq_true (indirect_index E hs ht pair)⟩
    · simp [pairMap,embed_index]
  have nd : K.Nodup := (DenseZero.allPairs_nodup n).filter _
  have bound := nd.length_le_of_subset subset
  change K.length≤L.length
  simpa only [List.length_map] using bound

theorem order_le_arcs {n : Nat} (E : Graph (Fin n))
    (degree : ∀x,Support E x→2≤outdegree E x+indegree E x) :
    card (Support E)≤arcCount E := by
  classical
  have bound := sum_mono (List.finRange n)
    (f:=fun x => if Support E x then 2 else 0)
    (g:=fun x => outdegree E x+indegree E x) (by
      intro x; split
      · exact degree x ‹_›
      · omega)
  rw [indicator_sum,GraphPadding.sum_add] at bound
  have rows : arcCount E=((List.finRange n).map (outdegree E)).sum := arc_rows E
  have cols : arcCount E=((List.finRange n).map (indegree E)).sum := arc_columns E
  omega

#print axioms arcCount_eq
#print axioms score_le
#print axioms order_le_arcs
end Delivery.GraphSupport
