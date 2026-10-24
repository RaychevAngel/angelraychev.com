import OddEndpointGraph
import DenseTwoType
import GraphRelabeling
import SparseSupport

/-! Explicit finite enumeration and exact arrow counts for the six cyclic
odd-endpoint graphs. No local certificate or game-winning premise is used. -/
namespace Delivery.OddEndpointCounts
open OddEndpointGraph FiniteGame Extremal DenseCombinatorics ConstructionCounts

def encodeRaw {k : Nat} (v : Raw k) : Fin (6*k) :=
  ⟨6*v.1.val+v.2.val,by have := v.1.isLt; have := v.2.isLt; omega⟩
def decodeRaw {k : Nat} (x : Fin (6*k)) : Raw k :=
  (⟨x.val/6,by have := x.isLt; omega⟩,⟨x.val%6,Nat.mod_lt _ (by decide)⟩)

@[simp] theorem decode_encode {k : Nat} (v : Raw k) : decodeRaw (encodeRaw v)=v := by
  apply Prod.ext <;> apply Fin.ext <;> dsimp [decodeRaw,encodeRaw]
  all_goals have := v.2.isLt; omega
@[simp] theorem encode_decode {k : Nat} (x : Fin (6*k)) : encodeRaw (decodeRaw x)=x := by
  apply Fin.ext
  dsimp [encodeRaw,decodeRaw]
  omega

def retained {k : Nat} (hk : 15≤k) (r : Case) (x : Fin (6*k)) : Prop :=
  Present hk r (decodeRaw x)
instance {k : Nat} (hk : 15≤k) (r : Case) (x : Fin (6*k)) : Decidable (retained hk r x) :=
  inferInstanceAs (Decidable (Present _ _ _))
def vertices {k : Nat} (hk : 15≤k) (r : Case) : List (Fin (6*k)) :=
  (List.finRange (6*k)).filter fun x => decide (retained hk r x)

@[simp] theorem mem_vertices {k : Nat} (hk : 15≤k) (r : Case) (x : Fin (6*k)) :
    x∈vertices hk r ↔ retained hk r x := by simp [vertices]
theorem vertices_nodup {k : Nat} (hk : 15≤k) (r : Case) :
    (vertices hk r).Nodup := (List.nodup_finRange _).filter _

theorem removed_count {k : Nat} (hk : 15≤k) (r : Case) :
    card (fun x : Fin (6*k) => ¬retained hk r x)=r.val := by
  classical
  let removed := (OddEndpointStrip.holes r).map (fun v => encodeRaw (project hk v))
  have nd : removed.Nodup := by
    apply List.pairwise_map.mpr
    apply (OddEndpointStrip.holes_nodup r).imp_of_mem
    intro v w hv hw different same
    have bv := OddEndpointStrip.holes_bounds r hv
    have bw := OddEndpointStrip.holes_bounds r hw
    have projected := congrArg decodeRaw same
    simp only [decode_encode] at projected
    exact different (project_injective_of_gap hk (by omega) (by omega) projected)
  have image (x : Fin (6*k)) : ¬retained hk r x ↔ x∈removed := by
    simp only [retained,Present,Classical.not_not,List.mem_map,removed]
    constructor
    · rintro ⟨v,member,same⟩
      exact ⟨v,member,by simpa only [encode_decode] using congrArg encodeRaw same⟩
    · rintro ⟨v,member,same⟩
      exact ⟨v,member,by simpa only [decode_encode] using congrArg decodeRaw same⟩
  have perm := (List.perm_ext_iff_of_nodup
    (elems_nodup (fun x : Fin (6*k) => ¬retained hk r x)) nd).mpr
    (fun x => by simpa only [mem_elems] using image x)
  change (elems (fun x : Fin (6*k) => ¬retained hk r x)).length=r.val
  rw [perm.length_eq,List.length_map,OddEndpointStrip.holes_length]

theorem vertices_length {k : Nat} (hk : 15≤k) (r : Case) :
    (vertices hk r).length=6*k-r.val := by
  classical
  have split := SparseSupport.card_complement (retained hk r)
  rw [removed_count hk r,card_eq] at split
  change (vertices hk r).length+r.val=6*k at split
  omega

def toVertex {k : Nat} {hk : 15≤k} {r : Case}
    (i : Fin (vertices hk r).length) : Vertex hk r :=
  ⟨decodeRaw ((vertices hk r)[i.val]),(mem_vertices hk r _).mp (List.getElem_mem i.isLt)⟩

def fromVertex {k : Nat} {hk : 15≤k} {r : Case}
    (v : Vertex hk r) : Fin (vertices hk r).length :=
  ⟨(vertices hk r).idxOf (encodeRaw v.val),List.idxOf_lt_length_of_mem
    ((mem_vertices hk r _).mpr (by simpa only [retained,decode_encode] using v.property))⟩

theorem to_injective {k : Nat} {hk : 15≤k} {r : Case}
    {i j : Fin (vertices hk r).length} (same : toVertex i=toVertex j) : i=j := by
  have h := congrArg (fun v : Vertex hk r => encodeRaw v.val) same
  simp only [toVertex,encode_decode] at h
  apply Fin.ext
  exact (List.getElem_inj (vertices_nodup hk r)).mp h

@[simp] theorem to_from {k : Nat} {hk : 15≤k} {r : Case} (v : Vertex hk r) :
    toVertex (fromVertex v)=v := by
  apply Subtype.ext
  simp only [toVertex,fromVertex,List.getElem_idxOf,decode_encode]
@[simp] theorem from_to {k : Nat} {hk : 15≤k} {r : Case}
    (i : Fin (vertices hk r).length) : fromVertex (toVertex i)=i :=
  to_injective (to_from (toVertex i))

def graph {k : Nat} (hk : 15≤k) (r : Case) : Graph (Fin (vertices hk r).length) :=
  fun s t => edge hk r (toVertex s) (toVertex t)

def graphIso {k : Nat} (hk : 15≤k) (r : Case) :
    GraphRelabeling.Iso (graph hk r) (edge hk r) where
  toFun := toVertex
  invFun := fromVertex
  left_inv := from_to
  right_inv := to_from
  edge_iff _ _ := Iff.rfl

def source {k : Nat} (hk : 15≤k) (r : Case) : Fin (vertices hk r).length :=
  fromVertex (lowSource hk r)
def target {k : Nat} (hk : 15≤k) (r : Case) : Fin (vertices hk r).length :=
  fromVertex (lowTarget hk r)

theorem graph_loopless {k : Nat} (hk : 15≤k) (r : Case) : Loopless (graph hk r) := by
  intro s hit
  exact OddEndpointGraph.loopless hk r (toVertex s) hit

theorem ordinary_row {k : Nat} (hk : 15≤k) (r : Case)
    (s t : Fin (vertices hk r).length) (ordinary : s≠source hk r) :
    graph hk r s t ↔ t=fromVertex (move hk r false (toVertex s)) ∨
      t=fromVertex (move hk r true (toVertex s)) := by
  have ordinary' : toVertex s≠lowSource hk r := by
    intro same
    exact ordinary (by simpa only [from_to,source] using congrArg fromVertex same)
  rw [graph,OddEndpointGraph.ordinary_row hk r _ _ ordinary']
  constructor
  · rintro (h|h)
    · exact Or.inl (by simpa only [from_to] using congrArg fromVertex h)
    · exact Or.inr (by simpa only [from_to] using congrArg fromVertex h)
  · rintro (h|h)
    · exact Or.inl (by simpa only [to_from] using congrArg toVertex h)
    · exact Or.inr (by simpa only [to_from] using congrArg toVertex h)

theorem source_row {k : Nat} (hk : 15≤k) (r : Case) (t : Fin (vertices hk r).length) :
    graph hk r (source hk r) t ↔
      t=fromVertex (move hk r (!(OddEndpointStrip.deletedChoice r)) (lowSource hk r)) := by
  simp only [graph,source,to_from,OddEndpointGraph.source_row]
  constructor
  · intro h; simpa only [from_to] using congrArg fromVertex h
  · intro h; simpa only [to_from] using congrArg toVertex h

theorem row_count {k : Nat} (hk : 15≤k) (r : Case) (s : Fin (vertices hk r).length) :
    card (graph hk r s)=if s≠source hk r then 2 else 1 := by
  classical
  by_cases ordinary : s≠source hk r
  · rw [if_pos ordinary,card_congr (ordinary_row hk r s · ordinary)]
    apply DenseTwoType.card_two
    intro same
    have raw := congrArg toVertex same
    simp only [to_from] at raw
    exact moves_distinct hk r (toVertex s) raw
  · have same : s=source hk r := Classical.not_not.mp ordinary
    rw [if_neg ordinary,same,card_congr (source_row hk r)]
    exact card_image (fun _ : Fin 1 => fromVertex
      (move hk r (!(OddEndpointStrip.deletedChoice r)) (lowSource hk r))) _
      (by intro i j _; exact Fin.ext (by have := i.isLt; have := j.isLt; omega))
      (by intro t; simp only [exists_const]; exact eq_comm)

theorem graph_arcs {k : Nat} (hk : 15≤k) (r : Case) :
    arcCount (graph hk r)=2*(vertices hk r).length-1 := by
  classical
  rw [SparseSupport.arc_rows]
  simp only [row_count]
  rw [one_or_two]
  have singleton : card (fun s => s=source hk r)=1 :=
    card_image (fun _ : Fin 1 => source hk r) _
      (by intro i j _; exact Fin.ext (by have := i.isLt; have := j.isLt; omega))
      (by intro t; simp only [exists_const]; exact eq_comm)
  have complement := SparseSupport.card_complement (fun s => s=source hk r)
  rw [singleton,card_eq] at complement
  change 1+(List.filter (fun s => decide (s≠source hk r))
    (List.finRange (vertices hk r).length)).length=(vertices hk r).length at complement
  simp only [List.length_finRange]
  omega

theorem graph_incoming {k : Nat} (hk : 15≤k) (r : Case) (s : Fin (vertices hk r).length) :
    graph hk r s (target hk r) ↔ s=fromVertex (predecessor hk r) := by
  simp only [graph,target,to_from,OddEndpointGraph.incoming]
  constructor
  · intro same; simpa only [from_to] using congrArg fromVertex same
  · intro same; simpa only [to_from] using congrArg toVertex same

theorem defect_distinct {k : Nat} (hk : 15≤k) (r : Case) : source hk r≠target hk r := by
  intro same
  have raw := congrArg toVertex same
  simp only [source,target,to_from] at raw
  exact OddEndpointGraph.defect_distinct hk r raw

theorem defect_missing {k : Nat} (hk : 15≤k) (r : Case) :
    ¬graph hk r (source hk r) (target hk r) := by
  simpa only [graph,source,target,to_from] using OddEndpointGraph.defect_missing hk r

#print axioms vertices_length
#print axioms graph_arcs
#print axioms graph_incoming
end Delivery.OddEndpointCounts
