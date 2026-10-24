import SixTypeComposition
import SparseAttainment
import DenseTwoType

namespace Delivery.SixTypeCounts
open SixTypeGraph SixTypeLocal SixTypeComposition FiniteGame Extremal
open DenseCombinatorics ConstructionCounts

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

def retained {k : Nat} (r : Nat) (x : Fin (6*k)) : Prop := Present (holes r) (decodeRaw x)
instance {k : Nat} (r : Nat) (x : Fin (6*k)) : Decidable (retained r x) :=
  inferInstanceAs (Decidable (Present _ _))
def vertices (k r : Nat) : List (Fin (6*k)) :=
  (List.finRange (6*k)).filter fun x => decide (retained r x)

@[simp] theorem mem_vertices {k r : Nat} (x : Fin (6*k)) :
    x∈vertices k r ↔ retained r x := by simp [vertices]
theorem vertices_nodup (k r : Nat) : (vertices k r).Nodup := (List.nodup_finRange _).filter _

def removed {k r : Nat} (hk : 15≤k) (hr : r≤5) (j : Fin r) : Fin (6*k) :=
  ⟨18*j.val+4,by have := j.isLt; omega⟩

theorem removed_image {k r : Nat} (hk : 15≤k) (hr : r≤5) (x : Fin (6*k)) :
    ¬retained r x ↔ ∃ j : Fin r, removed hk hr j=x := by
  constructor
  · intro no
    have typ : (decodeRaw x).2=4 := by
      apply Classical.byContradiction
      intro different
      exact no (Or.inl different)
    have hit : holes r (decodeRaw x).1 := by
      apply Classical.byContradiction
      intro absent
      exact no (Or.inr absent)
    obtain ⟨j,hj,col⟩ := hit
    refine ⟨⟨j.val,hj⟩,?_⟩
    apply Fin.ext
    have tv := congrArg Fin.val typ
    change x.val%6=4 at tv
    change x.val/6=3*j.val at col
    dsimp [removed]
    omega
  · rintro ⟨j,equal⟩ present
    have value := congrArg Fin.val equal
    change 18*j.val+4=x.val at value
    have typ : (decodeRaw x).2=4 := by apply Fin.ext; change x.val%6=4; omega
    have hit : holes r (decodeRaw x).1 := by
      refine ⟨⟨j.val,by have := j.isLt; omega⟩,j.isLt,?_⟩
      change x.val/6=3*j.val
      omega
    exact present.elim (fun h => h typ) (fun h => h hit)

theorem vertices_length {k r : Nat} (hk : 15≤k) (hr : r≤5) :
    (vertices k r).length=6*k-r := by
  classical
  have gone : card (fun x : Fin (6*k) => ¬retained r x)=r :=
    card_image (removed hk hr) _
      (by intro a b equal; apply Fin.ext; have h := congrArg Fin.val equal; dsimp [removed] at h; omega)
      (removed_image hk hr)
  have split := card_partition (fun _ : Fin (6*k) => True) (retained r)
  have keep : card (fun x : Fin (6*k) => True ∧ retained r x)=card (retained r) :=
    card_congr (fun _ => by simp)
  have drop : card (fun x : Fin (6*k) => True ∧ ¬retained r x)=r := by
    rw [card_congr (P:=fun x : Fin (6*k) => True ∧ ¬retained r x)
      (Q:=fun x => ¬retained r x) (fun _ => by simp)]
    exact gone
  rw [keep,drop,card_true,card_eq] at split
  change (vertices k r).length+r=6*k at split
  omega

def toVertex {k r : Nat} (i : Fin (vertices k r).length) : Vertex (holes (k:=k) r) :=
  ⟨decodeRaw ((vertices k r)[i.val]),(mem_vertices _).mp (List.getElem_mem i.isLt)⟩

def fromVertex {k r : Nat} (v : Vertex (holes (k:=k) r)) : Fin (vertices k r).length :=
  ⟨(vertices k r).idxOf (encodeRaw v.val),List.idxOf_lt_length_of_mem
    ((mem_vertices _).mpr (by simpa only [retained,decode_encode] using v.property))⟩

theorem to_injective {k r : Nat} {i j : Fin (vertices k r).length}
    (same : toVertex i=toVertex j) : i=j := by
  have h := congrArg (fun v : Vertex (holes (k:=k) r) => encodeRaw v.val) same
  simp only [toVertex,encode_decode] at h
  apply Fin.ext
  exact (List.getElem_inj (vertices_nodup k r)).mp h

@[simp] theorem to_from {k r : Nat} (v : Vertex (holes (k:=k) r)) :
    toVertex (fromVertex v)=v := by
  apply Subtype.ext
  simp only [toVertex,fromVertex,List.getElem_idxOf,decode_encode]

@[simp] theorem from_to {k r : Nat} (i : Fin (vertices k r).length) :
    fromVertex (toVertex i)=i := to_injective (to_from (toVertex i))

def graph (k r : Nat) : Graph (Fin (vertices k r).length) :=
  fun s t => edge (holes r) (toVertex s) (toVertex t)

def graphIso (k r : Nat) : GraphRelabeling.Iso (graph k r) (edge (holes (k:=k) r)) where
  toFun := toVertex
  invFun := fromVertex
  left_inv := from_to
  right_inv := to_from
  edge_iff _ _ := Iff.rfl

theorem graph_loopless (k r : Nat) : Loopless (graph k r) := by
  intro s edge
  exact SixTypeGraph.loopless (holes r) (toVertex s) edge

theorem row_iff {k r : Nat} (s t : Fin (vertices k r).length) :
    graph k r s t ↔ t=fromVertex (first (holes r) (toVertex s)) ∨
      t=fromVertex (second (holes r) (toVertex s)) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (by simpa only [from_to] using congrArg fromVertex h)
    · exact Or.inr (by simpa only [from_to] using congrArg fromVertex h)
  · rintro (h | h)
    · exact Or.inl (by simpa only [to_from] using congrArg toVertex h)
    · exact Or.inr (by simpa only [to_from] using congrArg toVertex h)

theorem graph_arcs {k r : Nat} (hk : 15≤k) : arcCount (graph k r)=2*(vertices k r).length := by
  have rows (s : Fin (vertices k r).length) : card (graph k r s)=2 := by
    rw [card_congr (row_iff s)]
    apply DenseTwoType.card_two
    intro same
    have raw := congrArg toVertex same
    simp only [to_from] at raw
    exact distinct (by omega) (holes r) (toVertex s) raw
  rw [SparseSupport.arc_rows]
  simp only [rows]
  have sum (xs : List (Fin (vertices k r).length)) :
      (xs.map fun _ => 2).sum=2*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih,Nat.mul_add,Nat.add_comm]
  simpa using sum (List.finRange (vertices k r).length)

theorem graph_guaranteed
    (cert : ∀ p, p∈SparseCropCoverage.catalog → Certificates p)
    {k r : Nat} (hk : 15≤k) (hr : r≤5) (s t : Fin (vertices k r).length) :
    Guaranteed (graph k r) s t := by
  have result := (graphIso k r).symm.guaranteed (toVertex s) (toVertex t)
    (canonical_guaranteed cert hk hr (toVertex s) (toVertex t))
  simpa only [GraphRelabeling.Iso.symm,graphIso,from_to] using result

theorem graph_score
    (cert : ∀ p, p∈SparseCropCoverage.catalog → Certificates p)
    {k r : Nat} (hk : 15≤k) (hr : r≤5) :
    score (graph k r)=(vertices k r).length*((vertices k r).length-3) := by
  have size := vertices_length hk hr
  have large : 3≤(vertices k r).length := by omega
  have missing := arcCount_add_missingCount (graph k r) (graph_loopless k r)
  have arcs := graph_arcs (r:=r) hk
  have scoring := score_eq_missing (graph k r) (fun s t _ _ => graph_guaranteed cert hk hr s t)
  have arithmetic : (vertices k r).length*((vertices k r).length-1)=
      (vertices k r).length*((vertices k r).length-3)+2*(vertices k r).length := by
    rw [show (vertices k r).length-1=((vertices k r).length-3)+2 by omega,Nat.mul_add]
    omega
  omega

theorem core_exists
    (cert : ∀ p, p∈SparseCropCoverage.catalog → Certificates p)
    (n : Nat) (large : 85≤n) :
    ∃ E : Graph (Fin n), Loopless E ∧ arcCount E=2*n ∧ score E=n*(n-3) := by
  let k := (n+5)/6
  let r := 6*k-n
  have hk : 15≤k := by dsimp [k]; omega
  have hr : r≤5 := by dsimp [r,k]; omega
  have order : (vertices k r).length=n := by rw [vertices_length hk hr]; dsimp [r,k]; omega
  have result : ∃ E : Graph (Fin (vertices k r).length), Loopless E ∧
      arcCount E=2*(vertices k r).length ∧
      score E=(vertices k r).length*((vertices k r).length-3) :=
    ⟨graph k r,graph_loopless k r,graph_arcs hk,graph_score cert hk hr⟩
  rw [order] at result
  exact result

#print axioms core_exists
end Delivery.SixTypeCounts
