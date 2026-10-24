import TwelveHubGraph
import SparseDeletion

/-! Exact counts and prefix attainment for the literal full twelve-hub graph. -/
namespace Delivery.TwelveHubCounts
open TwelveHubGraph FiniteGame Extremal DenseCombinatorics ConstructionCounts

def encode {g b : Nat} : Vertex g b → Fin (12+g+b)
  | .inl s => ComplementarySum.encode (.inl (ComplementarySum.encode s))
  | .inr x => ComplementarySum.encode (.inr x)
def decode {g b : Nat} (s : Fin (12+g+b)) : Vertex g b :=
  match ComplementarySum.decode s with
  | .inl y => .inl (ComplementarySum.decode y)
  | .inr x => .inr x

@[simp] theorem decode_encode {g b : Nat} (s : Vertex g b) : decode (encode s)=s := by
  rcases s with s|x <;> simp [encode,decode]
@[simp] theorem encode_decode {g b : Nat} (s : Fin (12+g+b)) : encode (decode s)=s := by
  have h := ComplementarySum.encode_decode s
  unfold decode
  split
  · rename_i y eq
    simpa only [eq,encode,ComplementarySum.encode_decode] using h
  · rename_i x eq
    simpa only [eq,encode] using h

def graph {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop) : Graph (Fin (12+g+b)) :=
  fun s t => base hg J (decode s) (decode t)
def envelope {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop) : Graph (Fin (12+g+b)) :=
  fun s t => upper hg J (decode s) (decode t)
def optional {g b : Nat} : Graph (Fin (12+g+b)) := fun s t => extra (decode s) (decode t)

def iso {g b : Nat} (E : Graph (Vertex g b)) :
    GraphRelabeling.Iso E (fun s t => E (decode s) (decode t)) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  edge_iff s t := by simp only [decode_encode]

theorem card_split {g b : Nat} (P : Vertex g b → Prop) :
    card (fun s : Fin (12+g+b) => P (decode s)) =
      card (fun h => P (.inl (.inl h))) + card (fun j => P (.inl (.inr j))) +
        card (fun x => P (.inr x)) := by
  rw [ComplementarySum.card_split,ComplementarySum.card_split]
  simp only [decode,ComplementarySum.decode_left,ComplementarySum.decode_right]

theorem sum_split {g b : Nat} (f : Vertex g b → Nat) :
    ((List.finRange (12+g+b)).map (fun s => f (decode s))).sum =
      ((List.finRange 12).map (fun h => f (.inl (.inl h)))).sum +
      ((List.finRange g).map (fun j => f (.inl (.inr j)))).sum +
      ((List.finRange b).map (fun x => f (.inr x))).sum := by
  rw [ComplementarySum.sum_split,ComplementarySum.sum_split]
  simp only [decode,ComplementarySum.decode_left,ComplementarySum.decode_right]

theorem hub_count (h : Fin 12) : card (hubArrow h)=9 := by
  rw [card_eq]
  revert h
  decide +kernel
theorem guide_count (j : Fin 8) : card (fun h => ¬omitted j h) = if j.val<2 then 9 else 10 := by
  rw [card_eq]
  revert j
  decide +kernel
theorem access_count : card access=7 := by rw [card_eq]; decide +kernel

private theorem sum_const {α : Type} (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum=xs.length*c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem guides_sum {g : Nat} (small : g≤8) (low : 2≤g) :
    ((List.finRange g).map fun j => if j.val<2 then 9 else 10).sum=10*g-2 := by
  have checked : ∀ g : Fin 9, 2≤g.val →
      ((List.finRange g.val).map fun j => if j.val<2 then 9 else 10).sum=10*g.val-2 := by
    decide +kernel
  exact checked ⟨g,by omega⟩ low

theorem base_count {g b r : Nat} (hg : g≤8) (low : 2≤g)
    (J : Fin b → Fin g → Prop) (weight : ∀ x, card (J x)=r) :
    arcCount (graph hg J)=106+22*g+(19+r)*b := by
  rw [SparseSupport.arc_rows]
  change ((List.finRange (12+g+b)).map
    (fun s => card (fun t => base hg J (decode s) (decode t)))).sum = _
  rw [sum_split (fun v : Vertex g b => card (fun t : Fin (12+g+b) => base hg J v (decode t)))]
  have rows (v : Vertex g b) : card (fun t : Fin (12+g+b) => base hg J v (decode t)) =
      card (fun h => base hg J v (.inl (.inl h))) + card (fun j => base hg J v (.inl (.inr j))) +
        card (fun x => base hg J v (.inr x)) := card_split (fun w => base hg J v w)
  simp only [rows]
  simp only [base,hub_count,card_true,card_false,guide_count,guideIndex,weight,
    access_count,Nat.add_zero]
  rw [sum_const,sum_const,List.length_finRange,List.length_finRange,guides_sum hg low]
  have cancel : 10*g-2+2=10*g := Nat.sub_add_cancel (by omega)
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_comm b] at *
  omega

theorem optional_count {g b : Nat} : arcCount (optional (g:=g) (b:=b))=b*(g+b-1) := by
  rw [SparseSupport.arc_rows]
  change ((List.finRange (12+g+b)).map
    (fun s => card (fun t => extra (decode s) (decode t)))).sum = _
  rw [sum_split (fun v : Vertex g b => card (fun t : Fin (12+g+b) => extra v (decode t)))]
  have different (x : Fin b) : card (fun y => x≠y)=b-1 := by
    have part := SparseSupport.card_complement (fun y => y=x)
    rw [SparseDeletion.card_singleton] at part
    have same : card (fun y => x≠y)=card (fun y => ¬y=x) := card_congr (fun y => ne_comm)
    omega
  have rows (v : Vertex g b) : card (fun t : Fin (12+g+b) => extra v (decode t)) =
      card (fun h => extra v (.inl (.inl h))) + card (fun j => extra v (.inl (.inr j))) +
        card (fun x => extra v (.inr x)) := card_split (fun w => extra v w)
  simp only [rows]
  simp only [extra,card_true,card_false,different,Nat.zero_add,Nat.add_zero]
  rw [sum_const,sum_const,sum_const]
  simp only [List.length_finRange,Nat.mul_zero,Nat.zero_add]
  by_cases zero : b=0
  · simp [zero]
  · have cancel : b-1+1=b := Nat.sub_add_cancel (by omega)
    have gap : g+b-1=g+(b-1) := by omega
    rw [gap,Nat.mul_add,Nat.mul_comm b g]

theorem extra_disjoint {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (s t : Vertex g b) : base hg J s t → extra s t → False := by
  rcases s with (h|j)|x <;> rcases t with (k|l)|y <;> simp [base,extra]

theorem upper_count {g b r : Nat} (hg : g≤8) (low : 2≤g)
    (J : Fin b → Fin g → Prop) (weight : ∀ x, card (J x)=r) :
    arcCount (envelope hg J)=106+22*g+(19+r)*b+b*(g+b-1) := by
  have h := SparseSupport.arcs_union (E:=graph hg J) (F:=optional)
    (fun s t => extra_disjoint hg J (decode s) (decode t))
  change arcCount (envelope hg J)=arcCount (graph hg J)+arcCount optional at h
  rw [h,base_count hg low J weight,optional_count]

theorem delivers {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j) :
    GuaranteedPrefix.Delivers (graph hg J) (envelope hg J) := by
  intro G lower bound s t
  let F : Graph (Vertex g b) := fun x y => G (encode x) (encode y)
  have lo : RobustTwoMove.Subgraph (base hg J) F := by
    intro x y arrow
    apply lower (encode x) (encode y)
    simpa only [graph,decode_encode] using arrow
  have hi : RobustTwoMove.Subgraph F (upper hg J) := by
    intro x y arrow
    have result := bound (encode x) (encode y) arrow
    simpa only [envelope,decode_encode] using result
  have result : Guaranteed F (decode s) (decode t) :=
    fun c initial => ⟨3,envelope_universal hg J two difference F lo hi _ _ c initial⟩
  have back := (iso F).guaranteed (decode s) (decode t) result
  simpa only [iso,F,encode_decode] using back

theorem maximum {g b r m : Nat} (hg : g≤8) (lowg : 2≤g)
    (J : Fin b → Fin g → Prop) (weight : ∀ x, card (J x)=r)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j)
    (low : 106+22*g+(19+r)*b≤m)
    (high : m≤106+22*g+(19+r)*b+b*(g+b-1)) :
    IsMaximum (12+g+b) m ((12+g+b)*(12+g+b-1)-m) := by
  apply GuaranteedPrefix.maximum (graph hg J) (envelope hg J)
    (fun s t h => Or.inl h) (fun s h => loopless hg J (decode s) h)
    (delivers hg J two difference)
  · simpa only [base_count hg lowg J weight] using low
  · simpa only [upper_count hg lowg J weight] using high

#print axioms base_count
#print axioms maximum
end Delivery.TwelveHubCounts
