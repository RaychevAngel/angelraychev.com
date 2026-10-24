import ReducedTwelveHubGraph
import TwelveHubCodes

/-! Exact counts, explicit finite guide codes, and arbitrary-budget prefix
attainment for the reduced twelve-hub family. -/
namespace Delivery.ReducedTwelveHubCounts
open ReducedTwelveHubGraph FiniteGame Extremal DenseCombinatorics ConstructionCounts
open TwelveHubGraph (Vertex hubArrow guideIndex)
open TwelveHubCounts (encode decode decode_encode encode_decode iso card_split sum_split
  hub_count guide_count guides_sum)

def graph {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop) : Graph (Fin (12+g+b)) :=
  fun s t => base hg J (decode s) (decode t)
def envelope {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop) : Graph (Fin (12+g+b)) :=
  fun s t => upper hg J (decode s) (decode t)
def optional {g b : Nat} : Graph (Fin (12+g+b)) := fun s t => extra (decode s) (decode t)

theorem access_count : card access=4 := by rw [card_eq]; decide +kernel
theorem extra_access_count : card (fun h => ¬bulkSafe h ∧ ¬access h)=5 := by
  rw [card_eq]; decide +kernel
theorem outlet_count : card outlet=8 := by rw [card_eq]; decide +kernel
theorem nonoutlet_count : card (fun h => ¬outlet h)=4 := by rw [card_eq]; decide +kernel

private theorem card_constant (n : Nat) (P : Prop) [Decidable P] :
    card (fun _ : Fin n => P)=if P then n else 0 := by
  by_cases h : P <;> simp [h,card_true,card_false]

private theorem sum_const {α : Type} (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum=xs.length*c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

private theorem sum_offset {α : Type} (xs : List α) (P : α → Prop) [DecidablePred P]
    (a b : Nat) :
    (xs.map (fun x => a+(if P x then b else 0))).sum =
      xs.length*a+(xs.filter (fun x => decide (P x))).length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : P x <;> simp [h,ih,Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem base_count {g b r : Nat} (hg : g≤7) (low : 2≤g)
    (J : Fin b → Fin g → Prop) (weight : ∀ x, card (J x)=r) :
    arcCount (graph hg J)=106+18*g+(12+r)*b := by
  rw [SparseSupport.arc_rows]
  change ((List.finRange (12+g+b)).map
    (fun s => card (fun t => base hg J (decode s) (decode t)))).sum = _
  rw [sum_split (fun v : Vertex g b => card (fun t : Fin (12+g+b) => base hg J v (decode t)))]
  have rows (v : Vertex g b) : card (fun t : Fin (12+g+b) => base hg J v (decode t)) =
      card (fun h => base hg J v (.inl (.inl h))) + card (fun j => base hg J v (.inl (.inr j))) +
        card (fun x => base hg J v (.inr x)) := card_split (fun w => base hg J v w)
  simp only [rows]
  simp only [base,hub_count,card_constant,ite_false,guide_count,guideIndex,weight,
    access_count,Nat.add_zero]
  have merge (h : Fin 12) : 9+(if outlet h then g else 0)+(if outlet h then b else 0) =
      9+(if outlet h then g+b else 0) := by by_cases yes : outlet h <;> simp [yes,Nat.add_assoc]
  simp only [merge]
  rw [sum_offset,sum_const,List.length_finRange,List.length_finRange,guides_sum (by omega) low]
  have out : ((List.finRange 12).filter (fun x => decide (outlet x))).length=8 := by
    simpa only [card_eq] using outlet_count
  rw [out]
  have cancel : 10*g-2+2=10*g := Nat.sub_add_cancel (by omega)
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_comm b] at *
  omega

theorem optional_count {g b : Nat} : arcCount (optional (g:=g) (b:=b))=b*(g+b+8) := by
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
  simp only [extra,card_constant,ite_true,ite_false,different,extra_access_count,Nat.zero_add,Nat.add_zero]
  have hubsum : ((List.finRange 12).map (fun h => if ¬outlet h then b else 0)).sum=4*b := by
    have h := sum_offset (List.finRange 12) (fun h => ¬outlet h) 0 b
    have count : ((List.finRange 12).filter (fun h => decide (¬outlet h))).length=4 := by
      simpa only [card_eq] using nonoutlet_count
    simpa only [Nat.zero_add,Nat.mul_zero,count] using h
  rw [hubsum,sum_const,sum_const]
  simp only [List.length_finRange]
  by_cases zero : b=0
  · simp [zero]
  · have gap : 5+(b-1)=b+4 := by omega
    rw [gap]
    simp only [Nat.add_mul,Nat.mul_comm b]
    omega

theorem extra_disjoint {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (s t : Vertex g b) : base hg J s t → extra s t → False := by
  rcases s with (h|j)|x <;> rcases t with (k|l)|y <;> simp [base,extra]
  intro present _
  exact present

theorem upper_count {g b r : Nat} (hg : g≤7) (low : 2≤g)
    (J : Fin b → Fin g → Prop) (weight : ∀ x, card (J x)=r) :
    arcCount (envelope hg J)=106+18*g+(12+r)*b+b*(g+b+8) := by
  have h := SparseSupport.arcs_union (E:=graph hg J) (F:=optional)
    (fun s t => extra_disjoint hg J (decode s) (decode t))
  change arcCount (envelope hg J)=arcCount (graph hg J)+arcCount optional at h
  rw [h,base_count hg low J weight,optional_count]

theorem delivers {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
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
    fun c initial => ⟨5,envelope_universal hg J two difference F lo hi _ _ c initial⟩
  have back := (iso F).guaranteed (decode s) (decode t) result
  simpa only [iso,F,encode_decode] using back

theorem maximum_of_codes {g b r m : Nat} (hg : g≤7) (lowg : 2≤g)
    (J : Fin b → Fin g → Prop) (weight : ∀ x, card (J x)=r)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j)
    (low : 106+18*g+(12+r)*b≤m)
    (high : m≤106+18*g+(12+r)*b+b*(g+b+8)) :
    IsMaximum (12+g+b) m ((12+g+b)*(12+g+b-1)-m) := by
  apply GuaranteedPrefix.maximum (graph hg J) (envelope hg J)
    (fun s t h => Or.inl h) (fun s h => loopless hg J (decode s) h)
    (delivers hg J two difference)
  · simpa only [base_count hg lowg J weight] using low
  · simpa only [upper_count hg lowg J weight] using high

theorem maximum {g b r m : Nat} (hg : g≤7) (lowr : 2≤r) (hr : r≤g)
    (room : b≤TwelveHubCodes.capacity g r)
    (low : 106+18*g+(12+r)*b≤m)
    (high : m≤106+18*g+(12+r)*b+b*(g+b+8)) :
    IsMaximum (12+g+b) m ((12+g+b)*(12+g+b-1)-m) :=
  maximum_of_codes hg (by omega) (TwelveHubCodes.assigned (by omega) hr room)
    (TwelveHubCodes.assigned_weight (by omega) hr room)
    (TwelveHubCodes.assigned_two (by omega) hr room lowr)
    (TwelveHubCodes.assigned_difference (by omega) hr room) low high

#print axioms base_count
#print axioms maximum
end Delivery.ReducedTwelveHubCounts
