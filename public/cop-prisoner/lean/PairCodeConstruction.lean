import PairCodeCapacity
import ComplementarySum
import PrefixEnvelope

/-! Standard Fin labels and exact arrow counts for the separated pair-code
construction. The optional arrows are precisely the nonloop ordered pairs
of outside vertices. -/
namespace Delivery.PairCodeConstruction
open FiniteGame Extremal DenseCombinatorics ConstructionCounts
open DenseTwoType PairCodeGeometry RobustTwoMove

def encode {k q : Nat} : Sum (Vertex k) (Fin q) → Fin (2*k+q)
  | .inl v => ComplementarySum.left (2*k) q (DenseTwoType.encode v)
  | .inr v => ComplementarySum.right (2*k) q v

def decode {k q : Nat} (v : Fin (2*k+q)) : Sum (Vertex k) (Fin q) :=
  match ComplementarySum.decode v with
  | .inl v => .inl (DenseTwoType.decode v)
  | .inr v => .inr v

@[simp] theorem decode_left {k q : Nat} (v : Fin (2*k)) :
    decode (ComplementarySum.left (2*k) q v) = .inl (DenseTwoType.decode v) := by
  simp [decode]

@[simp] theorem decode_right {k q : Nat} (v : Fin q) :
    decode (ComplementarySum.right (2*k) q v) = .inr v := by simp [decode]

@[simp] theorem decode_encode {k q : Nat} (v : Sum (Vertex k) (Fin q)) : decode (encode v) = v := by
  cases v <;> simp [encode]

@[simp] theorem encode_decode {k q : Nat} (v : Fin (2*k+q)) : encode (decode v) = v := by
  have eq := ComplementarySum.encode_decode v
  unfold decode
  cases h : ComplementarySum.decode v with
  | inl x => simpa [h,encode,ComplementarySum.encode] using eq
  | inr x => simpa [h,encode,ComplementarySum.encode] using eq

def graph {k q : Nat} (C : Fin q → Code k) (full : Bool) : Graph (Fin (2*k+q)) :=
  fun s t => (if full then PairCodeRouting.Envelope C else PairCodeRouting.Base C) (decode s) (decode t)

theorem graph_subset {k q : Nat} (C : Fin q → Code k) : Subgraph (graph C false) (graph C true) :=
  fun _ _ h => PairCodeRouting.subset C _ _ h

theorem graph_loopless {k q : Nat} (C : Fin q → Code k) (full : Bool) : Loopless (graph C full) := by
  intro s h
  cases full
  · exact PairCodeRouting.loopless C (decode s) (PairCodeRouting.subset C _ _ h)
  · exact PairCodeRouting.loopless C (decode s) h

theorem graph_witnesses {k q : Nat} (hk : 5 ≤ k) (C : Fin q → Code k)
    (distinct : PairCodeRouting.Distinct C) : Witnesses (graph C false) (graph C true) := by
  intro s t c different initial absent
  have ds : decode s ≠ decode t := by
    intro same; exact different (by simpa using congrArg encode same)
  have dc : decode c ≠ decode s := by
    intro same; exact initial (by simpa using congrArg encode same)
  obtain ⟨u,first,last,uncollided,unreached⟩ :=
    PairCodeRouting.witnesses hk C distinct (decode s) (decode t) (decode c) ds dc absent
  refine ⟨encode u,?_,?_,?_,?_⟩
  · simpa only [graph,Bool.false_eq_true,if_false,decode_encode] using first
  · simpa only [graph,Bool.false_eq_true,if_false,decode_encode] using last
  · intro same; exact uncollided (by simpa using congrArg decode same)
  · simpa only [graph,if_true,decode_encode] using unreached

theorem core_row {k q : Nat} (hk : 5 ≤ k) (C : Fin q → Code k) (full : Bool)
    (s : Fin (2*k)) :
    card (fun t => ComplementarySum.left (2*k) q s ≠ t ∧
      ¬ graph C full (ComplementarySum.left (2*k) q s) t) = 2 := by
  rw [ComplementarySum.card_split]
  have left : card (fun t => ComplementarySum.left (2*k) q s ≠ ComplementarySum.left (2*k) q t ∧
      ¬ graph C full (ComplementarySum.left (2*k) q s) (ComplementarySum.left (2*k) q t)) = 2 := by
    have eq : card (fun t => ComplementarySum.left (2*k) q s ≠ ComplementarySum.left (2*k) q t ∧
        ¬ graph C full (ComplementarySum.left (2*k) q s) (ComplementarySum.left (2*k) q t)) =
        card (fun t => s ≠ t ∧ ¬ DenseTwoType.graph k s t) := by
      apply card_congr
      intro t
      cases full <;> simp [graph,DenseTwoType.graph,PairCodeRouting.Base,PairCodeRouting.Envelope,
        ComplementarySum.left_ne_iff]
    rw [eq,card_congr (DenseTwoType.graph_missing_iff s)]
    exact card_two _ _ (fun same => neighbours_distinct hk _ (DenseTwoType.encode_injective same))
  have right : card (fun t => ComplementarySum.left (2*k) q s ≠ ComplementarySum.right (2*k) q t ∧
      ¬ graph C full (ComplementarySum.left (2*k) q s) (ComplementarySum.right (2*k) q t)) = 0 := by
    apply card_eq_zero.mpr
    intro t h
    apply h.2
    cases full <;> simp [graph,PairCodeRouting.Base,PairCodeRouting.Envelope]
  rw [left,right,Nat.add_zero]

theorem code_card {k : Nat} (K : Code k) :
    card (fun t : Fin (2*k) => K.Mem (DenseTwoType.decode t)) = 2 := by
  have eq : ∀ t, K.Mem (DenseTwoType.decode t) ↔
      t = DenseTwoType.encode K.a ∨ t = DenseTwoType.encode K.b := by
    intro t
    constructor
    · rintro (h | h)
      · exact Or.inl (by simpa using congrArg DenseTwoType.encode h)
      · exact Or.inr (by simpa using congrArg DenseTwoType.encode h)
    · rintro (rfl | rfl) <;> simp [Code.Mem]
  rw [card_congr eq]
  exact card_two _ _ (fun same => separated_ne K.separated (DenseTwoType.encode_injective same))

theorem outside_row {k q : Nat} (C : Fin q → Code k) (full : Bool) (s : Fin q) :
    card (fun t => ComplementarySum.right (2*k) q s ≠ t ∧
      ¬ graph C full (ComplementarySum.right (2*k) q s) t) =
      if full then 2 else q+1 := by
  classical
  rw [ComplementarySum.card_split]
  have left : card (fun t => ComplementarySum.right (2*k) q s ≠ ComplementarySum.left (2*k) q t ∧
      ¬ graph C full (ComplementarySum.right (2*k) q s) (ComplementarySum.left (2*k) q t)) = 2 := by
    apply Eq.trans (b := card (fun t : Fin (2*k) => (C s).Mem (DenseTwoType.decode t)))
    · apply card_congr
      intro t
      have neq : ComplementarySum.right (2*k) q s ≠ ComplementarySum.left (2*k) q t := by
        intro same
        have := congrArg Fin.val same
        dsimp [ComplementarySum.left,ComplementarySum.right] at this
        have := t.isLt
        omega
      cases full <;> simp [graph,PairCodeRouting.Base,PairCodeRouting.Envelope,neq]
    · exact code_card (C s)
  rw [left]
  cases full
  · have right : card (fun t => ComplementarySum.right (2*k) q s ≠ ComplementarySum.right (2*k) q t ∧
        ¬ graph C false (ComplementarySum.right (2*k) q s) (ComplementarySum.right (2*k) q t)) = q-1 := by
      have eq : ∀ t, (ComplementarySum.right (2*k) q s ≠ ComplementarySum.right (2*k) q t ∧
          ¬ graph C false (ComplementarySum.right (2*k) q s) (ComplementarySum.right (2*k) q t)) ↔ s ≠ t := by
        intro t
        simp [graph,PairCodeRouting.Base,ComplementarySum.right_ne_iff]
      rw [card_congr eq]
      have partition := card_partition (fun _ : Fin q => True) (fun t => t=s)
      have single : card (fun t : Fin q => t=s) = 1 := by
        rw [card_eq]
        simp [List.filter_eq,(List.nodup_finRange q).count]
      simp only [true_and,card_true] at partition
      rw [single] at partition
      have same := card_congr (P := fun t : Fin q => s ≠ t) (Q := fun t => ¬ t=s)
        (fun t => ne_comm)
      change card (fun t : Fin q => s ≠ t) = q-1
      rw [same]
      omega
    rw [right]
    have := s.isLt
    simp only [Bool.false_eq_true,if_false]
    omega
  · have right : card (fun t => ComplementarySum.right (2*k) q s ≠ ComplementarySum.right (2*k) q t ∧
        ¬ graph C true (ComplementarySum.right (2*k) q s) (ComplementarySum.right (2*k) q t)) = 0 := by
      apply card_eq_zero.mpr
      intro t h
      apply h.2
      simpa only [graph,if_true,decode_right,PairCodeRouting.Envelope] using
        (ComplementarySum.right_ne_iff s t).mp h.1
    simp only [right,if_true,Nat.add_zero]

theorem missing_count {k q : Nat} (hk : 5 ≤ k) (C : Fin q → Code k) (full : Bool) :
    missingCount (graph C full) = if full then 2*(2*k+q) else 4*k+q*(q+1) := by
  rw [missing_rows,ComplementarySum.sum_split]
  simp only [core_row hk,outside_row]
  have constant {α : Type} (xs : List α) (a : Nat) : (xs.map (fun _ => a)).sum = xs.length*a := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  simp only [constant,List.length_finRange]
  cases full <;> simp <;> omega

theorem base_arcs {k q : Nat} (hk : 6 ≤ k) (C : Fin q → Code k) :
    arcCount (graph C false) = (4*k-2)*(2*k+q)-2*k*(2*k+1) := by
  have partition := arcCount_add_missingCount (graph C false) (graph_loopless C false)
  rw [missing_count (by omega : 5 ≤ k)] at partition
  simp only [Bool.false_eq_true,if_false] at partition
  have a : 2*k-3+3=2*k := by omega
  have b : 4*k-2+2=4*k := by omega
  have c : 2*k+q-1+1=2*k+q := by omega
  have total : (2*k+q)*(2*k+q-1) =
      (2*k)*(2*k-3)+(4*k-2)*q+4*k+q*(q+1) := by grind
  have endpoint : (2*k)*(2*k-3)+(4*k-2)*q + 2*k*(2*k+1) =
      (4*k-2)*(2*k+q) := by grind
  omega

theorem envelope_arcs {k q : Nat} (hk : 6 ≤ k) (C : Fin q → Code k) :
    arcCount (graph C true) = (2*k+q)*(2*k+q-3) := by
  have partition := arcCount_add_missingCount (graph C true) (graph_loopless C true)
  rw [missing_count (by omega : 5 ≤ k)] at partition
  simp only [if_true] at partition
  have total : (2*k+q)*(2*k+q-1) = (2*k+q)*(2*k+q-3)+2*(2*k+q) := by
    have eq : 2*k+q-1=(2*k+q-3)+2 := by omega
    rw [eq,Nat.mul_add,Nat.mul_comm (2*k+q) 2]
  omega

/-- An exact-budget adjacency recipe: take the required lexicographic prefix
of the optional outside-to-outside arrows. The code enumeration is prescribed
in PairCodeCapacity and contains no search for a winning graph. -/
noncomputable def attainer {k q : Nat} (hk : 6 ≤ k) (capacity : q ≤ k*(k-5))
    (m : Nat) : Graph (Fin (2*k+q)) :=
  let C := PairCodeCapacity.codes hk capacity
  PrefixEnvelope.graph (graph C false) (graph C true)
    (m-((4*k-2)*(2*k+q)-2*k*(2*k+1)))

theorem attainer_exact {k q m : Nat} (hk : 6 ≤ k) (capacity : q ≤ k*(k-5))
    (low : (4*k-2)*(2*k+q)-2*k*(2*k+1) ≤ m)
    (high : m ≤ (2*k+q)*(2*k+q-3)) :
    Loopless (attainer hk capacity m) ∧ arcCount (attainer hk capacity m) = m ∧
      score (attainer hk capacity m) = (2*k+q)*(2*k+q-1)-m ∧
      ∀ s t, Universal (attainer hk capacity m) t 2 s := by
  let C := PairCodeCapacity.codes hk capacity
  have lower := base_arcs hk C
  have upper := envelope_arcs hk C
  have length := PrefixEnvelope.optional_length (graph C false) (graph C true) (graph_subset C)
  have range : m-arcCount (graph C false) ≤ (PrefixEnvelope.optional (graph C false) (graph C true)).length := by
    omega
  have exactBudget : arcCount (graph C false)+(m-arcCount (graph C false))=m := by omega
  have witness := graph_witnesses (by omega : 5 ≤ k) C (PairCodeCapacity.distinct hk capacity)
  dsimp only [attainer]
  rw [← lower]
  refine ⟨PrefixEnvelope.loopless _ _ _ (graph_subset C) (graph_loopless C true),?_,?_,?_⟩
  · rw [PrefixEnvelope.arc_count _ _ _ range,exactBudget]
  · rw [PrefixEnvelope.score_count _ _ _ (graph_subset C) (graph_loopless C true) witness range,exactBudget]
  · exact PrefixEnvelope.two_move _ _ _ (graph_subset C) witness

theorem maximum_at_sum {k q m : Nat} (hk : 6 ≤ k) (capacity : q ≤ k*(k-5))
    (low : (4*k-2)*(2*k+q)-2*k*(2*k+1) ≤ m)
    (high : m ≤ (2*k+q)*(2*k+q-3)) :
    IsMaximum (2*k+q) m ((2*k+q)*(2*k+q-1)-m) := by
  let C := PairCodeCapacity.codes hk capacity
  apply PrefixEnvelope.maximum_at (graph C false) (graph C true) (graph_subset C)
    (graph_loopless C true) (graph_witnesses (by omega) C (PairCodeCapacity.distinct hk capacity))
  · simpa only [base_arcs hk] using low
  · simpa only [envelope_arcs hk] using high

/-- The generalized separated-pair interval in the manuscript's n,k form.
Every premise is arithmetic; all code, graph, game and count obligations have
been proved for the literal constructor above. -/
theorem maximum {n k m : Nat} (hk : 6 ≤ k) (order : 2*k ≤ n)
    (capacity : n ≤ k*(k-3))
    (low : (4*k-2)*n-2*k*(2*k+1) ≤ m) (high : m ≤ n*(n-3)) :
    IsMaximum n m (n*(n-1)-m) := by
  have cap_identity : k*(k-3)=2*k+k*(k-5) := by
    have eq : k-3=(k-5)+2 := by omega
    rw [eq,Nat.mul_add,Nat.mul_comm k 2,Nat.add_comm]
  have cap : n-2*k ≤ k*(k-5) := by omega
  have total : 2*k+(n-2*k)=n := by omega
  have result := maximum_at_sum (q := n-2*k) hk cap
    (by simpa only [total] using low) (by simpa only [total] using high)
  simpa only [total] using result

#print axioms graph_witnesses
#print axioms missing_count
#print axioms attainer_exact
#print axioms maximum
end Delivery.PairCodeConstruction
