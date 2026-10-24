import SparseSupport
import GraphRelabeling
import RobustLosingRegion
import Init.Data.Nat.Bitwise.Lemmas

/-! Complete prescribed-degree row prefixes. External row choices and symmetry
routes are data; their coverage and transport are proved against actual graphs. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

def Prescribed {n : Nat} (D R : Fin n → Nat) (E : Graph (Fin n)) : Prop :=
  Loopless E ∧ (∀ s, outdegree E s = D s) ∧ (∀ t, indegree E t = R t)

def bit (mask : Nat) (t : Fin n) : Prop := mask.testBit t.val = true
instance (mask : Nat) (t : Fin n) : Decidable (bit mask t) :=
  inferInstanceAs (Decidable (_ = true))

def rowCount (n mask : Nat) : Nat :=
  ((List.finRange n).filter fun t => decide (bit mask t)).length

theorem rowCount_eq_card (mask : Nat) : rowCount n mask = card (bit (n:=n) mask) := by
  exact (card_eq _).symm

def encode {n : Nat} : List (Fin n) → Nat
  | [] => 0
  | x::xs => 2^x.val ||| encode xs

theorem encode_bit {n : Nat} (xs : List (Fin n)) (i : Nat) :
    (encode xs).testBit i = true ↔ ∃ x ∈ xs, x.val = i := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih =>
    simp only [encode,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,
      decide_eq_true_eq,ih,List.mem_cons]
    constructor
    · rintro (same | ⟨y,member,same⟩)
      · exact ⟨x,Or.inl rfl,same⟩
      · exact ⟨y,Or.inr member,same⟩
    · rintro ⟨y,(rfl | member),same⟩
      · exact Or.inl same
      · exact Or.inr ⟨y,member,same⟩

theorem encode_small {n : Nat} (xs : List (Fin n)) : encode xs < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro i high
  apply Bool.eq_false_iff.mpr
  intro set
  obtain ⟨x,_,same⟩ := (encode_bit xs i).mp set
  have := x.isLt
  omega

theorem row_exists {n : Nat} (E : Graph (Fin n)) (s : Fin n) :
    ∃ mask : Fin (2^n), ∀ t : Fin n, E s t ↔ bit mask.val t := by
  refine ⟨⟨encode (elems (E s)),encode_small _⟩,?_⟩
  intro t
  rw [bit,encode_bit]
  constructor
  · exact fun edge => ⟨t,mem_elems.mpr edge,rfl⟩
  · rintro ⟨x,member,same⟩
    have equal : x = t := Fin.ext same
    subst x
    exact mem_elems.mp member

def Agrees {n : Nat} (p : List Nat) (E : Graph (Fin n)) : Prop :=
  ∀ s : Fin n, ∀ h : s.val < p.length, ∀ t, E s t ↔ bit p[s.val] t

def Upper {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat) : Prop :=
  ∀ E, Prescribed D R E → Agrees p E → score E ≤ bound

def known {n : Nat} (p : List Nat) : Graph (Fin n) :=
  fun s t => ∃ h : s.val < p.length, bit p[s.val] t
instance {n : Nat} (p : List Nat) : DecidableRel (known (n:=n) p) :=
  fun _ _ => inferInstanceAs (Decidable (∃ h : _ < _, _))

def possible {n : Nat} (p : List Nat) : Graph (Fin n) :=
  fun s t => known p s t ∨ (p.length ≤ s.val ∧ s ≠ t)
instance {n : Nat} (p : List Nat) : DecidableRel (possible (n:=n) p) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem sandwich {n : Nat} {p : List Nat} {E : Graph (Fin n)}
    (loopless : Loopless E) (agrees : Agrees p E) :
    RobustTwoMove.Subgraph (known p) E ∧ RobustTwoMove.Subgraph E (possible p) := by
  constructor
  · rintro s t ⟨h,edge⟩
    exact (agrees s h t).mpr edge
  · intro s t edge
    by_cases before : s.val < p.length
    · exact Or.inl ⟨before,(agrees s before t).mp edge⟩
    · exact Or.inr ⟨by omega,fun same => loopless s (same ▸ edge)⟩

def PrefixOK {n : Nat} (D R : Fin n → Nat) (p : List Nat) : Prop :=
  (∀ s : Fin n, ∀ h : s.val < p.length,
    ¬ bit p[s.val] s ∧ rowCount n p[s.val] = D s) ∧
  (∀ t : Fin n,
    ((List.finRange n).filter fun s => decide (known p s t)).length ≤ R t ∧
    R t ≤ ((List.finRange n).filter fun s => decide (possible p s t)).length)
instance {n : Nat} (D R : Fin n → Nat) (p : List Nat) : Decidable (PrefixOK D R p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem prefix_ok {n : Nat} {D R : Fin n → Nat} {p : List Nat} {E : Graph (Fin n)}
    (valid : Prescribed D R E) (agrees : Agrees p E) : PrefixOK D R p := by
  refine ⟨?_,?_⟩
  · intro s hs
    refine ⟨fun edge => valid.1 s ((agrees s hs s).mpr edge),?_⟩
    rw [rowCount_eq_card,←valid.2.1 s]
    exact card_congr (fun t => (agrees s hs t).symm)
  · intro t
    have bounds := sandwich valid.1 agrees
    have lo := card_mono (fun s => bounds.1 s t)
    have hi := card_mono (fun s => bounds.2 s t)
    rw [card_eq (known p · t)] at lo
    rw [card_eq (possible p · t)] at hi
    change _ ≤ indegree E t at lo
    change indegree E t ≤ _ at hi
    rw [valid.2.2 t] at lo hi
    exact ⟨lo,hi⟩

theorem invalid_upper {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (invalid : ¬PrefixOK D R p) : Upper D R p bound := by
  intro E valid agrees
  exact False.elim (invalid (prefix_ok valid agrees))

theorem agrees_append {n : Nat} {p : List Nat} {E : Graph (Fin n)}
    (h : p.length < n) (agrees : Agrees p E) (mask : Nat)
    (row : ∀ t, E ⟨p.length,h⟩ t ↔ bit mask t) : Agrees (p++[mask]) E := by
  intro s hs t
  by_cases before : s.val < p.length
  · simpa [List.getElem_append,before] using agrees s before t
  · have same : s = ⟨p.length,h⟩ := by
      apply Fin.ext
      change s.val = p.length
      simp only [List.length_append,List.length_singleton] at hs
      omega
    subst s
    simpa using row t

def RowCover (n d : Nat) (rows : List Nat) : Prop :=
  ∀ mask : Fin (2^n), rowCount n mask.val = d → mask.val ∈ rows
instance (n d : Nat) (rows : List Nat) : Decidable (RowCover n d rows) :=
  inferInstanceAs (Decidable (∀ mask : Fin (2^n), _))

theorem branch_upper {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (h : p.length < n) (rows : List Nat)
    (cover : RowCover n (D ⟨p.length,h⟩) rows)
    (children : ∀ mask ∈ rows, Upper D R (p++[mask]) bound) : Upper D R p bound := by
  intro E valid agrees
  obtain ⟨mask,row⟩ := row_exists E ⟨p.length,h⟩
  have count : rowCount n mask.val = D ⟨p.length,h⟩ := by
    rw [rowCount_eq_card,←valid.2.1 ⟨p.length,h⟩]
    exact card_congr (fun t => (row t).symm)
  exact children mask.val (cover mask count) E valid (agrees_append h agrees _ row)

#print axioms branch_upper
end Delivery.RowPrefix
