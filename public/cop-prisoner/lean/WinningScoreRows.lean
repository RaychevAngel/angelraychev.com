import Extremal

/-! Positive finite witnesses for an extremal lower bound. The table may
omit losing states: it checks a winning region and every legal cop reply,
then counts only individually certified missing pairs. A separate upper
theorem, never a producer's score field, establishes exactness. -/
namespace Delivery.WinningScoreRows
open FiniteGame Extremal

structure Data (n : Nat) where
  code : Fin n → Fin n → Fin n → Nat
  move : Fin n → Fin n → Fin n → Fin n

def RowGood {n : Nat} (E : Graph (Fin n)) (D : Data n)
    (replies : Fin n → List (Fin n)) (t r c : Fin n) : Prop :=
  0<D.code t r c → r≠t → r≠c →
    Legal E r (D.move t r c) ∧ (D.move t r c=t ∨
      (D.move t r c≠c ∧ (replies c).all (fun d => decide
        (D.move t r c≠d ∧ 0<D.code t (D.move t r c) d ∧
          D.code t (D.move t r c) d<D.code t r c))=true))

instance {n : Nat} (E : Graph (Fin n)) [DecidableRel E] (D : Data n)
    (replies : Fin n → List (Fin n)) (t r c : Fin n) :
    Decidable (RowGood E D replies t r c) :=
  inferInstanceAs (Decidable (_ → _ → _ → (_ ∨ _) ∧ _))

def region {n : Nat} {E : Graph (Fin n)} (D : Data n)
    (replies : Fin n → List (Fin n))
    (coverage : ∀ c d, Legal E c d → d∈replies c)
    (checked : ∀ t r c, RowGood E D replies t r c) (t : Fin n) :
    WinningRegion E t where
  region r c := 0<D.code t r c
  rank := D.code t
  move := D.move t
  valid := by
    intro r c inside nonterminal safe
    obtain ⟨legal,finish | ⟨safeNow,future⟩⟩ := checked t r c inside nonterminal safe
    · exact ⟨legal,Or.inl finish⟩
    · refine ⟨legal,Or.inr ⟨safeNow,?_⟩⟩
      intro d reply
      exact of_decide_eq_true ((List.all_eq_true.mp future) d (coverage c d reply))

def acceptedCount {n : Nat} (E : Graph (Fin n)) [DecidableRel E]
    (accepted : Fin n → Fin n → Bool) : Nat :=
  ((allPairs n).filter fun p =>
    decide (p.1≠p.2 ∧ ¬E p.1 p.2 ∧ accepted p.1 p.2=true)).length

theorem lower_bound {n : Nat} (E : Graph (Fin n)) [DecidableRel E]
    (D : Data n) (replies : Fin n → List (Fin n))
    (accepted : Fin n → Fin n → Bool)
    (coverage : ∀ c d, Legal E c d → d∈replies c)
    (checked : ∀ t r c, RowGood E D replies t r c)
    (entries : ∀ s t, accepted s t=true → ∀ c, c≠s → 0<D.code t s c) :
    acceptedCount E accepted≤score E := by
  classical
  apply filter_length_mono
  intro pair yes
  have facts := of_decide_eq_true yes
  apply decide_eq_true
  refine ⟨facts.1,facts.2.1,?_⟩
  intro c initial
  exact ⟨_,winningRegion_winning (region D replies coverage checked pair.2)
    pair.1 c (entries pair.1 pair.2 facts.2.2 c initial) (Ne.symm initial)⟩

theorem maximum {n m value : Nat} (E : Graph (Fin n)) [DecidableRel E]
    (D : Data n) (replies : Fin n → List (Fin n))
    (accepted : Fin n → Fin n → Bool)
    (coverage : ∀ c d, Legal E c d → d∈replies c)
    (checked : ∀ t r c, RowGood E D replies t r c)
    (entries : ∀ s t, accepted s t=true → ∀ c, c≠s → 0<D.code t s c)
    (loops : Loopless E) (arcs : arcCount E=m)
    (count : acceptedCount E accepted=value)
    (upper : ∀ F : Graph (Fin n), Loopless F → arcCount F=m → score F≤value) :
    IsMaximum n m value := by
  have lower := lower_bound E D replies accepted coverage checked entries
  have bound := upper E loops arcs
  exact ⟨upper,E,loops,arcs,by omega⟩

#print axioms lower_bound
#print axioms maximum
end Delivery.WinningScoreRows
