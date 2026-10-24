import StagedEnvelopes
import GuaranteedPrefix

/-! Sparse-reply checking for literal asymmetric stages. Reply-list coverage
is proved against the upper graph, and every messenger move uses the lower
graph. The checker therefore applies to every intermediate optional subset. -/
namespace Delivery.MainStageRows
open FiniteGame Extremal RobustTwoMove StagedEnvelopes

structure Data (n : Nat) where
  rank : Fin n → Fin n → Fin n → Nat
  move : Fin n → Fin n → Fin n → Fin n

def RowGood {n : Nat} (B : Graph (Fin n)) (D : Data n)
    (replies : Fin n → List (Fin n)) (t r c : Fin n) : Prop :=
  r≠t → r≠c → Legal B r (D.move t r c) ∧
    (D.move t r c=t ∨ (D.move t r c≠c ∧
      (replies c).all (fun d => decide (D.move t r c≠d ∧
        D.rank t (D.move t r c) d < D.rank t r c))=true))

instance {n : Nat} (B : Graph (Fin n)) [DecidableRel B] (D : Data n)
    (replies : Fin n → List (Fin n)) (t r c : Fin n) :
    Decidable (RowGood B D replies t r c) := inferInstanceAs (Decidable
      (r≠t → r≠c → (r=D.move t r c ∨ B r (D.move t r c)) ∧
        (D.move t r c=t ∨ (D.move t r c≠c ∧
          (replies c).all (fun d => decide (D.move t r c≠d ∧
            D.rank t (D.move t r c) d < D.rank t r c))=true))))

theorem certificate {n : Nat} (B E : Graph (Fin n)) (D : Data n)
    (replies : Fin n → List (Fin n))
    (coverage : ∀ c d, Legal E c d → d∈replies c)
    (checked : ∀ t r c, RowGood B D replies t r c) (t : Fin n) :
    Nonempty (RankEnvelope B E t) := by
  refine ⟨⟨D.rank t,D.move t,?_⟩⟩
  intro r c notTarget distinct
  obtain ⟨move,finish | ⟨safe,repliesGood⟩⟩ := checked t r c notTarget distinct
  · exact ⟨move,Or.inl finish⟩
  · refine ⟨move,Or.inr ⟨safe,?_⟩⟩
    intro d legal
    exact of_decide_eq_true ((List.all_eq_true.mp repliesGood) d (coverage c d legal))

theorem delivers {n : Nat} (B E : Graph (Fin n)) (D : Data n)
    (replies : Fin n → List (Fin n))
    (coverage : ∀ c d, Legal E c d → d∈replies c)
    (checked : ∀ t r c, RowGood B D replies t r c) : GuaranteedPrefix.Delivers B E := by
  intro G lower upper s t c distinct
  obtain ⟨cert⟩ := certificate B E D replies coverage checked t
  exact ⟨_,envelope_winning cert lower upper (Ne.symm distinct)⟩

theorem maximum {n m : Nat} (B E : Graph (Fin n)) (D : Data n)
    (replies : Fin n → List (Fin n)) (subset : Subgraph B E) (loopless : Loopless E)
    (coverage : ∀ c d, Legal E c d → d∈replies c)
    (checked : ∀ t r c, RowGood B D replies t r c)
    (low : arcCount B≤m) (high : m≤arcCount E) : IsMaximum n m (n*(n-1)-m) :=
  GuaranteedPrefix.maximum B E subset loopless (delivers B E D replies coverage checked) low high

#print axioms delivers
#print axioms maximum
end Delivery.MainStageRows
