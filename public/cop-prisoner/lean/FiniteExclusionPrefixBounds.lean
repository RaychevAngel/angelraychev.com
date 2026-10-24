import FiniteExclusionBounds
import RobustLosingRegion

/-! Optimistic losing regions over a partial second permutation. Every possible
messenger move is retained; the cop uses only already fixed arrows. -/
namespace Delivery.FiniteExclusion.PrefixBounds
open FiniteGame Extremal Bounds

def PossibleSecond {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) : Prop :=
  (∃ hs : s.val < p.length, t = p[s.val]) ∨
  (p.length ≤ s.val ∧ t ≠ s ∧ t ≠ a s ∧
    ∀ u : Fin n, ∀ hu : u.val < p.length, t ≠ p[u.val])
instance {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) :
    Decidable (PossibleSecond a p s t) := inferInstanceAs (Decidable (_ ∨ _))

def upperEdge {n} (a : Assignment n) (p : List (Fin n)) : Graph (Fin n) :=
  fun s t => t = a s ∨ PossibleSecond a p s t
instance {n} (a : Assignment n) (p : List (Fin n)) : DecidableRel (upperEdge a p) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) :
    Decidable (Legal (upperEdge a p) s t) := inferInstanceAs (Decidable (_ ∨ _))

theorem completion_sandwich {n} {a b : Assignment n} {p : List (Fin n)}
    (valid : Valid a b) (agrees : Agrees p b) :
    RobustTwoMove.Subgraph (KnownEdge a p) (edgeOf a b) ∧
    RobustTwoMove.Subgraph (edgeOf a b) (upperEdge a p) := by
  constructor
  · intro s t known
    rcases known with first | ⟨hs,second⟩
    · exact Or.inl first
    · exact Or.inr (second.trans (agrees s hs).symm)
  · intro s t edge
    rcases edge with first | second
    · exact Or.inl first
    · apply Or.inr
      by_cases assigned : s.val < p.length
      · exact Or.inl ⟨assigned,second.trans (agrees s assigned)⟩
      · refine Or.inr ⟨by omega,?_,?_,?_⟩
        · rw [second]; exact (valid.2 s).1
        · rw [second]; exact (valid.2 s).2
        · intro u hu equal
          have same : s = u := valid.1 s u (by rw [←second,equal,agrees u hu])
          subst u
          exact assigned hu

def PrefixRegionOK {n} (a : Assignment n) (p : List (Fin n))
    (t : Fin n) (mask : Nat) : Prop :=
  (∀ r c : Fin n, maskRegion mask r c → r ≠ t) ∧
  (∀ r c : Fin n, maskRegion mask r c → r ≠ c →
    ∀ z, Legal (upperEdge a p) r z → z ≠ t ∧
      (z = c ∨ ∃ c', lowerLegal a p c c' ∧
        (z = c' ∨ maskRegion mask z c')))
instance {n} (a : Assignment n) (p : List (Fin n)) (t : Fin n) (mask : Nat) :
    Decidable (PrefixRegionOK a p t mask) := inferInstanceAs (Decidable (_ ∧ _))

def prefixCertificate {n} (a : Assignment n) (p : List (Fin n))
    (t : Fin n) (mask : Nat) (ok : PrefixRegionOK a p t mask) :
    RobustLosingRegion.Certificate (upperEdge a p) (KnownEdge a p) t where
  region := maskRegion mask
  nonterminal := ok.1
  closed := ok.2

theorem certified_prefix_not_guaranteed {n} {a b : Assignment n}
    {p : List (Fin n)} {masks : List (Fin n × Nat)}
    (valid : Valid a b) (agrees : Agrees p b)
    (checked : ∀ tm, tm ∈ masks → PrefixRegionOK a p tm.1 tm.2) {s t : Fin n}
    (lost : CertifiedLost masks s t) : ¬Guaranteed (edgeOf a b) s t := by
  obtain ⟨⟨u,mask⟩,member,equal,c,initial,region⟩ := lost
  change u = t at equal
  subst u
  have sandwich := completion_sandwich valid agrees
  exact RobustLosingRegion.not_guaranteed
    (prefixCertificate a p t mask (checked _ member)) sandwich.1 sandwich.2 region initial

theorem prefix_masks_upper {n} (a : Assignment n) (p : List (Fin n)) (bound : Nat)
    (masks : List (Fin n × Nat))
    (closed : ∀ tm, tm ∈ masks → PrefixRegionOK a p tm.1 tm.2)
    (count : refinedCount a p masks ≤ bound) : UpperPrefix a p bound := by
  intro b valid agrees
  apply Nat.le_trans ?_ count
  classical
  apply filter_length_mono
  intro st h
  have indirect : Indirect (edgeOf a b) st.1 st.2 := of_decide_eq_true h
  exact decide_eq_true ⟨indirect_eligible valid agrees indirect,
    fun lost => certified_prefix_not_guaranteed valid agrees closed lost indirect.2.2⟩

#print axioms completion_sandwich
#print axioms prefix_masks_upper
end Delivery.FiniteExclusion.PrefixBounds
