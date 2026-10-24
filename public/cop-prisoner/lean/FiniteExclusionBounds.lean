import FiniteExclusionScore

/-! Union-counted prefix upper bounds. Every pruning predicate is monotone
under valid completion, and every guaranteed missing pair remains eligible. -/
namespace Delivery.FiniteExclusion.Bounds
open FiniteGame Extremal

def KnownEdge {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) : Prop :=
  t = a s ∨ ∃ h : s.val < p.length, t = p[s.val]
instance {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) :
    Decidable (KnownEdge a p s t) := inferInstanceAs (Decidable (_ ∨ _))

def SourceCamp {n} (a : Assignment n) (p : List (Fin n)) (s : Fin n) : Prop :=
  ∃ hs : s.val < p.length, ∃ c : Fin n, c ≠ s ∧
    lowerLegal a p c (a s) ∧ lowerLegal a p c p[s.val]
instance {n} (a : Assignment n) (p : List (Fin n)) (s : Fin n) :
    Decidable (SourceCamp a p s) := inferInstanceAs (Decidable (∃ hs : s.val < p.length, _))

def RecipientCamp {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) : Prop :=
  ∃ u : Fin n, ∃ hu : u.val < p.length, p[u.val] = t ∧
    ∃ c : Fin n, c ≠ s ∧ (∀ z, a z = t → lowerLegal a p c z) ∧ lowerLegal a p c u
instance {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) :
    Decidable (RecipientCamp a p s t) := inferInstanceAs (Decidable (∃ u : Fin n, _))

def Eligible {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) : Prop :=
  s ≠ t ∧ ¬KnownEdge a p s t ∧ ¬SourceCamp a p s ∧ ¬RecipientCamp a p s t
instance {n} (a : Assignment n) (p : List (Fin n)) (s t : Fin n) :
    Decidable (Eligible a p s t) := inferInstanceAs (Decidable (_ ∧ _))

def eligibleCount {n} (a : Assignment n) (p : List (Fin n)) : Nat :=
  ((allPairs n).filter fun st => decide (Eligible a p st.1 st.2)).length

def UpperPrefix {n} (a : Assignment n) (p : List (Fin n)) (bound : Nat) : Prop :=
  ∀ b, Valid a b → Agrees p b → score (edgeOf a b) ≤ bound

theorem indirect_eligible {n} {a b : Assignment n} {p : List (Fin n)}
    (valid : Valid a b) (agrees : Agrees p b) {s t : Fin n}
    (indirect : Indirect (edgeOf a b) s t) : Eligible a p s t := by
  refine ⟨indirect.1,?_,?_,?_⟩
  · intro known
    apply indirect.2.1
    rcases known with h | ⟨hs,h⟩
    · exact Or.inl h
    · exact Or.inr (h.trans (agrees s hs).symm)
  · rintro ⟨hs,c,initial,first,second⟩
    obtain ⟨k,win⟩ := indirect.2.2 c initial
    apply source_camping_not_winning indirect.1 indirect.2.1 ?_ k win
    intro z edge
    rcases edge with rfl | rfl
    · exact lower_legal agrees first
    · rw [agrees s hs]
      exact lower_legal agrees second
  · rintro ⟨u,hu,assigned,c,initial,first,second⟩
    apply ExclusionCertificates.camping_not_guaranteed indirect.1 indirect.2.1 initial ?_
      indirect.2.2
    intro z edge
    rcases edge with firstEdge | secondEdge
    · exact lower_legal agrees (first z firstEdge.symm)
    · have same : z = u := valid.1 z u
        (secondEdge.symm.trans ((agrees u hu).trans assigned).symm)
      subst z
      exact lower_legal agrees second

theorem eligible_upper {n} {a b : Assignment n} {p : List (Fin n)}
    (valid : Valid a b) (agrees : Agrees p b) :
    score (edgeOf a b) ≤ eligibleCount a p := by
  classical
  apply filter_length_mono
  intro st h
  exact decide_eq_true (indirect_eligible valid agrees (of_decide_eq_true h))

theorem invalid_upper {n} (a : Assignment n) (p : List (Fin n)) (bound : Nat)
    (invalid : ¬PrefixOK a p) : UpperPrefix a p bound := by
  intro b valid agrees
  exact False.elim (invalid (prefix_ok valid agrees))

theorem branch_upper {n} (a : Assignment n) (p : List (Fin n)) (bound : Nat)
    (h : p.length < n) (children : ∀ v : Fin n, UpperPrefix a (p++[v]) bound) :
    UpperPrefix a p bound := by
  intro b valid agrees
  exact children (b ⟨p.length,h⟩) b valid (agrees_append h agrees)

theorem local_upper {n} (a : Assignment n) (p : List (Fin n)) (bound : Nat)
    (checked : eligibleCount a p ≤ bound) : UpperPrefix a p bound := by
  intro b valid agrees
  exact Nat.le_trans (eligible_upper valid agrees) checked

/-- A selected target's closed losing region. This records only losing states;
no winning score, optimal strategy, or producer-computed attractor is trusted. -/
def RegionOK {n} (a b : Assignment n) (t : Fin n) (mask : Nat) : Prop :=
  (∀ r c : Fin n, maskRegion mask r c → r ≠ t) ∧
  (∀ r c : Fin n, maskRegion mask r c → r ≠ c →
    ∀ z, Legal (edgeOf a b) r z → z ≠ t ∧
      (z = c ∨ ∃ c', Legal (edgeOf a b) c c' ∧
        (z = c' ∨ maskRegion mask z c')))
instance {n} (a b : Assignment n) (t : Fin n) (mask : Nat) :
    Decidable (RegionOK a b t mask) := inferInstanceAs (Decidable (_ ∧ _))

def CertifiedLost {n} (masks : List (Fin n × Nat)) (s t : Fin n) : Prop :=
  ∃ tm, tm ∈ masks ∧ tm.1 = t ∧ ∃ c : Fin n, c ≠ s ∧ maskRegion tm.2 s c
instance {n} (masks : List (Fin n × Nat)) (s t : Fin n) :
    Decidable (CertifiedLost masks s t) :=
  inferInstanceAs (Decidable (∃ tm ∈ masks, _))

def RefinedEligible {n} (a : Assignment n) (p : List (Fin n))
    (masks : List (Fin n × Nat)) (s t : Fin n) : Prop :=
  Eligible a p s t ∧ ¬CertifiedLost masks s t
instance {n} (a : Assignment n) (p : List (Fin n))
    (masks : List (Fin n × Nat)) (s t : Fin n) :
    Decidable (RefinedEligible a p masks s t) := inferInstanceAs (Decidable (_ ∧ _))

def refinedCount {n} (a : Assignment n) (p : List (Fin n))
    (masks : List (Fin n × Nat)) : Nat :=
  ((allPairs n).filter fun st => decide (RefinedEligible a p masks st.1 st.2)).length

theorem certified_not_guaranteed {n} {a b : Assignment n}
    {masks : List (Fin n × Nat)}
    (checked : ∀ tm, tm ∈ masks → RegionOK a b tm.1 tm.2) {s t : Fin n}
    (lost : CertifiedLost masks s t) : ¬Guaranteed (edgeOf a b) s t := by
  obtain ⟨⟨u,mask⟩,member,equal,c,initial,region⟩ := lost
  simp only [Prod.fst,Prod.snd] at equal region
  subst u
  have ok := checked (t,mask) member
  exact losingRegion_not_guaranteed (losingMask a b t mask ok.1 ok.2) region initial

theorem refined_upper {n} {a b : Assignment n} {p : List (Fin n)}
    {masks : List (Fin n × Nat)} (valid : Valid a b) (agrees : Agrees p b)
    (checked : ∀ tm, tm ∈ masks → RegionOK a b tm.1 tm.2) :
    score (edgeOf a b) ≤ refinedCount a p masks := by
  classical
  apply filter_length_mono
  intro st h
  have indirect : Indirect (edgeOf a b) st.1 st.2 := of_decide_eq_true h
  exact decide_eq_true ⟨indirect_eligible valid agrees indirect,
    fun lost => certified_not_guaranteed checked lost indirect.2.2⟩

theorem full_upper {n} (a : Assignment n) (p : List (Fin n))
    (bound : Nat) (full : p.length = n) (b : Assignment n)
    (same : ∀ i : Fin n, p[i.val]'(by omega) = b i)
    (masks : List (Fin n × Nat))
    (closed : ∀ tm, tm ∈ masks → RegionOK a b tm.1 tm.2)
    (count : refinedCount a p masks ≤ bound) : UpperPrefix a p bound := by
  intro b' valid agrees
  have equal : b' = b := by
    funext i
    exact (agrees i (by omega)).trans (same i)
  subst b'
  exact Nat.le_trans (refined_upper valid agrees closed) count

#print axioms refined_upper
#print axioms full_upper
#print axioms indirect_eligible
#print axioms eligible_upper
#print axioms branch_upper
#print axioms local_upper
end Delivery.FiniteExclusion.Bounds
