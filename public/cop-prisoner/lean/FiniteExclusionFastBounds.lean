import FiniteExclusionBitset

/-! Cached pair-cover certificates. Every omitted pair has an explicit local
camping or closed-region reason; the union is counted only once. -/
namespace Delivery.FiniteExclusion.FastBounds
open FiniteGame Extremal Bounds PrefixBounds Bitset

abbrev SourceWitness := Fin 9 × Fin 9
abbrev RecipientWitness := Fin 9 × Fin 9 × Fin 9

def SourceOK (a : Assignment 9) (p : List (Fin 9)) (w : SourceWitness) : Prop :=
  ∃ h : w.1.val < p.length, w.2 ≠ w.1 ∧
    lowerLegal a p w.2 (a w.1) ∧ lowerLegal a p w.2 p[w.1.val]
instance (a : Assignment 9) (p : List (Fin 9)) (w : SourceWitness) : Decidable (SourceOK a p w) :=
  inferInstanceAs (Decidable (∃ h : w.1.val < p.length, _))

def RecipientOK (a : Assignment 9) (p : List (Fin 9)) (w : RecipientWitness) : Prop :=
  ∃ h : w.2.1.val < p.length, p[w.2.1.val] = w.1 ∧
    (∀ z, a z = w.1 → lowerLegal a p w.2.2 z) ∧ lowerLegal a p w.2.2 w.2.1
instance (a : Assignment 9) (p : List (Fin 9)) (w : RecipientWitness) : Decidable (RecipientOK a p w) :=
  inferInstanceAs (Decidable (∃ h : w.2.1.val < p.length, _))

def SourceListed (sources : List SourceWitness) (s : Fin 9) : Prop :=
  ∃ w ∈ sources, w.1 = s
instance (sources : List SourceWitness) (s : Fin 9) : Decidable (SourceListed sources s) :=
  inferInstanceAs (Decidable (∃ w ∈ sources, _))

def RecipientListed (recipients : List RecipientWitness) (s t : Fin 9) : Prop :=
  ∃ w ∈ recipients, w.1 = t ∧ w.2.2 ≠ s
instance (recipients : List RecipientWitness) (s t : Fin 9) : Decidable (RecipientListed recipients s t) :=
  inferInstanceAs (Decidable (∃ w ∈ recipients, _))

def MaskLost (masks : List (Fin 9 × Nat)) (s t : Fin 9) : Prop :=
  ∃ tm ∈ masks, tm.1 = t ∧ row tm.2 s &&& (511 ^^^ 2^s.val) ≠ 0
instance (masks : List (Fin 9 × Nat)) (s t : Fin 9) : Decidable (MaskLost masks s t) :=
  inferInstanceAs (Decidable (∃ tm ∈ masks, _))

theorem except_bit (s c : Fin 9) :
    (511 ^^^ 2^s.val).testBit c.val = true ↔ c ≠ s := by
  revert s c
  decide +kernel

theorem mask_lost_sound {masks : List (Fin 9 × Nat)} {s t : Fin 9}
    (lost : MaskLost masks s t) : CertifiedLost masks s t := by
  obtain ⟨tm,member,target,nonzero⟩ := lost
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero nonzero
  have facts : (row tm.2 s).testBit i = true ∧ (511 ^^^ 2^s.val).testBit i = true := by
    simpa only [Nat.testBit_and,Bool.and_eq_true] using hi
  have small : row tm.2 s < 512 := by
    have bound : row tm.2 s ≤ 511 := Nat.and_le_right
    omega
  let c : Fin 9 := ⟨i,bit_index_lt small facts.1⟩
  refine ⟨tm,member,target,c,(except_bit s c).mp facts.2,?_⟩
  change tm.2.testBit (s.val*9+c.val) = true
  rw [←row_bit]
  exact facts.1

theorem source_listed_sound {a : Assignment 9} {p : List (Fin 9)}
    {sources : List SourceWitness} (checks : ∀ w ∈ sources, SourceOK a p w)
    {s : Fin 9} (listed : SourceListed sources s) : SourceCamp a p s := by
  obtain ⟨⟨u,c⟩,member,equal⟩ := listed
  change u = s at equal
  subst u
  obtain ⟨h,initial,first,second⟩ := checks (s,c) member
  exact ⟨h,c,initial,first,second⟩

theorem recipient_listed_sound {a : Assignment 9} {p : List (Fin 9)}
    {recipients : List RecipientWitness} (checks : ∀ w ∈ recipients, RecipientOK a p w)
    {s t : Fin 9} (listed : RecipientListed recipients s t) : RecipientCamp a p s t := by
  obtain ⟨⟨v,u,c⟩,member,equal,initial⟩ := listed
  change v = t at equal
  subst v
  obtain ⟨h,target,first,second⟩ := checks (t,u,c) member
  exact ⟨u,h,target,c,initial,first,second⟩

def CoverOK (a : Assignment 9) (p : List (Fin 9)) (allowed : Rows)
    (sources : List SourceWitness) (recipients : List RecipientWitness)
    (masks : List (Fin 9 × Nat)) : Prop :=
  ∀ s t : Fin 9, graph allowed s t ∨ s = t ∨ KnownEdge a p s t ∨
    SourceListed sources s ∨ RecipientListed recipients s t ∨ MaskLost masks s t
instance (a : Assignment 9) (p : List (Fin 9)) (allowed : Rows)
    (sources : List SourceWitness) (recipients : List RecipientWitness)
    (masks : List (Fin 9 × Nat)) : Decidable (CoverOK a p allowed sources recipients masks) :=
  inferInstanceAs (Decidable (∀ s t : Fin 9, _))

def allowedCount (allowed : Rows) : Nat :=
  ((allPairs 9).filter fun st => decide (graph allowed st.1 st.2)).length

theorem upper (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (allowed : Rows)
    (sources : List SourceWitness) (recipients : List RecipientWitness)
    (masks : List (Fin 9 × Nat))
    (sourceChecks : ∀ w ∈ sources, SourceOK a p w)
    (recipientChecks : ∀ w ∈ recipients, RecipientOK a p w)
    (regionChecks : ∀ tm ∈ masks, PrefixRegionOK a p tm.1 tm.2)
    (cover : CoverOK a p allowed sources recipients masks)
    (count : allowedCount allowed ≤ bound) : UpperPrefix a p bound := by
  intro b valid agrees
  apply Nat.le_trans ?_ count
  classical
  apply filter_length_mono
  intro st h
  have indirect : Indirect (edgeOf a b) st.1 st.2 := of_decide_eq_true h
  have eligible := indirect_eligible valid agrees indirect
  rcases cover st.1 st.2 with yes | diagonal | edge | source | recipient | loss
  · exact decide_eq_true yes
  · exact False.elim (indirect.1 diagonal)
  · exact False.elim (eligible.2.1 edge)
  · exact False.elim (eligible.2.2.1 (source_listed_sound sourceChecks source))
  · exact False.elim (eligible.2.2.2 (recipient_listed_sound recipientChecks recipient))
  · exact False.elim (certified_prefix_not_guaranteed valid agrees regionChecks
      (mask_lost_sound loss) indirect.2.2)

#print axioms mask_lost_sound
#print axioms upper
end Delivery.FiniteExclusion.FastBounds
