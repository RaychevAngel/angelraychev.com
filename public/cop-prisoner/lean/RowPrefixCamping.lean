import RowPrefixCutLoss
import RowPrefixFastEnvelope

/-! Stationary-cop losing regions, checked with one bitset per messenger row.
Several target vertices may share the same closed region. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal

structure CampLoss (n : Nat) where
  cop : Fin n
  region : Nat
  targets : Nat

def CampRegionOK (upper lower : Rows n) (loss : CampLoss n) : Prop :=
  loss.region &&& loss.targets = 0 ∧
  ∀ r : Fin n, bit loss.region r → r ≠ loss.cop →
    upper r &&& loss.targets = 0 ∧
    upper r &&& (lower loss.cop ||| loss.region) = upper r
instance (upper lower : Rows n) (loss : CampLoss n) : Decidable (CampRegionOK upper lower loss) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem bits_disjoint {a b : Nat} (disjoint : a &&& b=0) (t : Fin n)
    (ha : bit a t) (hb : bit b t) : False := by
  have eq := congrArg (fun bits => bits.testBit t.val) disjoint
  simp only [Nat.testBit_and,Nat.zero_testBit,show a.testBit t.val=true from ha,
    show b.testBit t.val=true from hb] at eq
  contradiction

def campRegion {D R : Fin n → Nat} {p : List Nat} {E : Graph (Fin n)}
    (valid : Prescribed D R E) (agrees : Agrees p E)
    (upper lower : Rows n) (envelope : EnvelopeOK R p upper lower)
    (loss : CampLoss n) (checked : CampRegionOK upper lower loss)
    (t : Fin n) (target : bit loss.targets t) : LosingRegion E t where
  region := fun r c => bit loss.region r ∧ c=loss.cop
  nonterminal := by
    rintro r c ⟨inside,_⟩ rfl
    exact bits_disjoint checked.1 r inside target
  closed := by
    rintro r c ⟨inside,rfl⟩ safe z legal
    have upperbit : bit (upper r) z := envelope.1 r z
      (legal.elim Or.inl (fun edge => Or.inr ((tight_sandwich valid agrees).2 _ _ edge)))
    have row := checked.2 r inside safe
    have different : z ≠ t := by
      intro same
      subst z
      exact bits_disjoint row.1 t upperbit target
    have subset := congrArg (fun bits => bits.testBit z.val) row.2
    have choice : bit (lower loss.cop) z ∨ bit loss.region z := by
      simpa only [bit,Nat.testBit_and,Nat.testBit_or,show (upper r).testBit z.val=true from upperbit,
        Bool.true_and,Bool.or_eq_true] using subset
    refine ⟨different,?_⟩
    rcases choice with capture | remains
    · have reply : Legal E loss.cop z :=
        (envelope.2 _ _ capture).elim Or.inl (fun edge => Or.inr ((tight_sandwich valid agrees).1 _ _ edge))
      exact Or.inr ⟨z,reply,Or.inl rfl⟩
    · exact Or.inr ⟨loss.cop,legal_wait E loss.cop,Or.inr ⟨remains,rfl⟩⟩

def CampExists (losses : List (CampLoss n)) (s t : Fin n) : Prop :=
  ∃ loss ∈ losses, bit loss.region s ∧ s ≠ loss.cop ∧ bit loss.targets t
instance (losses : List (CampLoss n)) (s t : Fin n) : Decidable (CampExists losses s t) :=
  inferInstanceAs (Decidable (∃ loss ∈ losses, _))

theorem camp_loss_sound {D R : Fin n → Nat} {p : List Nat} {E : Graph (Fin n)}
    (valid : Prescribed D R E) (agrees : Agrees p E)
    (upper lower : Rows n) (envelope : EnvelopeOK R p upper lower)
    (losses : List (CampLoss n)) (checked : ∀ loss ∈ losses, CampRegionOK upper lower loss)
    {s t : Fin n} (lost : CampExists losses s t) : ¬Guaranteed E s t := by
  obtain ⟨loss,member,inside,safe,target⟩ := lost
  exact losingRegion_not_guaranteed (campRegion valid agrees upper lower envelope loss (checked loss member) t target)
    ⟨inside,rfl⟩ (Ne.symm safe)

structure MixedBound (n : Nat) where
  lost : Rows n
  upper : Rows n
  lower : Rows n
  available : Nat
  camps : List (CampLoss n)
  losses : List (Loss n)

def MixedBoundOK (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : MixedBound n) : Prop :=
  FastEnvelopeOK R p cert.upper cert.lower cert.available ∧
  (∀ loss ∈ cert.camps, CampRegionOK cert.upper cert.lower loss) ∧
  (∀ loss ∈ cert.losses, RegionOK cert.upper cert.lower loss.good loss.region loss.target) ∧
  (∀ s t, bit (cert.lost s) t → 2 ≤ D s ∧ 2 ≤ R t ∧ s ≠ t ∧
    (CampExists cert.camps s t ∨ LossExists cert.losses s t)) ∧
  eligibleCount D R + lowSum D + lowSum R ≤
    bound + allowedCount cert.lost + degreeSum D + cornerCount D R p
instance (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : MixedBound n) :
    Decidable (MixedBoundOK D R p bound cert) := inferInstanceAs (Decidable (_ ∧ _))

theorem mixed_bound_sound (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (cert : MixedBound n) (checked : MixedBoundOK D R p bound cert) : Upper D R p bound := by
  apply cut_count_sound D R p bound cert.lost
  · intro s t h
    have yes := checked.2.2.2.1 s t h
    exact ⟨yes.1,yes.2.1,yes.2.2.1⟩
  · intro E valid agrees s t h
    have env := fast_envelope_sound R p cert.upper cert.lower cert.available checked.1
    rcases (checked.2.2.2.1 s t h).2.2.2 with camp | game
    · exact camp_loss_sound valid agrees cert.upper cert.lower env cert.camps checked.2.1 camp
    · exact loss_sound valid agrees cert.upper cert.lower cert.losses env checked.2.2.1 game
  · exact checked.2.2.2.2

#print axioms camp_loss_sound
#print axioms mixed_bound_sound
end Delivery.RowPrefix
