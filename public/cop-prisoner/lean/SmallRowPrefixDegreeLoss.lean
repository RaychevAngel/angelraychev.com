import SmallRowPrefixCut
import RowPrefixFastEnvelope

/-! Prescribed zero-outdegree rows sharpen the optimistic game envelope.
The finite checks are transported directly to each actual completion. -/
namespace Delivery.RowPrefix.DegreeLoss
open FiniteGame Extremal DenseCombinatorics SparseSupport SmallBoolean

def ActualEnvelope (E : Graph (Fin n)) (upper lower : Rows n) : Prop :=
  (∀r z,Legal E r z → bit (upper r) z) ∧ (∀c z,bit (lower c) z → Legal E c z)

def EnvelopeOK (D R : Fin n → Nat) (p : List Nat)
    (upper lower : Rows n) (available : Nat) : Prop :=
  (∀t,bit available t ↔ used p t<R t) ∧
  (∀r,lower r=(if h:r.val<p.length then p[r.val] else 0) ||| 2^r.val) ∧
  (∀r,upper r=if r.val<p.length then lower r else
    if D r=0 then 2^r.val else available ||| 2^r.val)
instance (D R : Fin n → Nat) (p : List Nat) (upper lower : Rows n) (available : Nat) :
    Decidable (EnvelopeOK D R p upper lower available) := inferInstanceAs (Decidable (_∧_))

theorem envelope_sound (D R : Fin n → Nat) (p : List Nat) (upper lower : Rows n)
    (available : Nat) (checked : EnvelopeOK D R p upper lower available)
    {E : Graph (Fin n)} (valid : Prescribed D R E) (agrees : Agrees p E) :
    ActualEnvelope E upper lower := by
  let wide : Rows n := fun r => if r.val<p.length then lower r else available ||| 2^r.val
  have base : FastEnvelopeOK R p wide lower available := ⟨checked.1,checked.2.1,fun _ => rfl⟩
  have old := fast_envelope_sound R p wide lower available base
  have sandwich := tight_sandwich valid agrees
  constructor
  · intro r z legal
    have widebit := old.1 r z (legal.elim Or.inl (fun edge => Or.inr (sandwich.2 r z edge)))
    rw [checked.2.2 r]
    by_cases before : r.val<p.length
    · simpa only [wide,if_pos before] using widebit
    · rw [if_neg before]
      by_cases zero : D r=0
      · rw [if_pos zero]
        rcases legal with same | arrow
        · exact (bit_power r z).mpr same
        · have degree : outdegree E r=0 := (valid.2.1 r).trans zero
          exact False.elim ((card_eq_zero.mp degree) z arrow)
      · simpa only [wide,if_neg before,if_neg zero] using widebit
  · intro c z bitset
    exact (old.2 c z bitset).elim Or.inl (fun edge => Or.inr (sandwich.1 c z edge))

def regionCertificate {n : Nat} {E : Graph (Fin n)}
    (upper lower good region : Rows n) (t : Fin n)
    (envelope : ActualEnvelope E upper lower)
    (checked : RegionOK upper lower good region t) : LosingRegion E t where
  region := fun r c => bit (region r) c
  nonterminal := by
    intro r c inside same
    subst r
    simpa [checked.2.1,bit] using inside
  closed := by
    intro r c inside safe z legal
    have upperbit : bit (upper r) z := envelope.1 r z legal
    have subset := congrArg (fun mask => mask.testBit z.val) (checked.2.2.2 r c inside safe)
    have goodbit : bit (good c) z := by
      simp only [Nat.testBit_and,show (upper r).testBit z.val = true from upperbit,
        Bool.true_and] at subset
      exact subset
    obtain ⟨different,capture | intersection⟩ := checked.2.2.1 c z goodbit
    · exact ⟨different,Or.inl capture⟩
    · obtain ⟨d,reply,outcome⟩ := intersect_reply lower region checked.1 c z intersection
      have reply' : Legal E c d := envelope.2 c d reply
      exact ⟨different,Or.inr ⟨d,reply',outcome⟩⟩
theorem loss_sound {n : Nat} {E : Graph (Fin n)}
    (upper lower : Rows n) (losses : List (Loss n))
    (envelope : ActualEnvelope E upper lower)
    (checked : ∀ loss ∈ losses, RegionOK upper lower loss.good loss.region loss.target)
    {s t : Fin n} (lost : LossExists losses s t) : ¬Guaranteed E s t := by
  obtain ⟨loss,member,target,nonzero⟩ := lost
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero nonzero
  have facts : (loss.region s).testBit i = true ∧ (except n s).testBit i = true := by
    simpa only [Nat.testBit_and,Bool.and_eq_true] using hi
  have small : except n s < 2^n := by
    apply Nat.lt_pow_two_of_testBit
    intro j high
    simp only [except,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow]
    have h1 : ¬j < n := by omega
    have h2 : s.val ≠ j := by have := s.isLt; omega
    simp [h1,h2]
  let c : Fin n := ⟨i,bit_index_lt small facts.2⟩
  have initial : c ≠ s := (except_bit s c).mp facts.2
  let cert := regionCertificate upper lower loss.good loss.region loss.target
    envelope (checked loss member)
  rw [←target]
  exact losingRegion_not_guaranteed cert (show cert.region s c from facts.1) initial

def BoundOK (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : Bound n) : Prop :=
  EnvelopeOK D R p cert.upper cert.lower available ∧
  (∀loss∈cert.losses,RegionOK cert.upper cert.lower loss.good loss.region loss.target) ∧
  CoverOK D R p cert.allowed cert.losses ∧ allowedCount cert.allowed≤bound
instance (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : Bound n) :
    Decidable (BoundOK D R p bound available cert) := inferInstanceAs (Decidable (_∧_))
theorem bound_sound {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (available : Nat) (cert : Bound n) (checked : BoundOK D R p bound available cert) : Upper D R p bound := by
  intro E valid agrees
  apply Nat.le_trans ?_ checked.2.2.2
  classical
  apply filter_length_mono
  intro st counted
  have indirect : Indirect E st.1 st.2 := of_decide_eq_true counted
  have out := live_outdegree valid.1 indirect
  have inc := live_indegree indirect
  rw [valid.2.1] at out
  rw [valid.2.2] at inc
  rcases checked.2.2.1 st.1 st.2 with yes | lowout | lowin | diagonal | edge | lost
  · exact decide_eq_true yes
  · omega
  · omega
  · exact False.elim (indirect.1 diagonal)
  · exact False.elim (indirect.2.1 ((sandwich valid.1 agrees).1 _ _ edge))
  · exact False.elim (loss_sound cert.upper cert.lower cert.losses
      (envelope_sound D R p cert.upper cert.lower available checked.1 valid agrees) checked.2.1 lost indirect.2.2)

def CutBoundOK (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : CutBound n) : Prop :=
  EnvelopeOK D R p cert.upper cert.lower available ∧
  (∀loss∈cert.losses,RegionOK cert.upper cert.lower loss.good loss.region loss.target) ∧
  LostOK D R cert.lost cert.losses ∧
  eligibleCount D R+lowSum D+lowSum R≤bound+allowedCount cert.lost+degreeSum D+cornerCount D R p
instance (D R : Fin n → Nat) (p : List Nat) (bound available : Nat) (cert : CutBound n) :
    Decidable (CutBoundOK D R p bound available cert) := inferInstanceAs (Decidable (_∧_))

theorem cut_bound_sound (D R : Fin n → Nat) (p : List Nat) (bound available : Nat)
    (cert : CutBound n) (checked : CutBoundOK D R p bound available cert) : Upper D R p bound := by
  apply cut_count_sound D R p bound cert.lost
  · intro s t h
    have yes := checked.2.2.1 s t h
    exact ⟨yes.1,yes.2.1,yes.2.2.1⟩
  · intro E valid agrees s t h
    exact loss_sound cert.upper cert.lower cert.losses
      (envelope_sound D R p cert.upper cert.lower available checked.1 valid agrees)
      checked.2.1 (checked.2.2.1 s t h).2.2.2
  · exact checked.2.2.2

#print axioms envelope_sound
#print axioms bound_sound
#print axioms cut_bound_sound
end Delivery.RowPrefix.DegreeLoss
