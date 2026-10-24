import RowPrefixEnvelope

/-! Cached bitset losing regions and pair unions for arbitrary prescribed
degrees. Every omitted pair is justified from the actual alternating game. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

abbrev Rows (n : Nat) := Fin n → Nat

theorem bit_index_lt {bits i n : Nat} (small : bits < 2^n)
    (set : bits.testBit i = true) : i < n := by
  have lower := Nat.ge_two_pow_of_testBit set
  apply Classical.byContradiction
  intro large
  have power : 2^n ≤ 2^i := Nat.pow_le_pow_of_le (by decide) (by omega)
  omega

theorem intersect_reply {n : Nat} (lower region : Rows n)
    (small : ∀ c, lower c < 2^n) (c z : Fin n)
    (nonzero : lower c &&& (2^z.val ||| region z) ≠ 0) :
    ∃ d : Fin n, bit (lower c) d ∧ (z = d ∨ bit (region z) d) := by
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero nonzero
  have facts : (lower c).testBit i = true ∧
      ((2^z.val).testBit i = true ∨ (region z).testBit i = true) := by
    simpa only [Nat.testBit_and,Nat.testBit_or,Bool.and_eq_true,Bool.or_eq_true] using hi
  let d : Fin n := ⟨i,bit_index_lt (small c) facts.1⟩
  refine ⟨d,facts.1,?_⟩
  rcases facts.2 with captured | lost
  · exact Or.inl (Fin.ext (of_decide_eq_true (Nat.testBit_two_pow ▸ captured)))
  · exact Or.inr lost

def RegionOK {n : Nat} (upper lower good region : Rows n) (t : Fin n) : Prop :=
  (∀ c, lower c < 2^n) ∧
  region t = 0 ∧
  (∀ c z : Fin n, bit (good c) z → z ≠ t ∧
    (z = c ∨ lower c &&& (2^z.val ||| region z) ≠ 0)) ∧
  (∀ r c : Fin n, bit (region r) c → r ≠ c → upper r &&& good c = upper r)
instance {n : Nat} (upper lower good region : Rows n) (t : Fin n) :
    Decidable (RegionOK upper lower good region t) := inferInstanceAs (Decidable (_ ∧ _))

instance {n : Nat} (R : Fin n → Nat) (p : List Nat) (s t : Fin n) :
    Decidable (Legal (upperEdge R p) s t) := inferInstanceAs (Decidable (_ ∨ _))

def EnvelopeOK {n : Nat} (R : Fin n → Nat) (p : List Nat) (upper lower : Rows n) : Prop :=
  (∀ r z, Legal (upperEdge R p) r z → bit (upper r) z) ∧
  (∀ c z, bit (lower c) z → c = z ∨ known p c z)
instance {n : Nat} (R : Fin n → Nat) (p : List Nat) (upper lower : Rows n) :
    Decidable (EnvelopeOK R p upper lower) := inferInstanceAs (Decidable (_ ∧ _))

def regionCertificate {n : Nat} {D R : Fin n → Nat} {p : List Nat}
    {E : Graph (Fin n)} (valid : Prescribed D R E) (agrees : Agrees p E)
    (upper lower good region : Rows n) (t : Fin n)
    (envelope : EnvelopeOK R p upper lower)
    (checked : RegionOK upper lower good region t) : LosingRegion E t where
  region := fun r c => bit (region r) c
  nonterminal := by
    intro r c inside same
    subst r
    simpa [checked.2.1,bit] using inside
  closed := by
    intro r c inside safe z legal
    have sandwich := tight_sandwich valid agrees
    have upperbit : bit (upper r) z := envelope.1 r z
      (legal.elim Or.inl (fun edge => Or.inr (sandwich.2 r z edge)))
    have subset := congrArg (fun mask => mask.testBit z.val) (checked.2.2.2 r c inside safe)
    have goodbit : bit (good c) z := by
      simp only [Nat.testBit_and,show (upper r).testBit z.val = true from upperbit,
        Bool.true_and] at subset
      exact subset
    obtain ⟨different,capture | intersection⟩ := checked.2.2.1 c z goodbit
    · exact ⟨different,Or.inl capture⟩
    · obtain ⟨d,reply,outcome⟩ := intersect_reply lower region checked.1 c z intersection
      have reply' : Legal E c d :=
        (envelope.2 c d reply).elim Or.inl (fun edge => Or.inr (sandwich.1 c d edge))
      exact ⟨different,Or.inr ⟨d,reply',outcome⟩⟩

def except (n : Nat) (s : Fin n) : Nat := (2^n-1) ^^^ 2^s.val

theorem except_bit (s c : Fin n) : bit (except n s) c ↔ c ≠ s := by
  simp only [bit,except,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow,show decide (c.val < n) = true from decide_eq_true c.isLt]
  by_cases same : c = s
  · subst c; simp
  · have values : s.val ≠ c.val := fun equal => same (Fin.ext equal.symm)
    simp [values,same]

structure Loss (n : Nat) where
  target : Fin n
  region : Rows n
  good : Rows n

def LossExists {n : Nat} (losses : List (Loss n)) (s t : Fin n) : Prop :=
  ∃ loss ∈ losses, loss.target = t ∧ loss.region s &&& except n s ≠ 0
instance {n : Nat} (losses : List (Loss n)) (s t : Fin n) : Decidable (LossExists losses s t) :=
  inferInstanceAs (Decidable (∃ loss ∈ losses, _))

theorem loss_sound {n : Nat} {D R : Fin n → Nat} {p : List Nat}
    {E : Graph (Fin n)} (valid : Prescribed D R E) (agrees : Agrees p E)
    (upper lower : Rows n) (losses : List (Loss n))
    (envelope : EnvelopeOK R p upper lower)
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
  let cert := regionCertificate valid agrees upper lower loss.good loss.region loss.target
    envelope (checked loss member)
  rw [←target]
  exact losingRegion_not_guaranteed cert (show cert.region s c from facts.1) initial

def allowedCount {n : Nat} (allowed : Rows n) : Nat :=
  ((allPairs n).filter fun st => decide (bit (allowed st.1) st.2)).length

def CoverOK {n : Nat} (D R : Fin n → Nat) (p : List Nat)
    (allowed : Rows n) (losses : List (Loss n)) : Prop :=
  ∀ s t : Fin n, bit (allowed s) t ∨ D s < 2 ∨ R t < 2 ∨ s = t ∨
    known p s t ∨ LossExists losses s t
instance {n : Nat} (D R : Fin n → Nat) (p : List Nat)
    (allowed : Rows n) (losses : List (Loss n)) : Decidable (CoverOK D R p allowed losses) :=
  inferInstanceAs (Decidable (∀ s t : Fin n, _))

structure Bound (n : Nat) where
  allowed : Rows n
  upper : Rows n
  lower : Rows n
  losses : List (Loss n)

def BoundOK {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (cert : Bound n) : Prop :=
  EnvelopeOK R p cert.upper cert.lower ∧
  (∀ loss ∈ cert.losses, RegionOK cert.upper cert.lower loss.good loss.region loss.target) ∧
  CoverOK D R p cert.allowed cert.losses ∧ allowedCount cert.allowed ≤ bound
instance {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : Bound n) :
    Decidable (BoundOK D R p bound cert) := inferInstanceAs (Decidable (_ ∧ _))

theorem bound_sound {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (cert : Bound n) (checked : BoundOK D R p bound cert) : Upper D R p bound := by
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
  · exact False.elim (loss_sound valid agrees cert.upper cert.lower cert.losses
      checked.1 checked.2.1 lost indirect.2.2)

#print axioms regionCertificate
#print axioms bound_sound
end Delivery.RowPrefix
