import RowPrefixLoss

namespace Delivery.RowPrefix
open FiniteGame

def FastEnvelopeOK (R : Fin n → Nat) (p : List Nat)
    (upper lower : Rows n) (available : Nat) : Prop :=
  (∀ t, bit available t ↔ used p t < R t) ∧
  (∀ r, lower r = (if h : r.val < p.length then p[r.val] else 0) ||| 2^r.val) ∧
  (∀ r, upper r = if r.val < p.length then lower r else available ||| 2^r.val)
instance (R : Fin n → Nat) (p : List Nat) (upper lower : Rows n) (available : Nat) :
    Decidable (FastEnvelopeOK R p upper lower available) := inferInstanceAs (Decidable (_ ∧ _))

theorem bit_self (s : Fin n) : bit (2^s.val) s := by simp [bit]
theorem bit_power (s t : Fin n) : bit (2^s.val) t ↔ s = t := by
  simp [bit,Nat.testBit_two_pow,Fin.ext_iff]

theorem fast_envelope_sound (R : Fin n → Nat) (p : List Nat)
    (upper lower : Rows n) (available : Nat)
    (checked : FastEnvelopeOK R p upper lower available) : EnvelopeOK R p upper lower := by
  have lo (r z : Fin n) : bit (lower r) z ↔ r=z ∨ known p r z := by
    rw [checked.2.1 r]
    simp only [bit,Nat.testBit_or,Bool.or_eq_true]
    have power := bit_power r z
    change (Nat.testBit (2^r.val) z.val = true ↔ r=z) at power
    rw [power]
    by_cases before : r.val < p.length
    · rw [dif_pos before]
      constructor
      · rintro (edge | same)
        · exact Or.inr ⟨before,edge⟩
        · exact Or.inl same
      · rintro (same | ⟨_,edge⟩)
        · exact Or.inr same
        · exact Or.inl edge
    · rw [dif_neg before]
      simp only [Nat.zero_testBit,Bool.false_eq_true,false_or]
      exact ⟨Or.inl,fun h => h.elim id (fun edge => False.elim (before edge.1))⟩
  refine ⟨?_,fun c z h => (lo c z).mp h⟩
  intro r z legal
  rw [checked.2.2 r]
  by_cases before : r.val < p.length
  · rw [if_pos before]
    apply (lo r z).mpr
    rcases legal with same | known | future
    · exact Or.inl same
    · exact Or.inr known
    · omega
  · rw [if_neg before]
    simp only [bit,Nat.testBit_or,Bool.or_eq_true]
    rcases legal with same | known | future
    · exact Or.inr ((bit_power r z).mpr same)
    · exact False.elim (before known.1)
    · exact Or.inl ((checked.1 z).mpr future.2.2)

#print axioms fast_envelope_sound
end Delivery.RowPrefix
