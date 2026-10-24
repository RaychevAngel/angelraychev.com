import CircleConstruction
import CirclePrefixCounting

/-! Closed-form exact budgets for the guarded five-offset circle. -/
namespace Delivery.CircleGuardedConstruction
open FiniteGame Extremal DenseCombinatorics CirclePropagation CircleEnvelope

/-- The zero offset represents waiting and is removed from the row degree. -/
def degree (n h : Nat) : Nat :=
  2*((n-h+1)/4)+min ((n-h+1)%4) 2+1-(if 2*h-1≤n-h then 1 else 0)-1

theorem allowed_count {n h : Nat} (hh : 7≤h) (residue : h%4=3)
    (room : 2*h+2≤n) :
    card (fun d : Fin n => CircleGuarded.Allowed n h d.val)-1=degree n h := by
  have equal := card_congr (P := fun d : Fin n => CircleGuarded.Allowed n h d.val)
    (Q := CirclePrefixCounting.allowed h) (fun d => by
      simp only [CircleGuarded.Allowed,CircleEnvelope.Allowed,CirclePrefixCounting.allowed,
        CircleCounting.periodic,d.isLt,true_and]
      constructor
      · rintro ⟨⟨hp,ne⟩,small⟩
        exact ⟨small,by simpa only [or_assoc] using hp,ne⟩
      · rintro ⟨small,hp,ne⟩
        exact ⟨⟨by simpa only [or_assoc] using hp,ne⟩,small⟩)
  rw [equal,CirclePrefixCounting.allowed_count hh residue room]
  rfl

theorem arcCount {n h : Nat} (hh : 7≤h) (residue : h%4=3)
    (room : 2*h+2≤n) :
    Extremal.arcCount (Envelope (n := n) (CircleGuarded.Allowed n h))=n*degree n h := by
  rw [CircleConstruction.envelope_arcCount _ (fun _ h => h.1.1)
    (CircleGuarded.zero_allowed hh room),allowed_count hh residue room]

/-- The construction is the lexicographic optional-arrow prefix of the
literal five-offset base and guarded envelope. -/
theorem maximum {n h m : Nat} (hh : 7≤h) (residue : h%4=3)
    (room : 2*h+2≤n) (coprime : Nat.Coprime n h)
    (low : 5*n≤m) (high : m≤n*degree n h) : IsMaximum n m (n*(n-1)-m) := by
  apply CircleConstruction.guarded_maximum hh residue room coprime low
  rwa [allowed_count hh residue room]

#print axioms maximum
end Delivery.CircleGuardedConstruction
