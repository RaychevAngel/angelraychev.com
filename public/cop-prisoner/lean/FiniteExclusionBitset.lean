import FiniteExclusionPrefixBounds
import Init.Data.Nat.Bitwise.Lemmas

/-! Bitset closure certificates for nine-vertex finite exclusions. The kernel
checks the bit operations; generic lemmas recover every quantified game reply. -/
namespace Delivery.FiniteExclusion.Bitset
open FiniteGame

abbrev Rows := Fin 9 → Nat

def graph (rows : Rows) : Graph (Fin 9) :=
  fun s t => (rows s).testBit t.val = true
instance (rows : Rows) : DecidableRel (graph rows) := fun _ _ => inferInstanceAs (Decidable (_ = true))

def row (mask : Nat) (s : Fin 9) : Nat := (mask >>> (s.val*9)) &&& 511

theorem row_bit (mask : Nat) (s c : Fin 9) :
    (row mask s).testBit c.val = mask.testBit (s.val*9+c.val) := by
  simp only [row,Nat.testBit_and,Nat.testBit_shiftRight]
  have limit : (511 : Nat).testBit c.val = true := by
    change (2^9-1 : Nat).testBit c.val = true
    simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact c.isLt
  rw [limit,Bool.and_true]

theorem bit_index_lt {bits i : Nat} (bound : bits < 512)
    (set : bits.testBit i = true) : i < 9 := by
  have lower := Nat.ge_two_pow_of_testBit set
  apply Classical.byContradiction
  intro high
  have powers : 2^9 ≤ 2^i := Nat.pow_le_pow_of_le (by decide) (by omega)
  omega

theorem intersect_reply (lower : Rows) (small : ∀ c, lower c < 512)
    (mask : Nat) (c z : Fin 9)
    (intersection : lower c &&& (2^z.val ||| row mask z) ≠ 0) :
    ∃ d : Fin 9, graph lower c d ∧ (z = d ∨ maskRegion mask z d) := by
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero intersection
  have facts : (lower c).testBit i = true ∧
      ((2^z.val).testBit i = true ∨ (row mask z).testBit i = true) := by
    simpa only [Nat.testBit_and,Nat.testBit_or,Bool.and_eq_true,Bool.or_eq_true] using hi
  let d : Fin 9 := ⟨i,bit_index_lt (small c) facts.1⟩
  refine ⟨d,facts.1,?_⟩
  rcases facts.2 with captured | lose
  · apply Or.inl
    apply Fin.ext
    exact of_decide_eq_true (Nat.testBit_two_pow ▸ captured)
  · apply Or.inr
    change mask.testBit (z.val*9+d.val) = true
    rw [←row_bit]
    exact lose

def RegionOK (upper lower : Rows) (t : Fin 9) (mask : Nat) : Prop :=
  (∀ c, lower c < 512) ∧
  (∀ r, (upper r).testBit r.val = true) ∧
  row mask t = 0 ∧
  (∀ r c : Fin 9, maskRegion mask r c → r ≠ c →
    ∀ z : Fin 9, graph upper r z → z ≠ t ∧
      (z = c ∨ lower c &&& (2^z.val ||| row mask z) ≠ 0))
instance (upper lower : Rows) (t : Fin 9) (mask : Nat) :
    Decidable (RegionOK upper lower t mask) := inferInstanceAs (Decidable (_ ∧ _))

def certificate (upper lower : Rows) (t : Fin 9) (mask : Nat)
    (checked : RegionOK upper lower t mask) :
    RobustLosingRegion.Certificate (graph upper) (graph lower) t where
  region := maskRegion mask
  nonterminal := by
    intro r c inside same
    subst r
    change mask.testBit (t.val*9+c.val) = true at inside
    rw [←row_bit,checked.2.2.1] at inside
    simp at inside
  closed := by
    intro r c inside safe z legal
    have edge : graph upper r z := by
      rcases legal with same | edge
      · subst z; exact checked.2.1 r
      · exact edge
    obtain ⟨different,captured | intersection⟩ := checked.2.2.2 r c inside safe z edge
    · exact ⟨different,Or.inl captured⟩
    · obtain ⟨d,reply,outcome⟩ := intersect_reply lower checked.1 mask c z intersection
      exact ⟨different,Or.inr ⟨d,Or.inr reply,outcome⟩⟩

theorem prefix_ok (a : Assignment 9) (p : List (Fin 9))
    (upper lower : Rows)
    (upperCover : ∀ r z, Legal (PrefixBounds.upperEdge a p) r z → graph upper r z)
    (lowerCover : ∀ c z, graph lower c z → lowerLegal a p c z)
    (t : Fin 9) (mask : Nat) (checked : RegionOK upper lower t mask) :
    PrefixBounds.PrefixRegionOK a p t mask := by
  constructor
  · exact (certificate upper lower t mask checked).nonterminal
  · intro r c inside safe z legal
    obtain ⟨different,captured | intersection⟩ :=
      checked.2.2.2 r c inside safe z (upperCover r z legal)
    · exact ⟨different,Or.inl captured⟩
    · obtain ⟨d,reply,outcome⟩ := intersect_reply lower checked.1 mask c z intersection
      exact ⟨different,Or.inr ⟨d,lowerCover c d reply,outcome⟩⟩

/-- A cached set of safe messenger destinations for each cop position.
The row subset test covers all messenger moves in one bit operation. -/
def FastRegionOK (upper lower good : Rows) (t : Fin 9) (mask : Nat) : Prop :=
  (∀ c, lower c < 512) ∧
  (∀ r, (upper r).testBit r.val = true) ∧
  row mask t = 0 ∧
  (∀ c z : Fin 9, graph good c z → z ≠ t ∧
    (z = c ∨ lower c &&& (2^z.val ||| row mask z) ≠ 0)) ∧
  (∀ r c : Fin 9, maskRegion mask r c → r ≠ c →
    upper r &&& good c = upper r)
instance (upper lower good : Rows) (t : Fin 9) (mask : Nat) :
    Decidable (FastRegionOK upper lower good t mask) := inferInstanceAs (Decidable (_ ∧ _))

theorem fast_sound (upper lower good : Rows) (t : Fin 9) (mask : Nat)
    (checked : FastRegionOK upper lower good t mask) : RegionOK upper lower t mask := by
  refine ⟨checked.1,checked.2.1,checked.2.2.1,?_⟩
  intro r c inside safe z edge
  have subset := congrArg (fun bits : Nat => bits.testBit z.val)
    (checked.2.2.2.2 r c inside safe)
  have goodbit : graph good c z := by
    simp only [Nat.testBit_and,show (upper r).testBit z.val = true from edge,
      Bool.true_and] at subset
    exact subset
  exact checked.2.2.2.1 c z goodbit

#print axioms fast_sound
#print axioms prefix_ok
#print axioms certificate
end Delivery.FiniteExclusion.Bitset
