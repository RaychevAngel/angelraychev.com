import TwelveHubCounts

/-! Equal-weight guide codes from an explicit finite mask inventory. The
capacity table is checked for all guide counts through eight. -/
namespace Delivery.TwelveHubCodes
open DenseCombinatorics

def weight (g mask : Nat) : Nat := ((List.finRange g).filter fun j => mask.testBit j.val).length
def inventory (g r : Nat) : List Nat := (List.range (2^g)).filter fun mask => weight g mask == r
def capacity (g r : Nat) : Nat :=
  (match g with
  | 0 => [1] | 1 => [1,1] | 2 => [1,2,1] | 3 => [1,3,3,1]
  | 4 => [1,4,6,4,1] | 5 => [1,5,10,10,5,1]
  | 6 => [1,6,15,20,15,6,1] | 7 => [1,7,21,35,35,21,7,1]
  | 8 => [1,8,28,56,70,56,28,8,1] | _ => []).getD r 0

theorem inventory_size {g r : Nat} (hg : g≤8) (hr : r≤g) :
    (inventory g r).length=capacity g r := by
  have checked : ∀ g r : Fin 9, (inventory g.val r.val).length=capacity g.val r.val := by
    decide +kernel
  exact checked ⟨g,by omega⟩ ⟨r,by omega⟩

theorem inventory_nodup (g r : Nat) : (inventory g r).Nodup := List.nodup_range.filter _
theorem inventory_mem {g r mask : Nat} (member : mask∈inventory g r) :
    mask<2^g ∧ weight g mask=r := by
  simpa [inventory] using member

def mask {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r) (x : Fin b) : Nat :=
  (inventory g r)[x.val]'(by rw [inventory_size hg hr]; exact Nat.lt_of_lt_of_le x.isLt room)

theorem mask_mem {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r) (x : Fin b) :
    mask hg hr room x∈inventory g r := List.getElem_mem _

theorem mask_injective {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r)
    (x y : Fin b) (same : mask hg hr room x=mask hg hr room y) : x=y := by
  apply Fin.ext
  exact (List.getElem_inj (inventory_nodup g r)).mp same

def assigned {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r) (x : Fin b) (j : Fin g) : Prop :=
  (mask hg hr room x).testBit j.val=true

instance {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r) (x : Fin b) (j : Fin g) :
    Decidable (assigned hg hr room x j) := inferInstanceAs (Decidable (_=true))

theorem assigned_weight {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r) (x : Fin b) :
    card (assigned hg hr room x)=r := by
  have h := (inventory_mem (mask_mem hg hr room x)).2
  rw [card_eq]
  change ((List.finRange g).filter (fun j => decide ((mask hg hr room x).testBit j.val=true))).length=r
  simpa only [Bool.decide_eq_true,weight] using h

theorem equal_card_subset {g : Nat} (P Q : Fin g → Prop)
    (same : card P=card Q) (subset : ∀ j, P j → Q j) : ∀ j, Q j → P j := by
  have partition := card_partition Q P
  have common : card (fun j => Q j ∧ P j)=card P :=
    card_congr (fun j => ⟨And.right,fun h => ⟨subset j h,h⟩⟩)
  rw [common] at partition
  have zero : card (fun j => Q j ∧ ¬P j)=0 := by omega
  intro j member
  apply Classical.byContradiction
  intro no
  exact (card_eq_zero.mp zero) j ⟨member,no⟩

theorem bit_ext {g a b : Nat} (ha : a<2^g) (hb : b<2^g)
    (same : ∀ j : Fin g, a.testBit j.val=true ↔ b.testBit j.val=true) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases small : i<g
  · exact Bool.eq_iff_iff.mpr (same ⟨i,small⟩)
  · have power : 2^g≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha power),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb power)]

theorem assigned_difference {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r)
    (x y : Fin b) (different : x≠y) : ∃ j, assigned hg hr room x j ∧ ¬assigned hg hr room y j := by
  apply Classical.byContradiction
  intro absent
  have subset : ∀ j, assigned hg hr room x j → assigned hg hr room y j := by
    intro j yes
    apply Classical.byContradiction
    intro no
    exact absent ⟨j,yes,no⟩
  have reverse := equal_card_subset (assigned hg hr room x) (assigned hg hr room y)
    ((assigned_weight hg hr room x).trans (assigned_weight hg hr room y).symm) subset
  apply different
  apply mask_injective hg hr room x y
  exact bit_ext (inventory_mem (mask_mem hg hr room x)).1
    (inventory_mem (mask_mem hg hr room y)).1 (fun j => ⟨subset j,reverse j⟩)

theorem two_of_card {g : Nat} (P : Fin g → Prop) (large : 2≤card P) :
    ∃ j l, P j ∧ P l ∧ j≠l := by
  obtain ⟨j,yes⟩ := card_positive.mp (by omega : 0<card P)
  apply Classical.byContradiction
  intro absent
  have subset : ∀ l, P l → l=j := by
    intro l hl
    apply Classical.byContradiction
    intro no
    exact absent ⟨j,l,yes,hl,Ne.symm no⟩
  have bound := card_mono subset
  rw [SparseDeletion.card_singleton] at bound
  omega

theorem assigned_two {g r b : Nat} (hg : g≤8) (hr : r≤g) (room : b≤capacity g r)
    (low : 2≤r) (x : Fin b) : ∃ j l, assigned hg hr room x j ∧ assigned hg hr room x l ∧ j≠l := by
  apply two_of_card
  rw [assigned_weight hg hr room x]
  exact low

theorem maximum {g b r m : Nat} (hg : g≤8) (lowr : 2≤r) (hr : r≤g)
    (room : b≤capacity g r)
    (low : 106+22*g+(19+r)*b≤m)
    (high : m≤106+22*g+(19+r)*b+b*(g+b-1)) :
    Extremal.IsMaximum (12+g+b) m ((12+g+b)*(12+g+b-1)-m) :=
  TwelveHubCounts.maximum hg (by omega) (assigned hg hr room)
    (assigned_weight hg hr room) (assigned_two hg hr room lowr)
    (assigned_difference hg hr room) low high

#print axioms inventory_size
#print axioms maximum
end Delivery.TwelveHubCodes
