import CyclicWindow

/-! A finite defect and a cyclic observation window have at most one relevant
lift when their combined spans are shorter than the circumference. These are
geometry lemmas only; graph moves, smoothing, and local strategies remain
separate obligations. -/
namespace Delivery.SinglePatchWindow
open CyclicArithmetic CyclicWindow

/-- The cyclic origin from which signed anchors `[-span,width]` are enumerated. -/
def anchorBase {k : Nat} (base : Fin k) (span : Nat) : Fin k :=
  shift base (k-span)

@[simp] theorem anchorBase_back {k span : Nat} (base : Fin k) (small : span≤k) :
    shift (anchorBase base span) span=base := by
  rw [anchorBase,shift_add,show k-span+span=k by omega,shift_period]

theorem anchorBase_lift {k span : Nat} (base : Fin k) (small : span≤k) (u : Nat) :
    shift (anchorBase base span) (u+span)=shift base u := by
  rw [Nat.add_comm u span,←shift_add,anchorBase_back base small]

/-- The offset is computed, not chosen from an existence proof. -/
def offset {k : Nat} (base target : Fin k) : Fin k :=
  ⟨(target.val+k-base.val)%k,Nat.mod_lt _ (by have := base.isLt; omega)⟩

theorem shift_offset {k : Nat} (base target : Fin k) :
    shift base (offset base target).val=target := by
  apply Fin.ext
  change (base.val+(target.val+k-base.val)%k)%k=target.val
  rw [Nat.add_mod_mod,show base.val+(target.val+k-base.val)=target.val+k by
    have := base.isLt; omega]
  simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,
    Nat.mod_eq_of_lt target.isLt]

/-- `Relevant` enumerates the full support interval; an actual patch may use
only some positions within that interval. -/
def Relevant {k : Nat} (base : Fin k) (width span : Nat) (origin : Fin k) : Prop :=
  Inside (anchorBase base span) (width+span) origin

def anchorIndex {k : Nat} (base : Fin k) (span : Nat) (origin : Fin k) : Fin k :=
  offset (anchorBase base span) origin

theorem relevant_iff_index {k width span : Nat} (base origin : Fin k)
    (small : width+span<k) :
    Relevant base width span origin ↔ (anchorIndex base span origin).val≤width+span := by
  constructor
  · rintro ⟨h,range,eq⟩
    have same := eq.trans (shift_offset (anchorBase base span) origin).symm
    have hv := inside_unique (anchorBase base span) (w:=k-1)
      (u:=h) (v:=(anchorIndex base span origin).val)
      (by omega) (by have := (anchorIndex base span origin).isLt; omega)
      (by have := base.isLt; omega) same
    omega
  · intro range
    exact ⟨(anchorIndex base span origin).val,range,
      shift_offset (anchorBase base span) origin⟩

theorem anchor_unique {k width span h h' : Nat} (base origin : Fin k)
    (small : width+span<k) (hh : h≤width+span) (hh' : h'≤width+span)
    (first : shift (anchorBase base span) h=origin)
    (second : shift (anchorBase base span) h'=origin) : h=h' :=
  inside_unique (anchorBase base span) hh hh' small (first.trans second.symm)

/-- Any actual overlap supplies the unique relevant anchor. -/
theorem overlap_relevant {k width span u j : Nat} (base origin : Fin k)
    (small : span≤k) (hu : u≤width) (hj : j≤span)
    (same : shift origin j=shift base u) : Relevant base width span origin := by
  let h := u+span-j
  have hj' : h+j=u+span := by dsimp [h]; omega
  refine ⟨h,by dsimp [h]; omega,?_⟩
  apply shift_injective (d:=j)
  rw [shift_add,hj',anchorBase_lift base small u]
  exact same.symm

theorem irrelevant_disjoint {k width span : Nat} (base origin : Fin k)
    (small : span≤k) (irrelevant : ¬Relevant base width span origin)
    {j : Nat} (hj : j≤span) : ¬Inside base width (shift origin j) := by
  rintro ⟨u,hu,same⟩
  exact irrelevant (overlap_relevant base origin small hu hj same.symm)

/-- Equality of a patch position and a window position is an ordinary integer
coordinate equality, with no unnoticed second lift through the cyclic seam. -/
theorem coordinates {k width span h u j : Nat} (base origin : Fin k)
    (small : width+span<k) (hh : h≤width+span)
    (anchor : shift (anchorBase base span) h=origin)
    (hu : u≤width) (hj : j≤span) :
    shift origin j=shift base u ↔ h+j=u+span := by
  have back : span≤k := by omega
  have target := anchorBase_lift base back u
  constructor
  · intro same
    have same' : shift (anchorBase base span) (h+j)=
        shift (anchorBase base span) (u+span) := by
      rw [←shift_add,anchor,target]
      exact same
    by_cases less : h+j<u+span
    · exact False.elim (shift_ne_of_lt_gap _ less (by omega) same')
    by_cases greater : u+span<h+j
    · exact False.elim (shift_ne_of_lt_gap _ greater (by omega) same'.symm)
    omega
  · intro same
    rw [←anchor,shift_add,same,target]

/-- Arbitrary type-specific patch tables can use this equivalence: the cyclic
membership test becomes membership in the single translated finite table. -/
theorem table_membership {k width span h u : Nat} (base origin : Fin k)
    (small : width+span<k) (hh : h≤width+span)
    (anchor : shift (anchorBase base span) h=origin)
    (hu : u≤width) (P : Nat → Prop) :
    (∃ j, j≤span ∧ P j ∧ shift origin j=shift base u) ↔
      ∃ j, j≤span ∧ P j ∧ h+j=u+span := by
  constructor <;> rintro ⟨j,hj,pj,eq⟩
  · exact ⟨j,hj,pj,(coordinates base origin small hh anchor hu hj).mp eq⟩
  · exact ⟨j,hj,pj,(coordinates base origin small hh anchor hu hj).mpr eq⟩

#print axioms coordinates
#print axioms irrelevant_disjoint
#print axioms table_membership
end Delivery.SinglePatchWindow
