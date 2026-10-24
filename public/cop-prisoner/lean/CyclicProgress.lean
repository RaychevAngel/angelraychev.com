import SinglePatchWindow
import CyclicSigned

/-! Exact cyclic distances decrease under bounded directed steps. These
lemmas use the canonical offset and do not assume away the cyclic seam. -/
namespace Delivery.CyclicProgress
open CyclicArithmetic CyclicWindow SinglePatchWindow CyclicSigned

theorem offset_shift {k : Nat} (base : Fin k) (d : Nat) (small : d<k) :
    (offset base (shift base d)).val=d := by
  apply inside_unique base (w:=k-1)
  · have := (offset base (shift base d)).isLt; omega
  · omega
  · have := base.isLt; omega
  · exact shift_offset base (shift base d)

theorem offset_of_shift {k : Nat} (base target : Fin k) (d : Nat)
    (small : d<k) (reaches : shift base d=target) :
    (offset base target).val=d := by
  rw [←reaches]
  exact offset_shift base d small

theorem backward {k : Nat} (positive : 0<k) (base s : Fin k) (d : Nat)
    (bounded : d≤(offset base s).val) :
    (offset base (wrap positive ((s.val : Int)-(d : Int)))).val=
      (offset base s).val-d := by
  apply offset_of_shift base _ ((offset base s).val-d)
  · have := (offset base s).isLt; omega
  · apply shift_injective (d:=d)
    rw [shift_add,show (offset base s).val-d+d=(offset base s).val by omega,
      shift_offset,←wrap_shift,show (s.val : Int)-(d : Int)+(d : Int)=(s.val : Int) by omega,
      wrap_fin]

theorem forward {k : Nat} (s target : Fin k) (d : Nat)
    (bounded : d≤(offset s target).val) :
    (offset (shift s d) target).val=(offset s target).val-d := by
  apply offset_of_shift (shift s d) target ((offset s target).val-d)
  · have := (offset s target).isLt; omega
  · rw [shift_add,show d+((offset s target).val-d)=(offset s target).val by omega,
      shift_offset]

#print axioms backward
#print axioms forward
end Delivery.CyclicProgress
