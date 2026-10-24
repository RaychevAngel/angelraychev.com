import CyclicArithmetic

/-! Integer lifts of cyclic columns, with explicit short-gap injectivity.
The chosen representative interval starts at -2 for the odd defect patches. -/
namespace Delivery.CyclicSigned
open CyclicArithmetic

def wrap {k : Nat} (positive : 0<k) (x : Int) : Fin k :=
  ⟨(x % (k : Int)).toNat,by
    have := Int.emod_nonneg x (show (k : Int)≠0 by omega)
    have := Int.emod_lt_of_pos x (show 0<(k : Int) by omega)
    omega⟩

@[simp] theorem wrap_val {k : Nat} (positive : 0<k) (x : Int) :
    ((wrap positive x).val : Int)=x%(k : Int) := by
  have := Int.emod_nonneg x (show (k : Int)≠0 by omega)
  dsimp [wrap]
  omega

theorem wrap_eq_iff {k : Nat} (positive : 0<k) (x y : Int) :
    wrap positive x=wrap positive y ↔ x%(k : Int)=y%(k : Int) := by
  constructor
  · intro same
    have := congrArg (fun i : Fin k => (i.val : Int)) same
    simpa only [wrap_val] using this
  · intro same
    apply Fin.ext
    dsimp [wrap]
    exact congrArg Int.toNat same

theorem injective_of_gap {k : Nat} (positive : 0<k) {x y : Int}
    (right : x<y+(k : Int)) (left : y<x+(k : Int))
    (same : wrap positive x=wrap positive y) : x=y := by
  have modEq := (wrap_eq_iff positive x y).mp same
  by_cases lt : x<y
  · have zero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp modEq.symm
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at zero
    omega
  · have zero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp modEq
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at zero
    omega

@[simp] theorem wrap_fin {k : Nat} (positive : 0<k) (i : Fin k) :
    wrap positive (i.val : Int)=i := by
  apply Fin.ext
  dsimp [wrap]
  rw [Int.emod_eq_of_lt (by omega) (by have := i.isLt; omega)]
  rfl

theorem wrap_shift {k : Nat} (positive : 0<k) (x : Int) (d : Nat) :
    wrap positive (x+(d : Int))=shift (wrap positive x) d := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [wrap_val]
  change (x+(d : Int))%(k : Int)=(((wrap positive x).val+d)%k : Nat)
  rw [Int.natCast_emod,Int.natCast_add,wrap_val,Int.emod_add_emod]

def representative {k : Nat} (i : Fin k) : Int :=
  if i.val+2<k then (i.val : Int) else (i.val : Int)-(k : Int)

theorem representative_bounds {k : Nat} (large : 3≤k) (i : Fin k) :
    -2≤representative i ∧ representative i≤(k : Int)-3 := by
  have := i.isLt
  unfold representative
  split <;> omega

@[simp] theorem wrap_representative {k : Nat} (positive : 0<k) (i : Fin k) :
    wrap positive (representative i)=i := by
  unfold representative
  split
  · exact wrap_fin positive i
  · have same : wrap positive ((i.val : Int)-(k : Int))=wrap positive (i.val : Int) := by
      apply (wrap_eq_iff positive _ _).mpr
      simp only [Int.sub_emod,Int.emod_self,Int.sub_zero,Int.emod_emod]
    exact same.trans (wrap_fin positive i)

theorem representative_wrap {k : Nat} (large : 3≤k) (x : Int)
    (low : -2≤x) (high : x≤(k : Int)-3) :
    representative (wrap (by omega : 0<k) x)=x := by
  have bounds := representative_bounds large (wrap (by omega : 0<k) x)
  apply injective_of_gap (by omega : 0<k) (by omega) (by omega)
  exact wrap_representative _ _

#print axioms injective_of_gap
#print axioms representative_wrap
end Delivery.CyclicSigned
