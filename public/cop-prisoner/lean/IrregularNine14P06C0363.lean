import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0106

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21780 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 268 81 48 70 198 326), lower := (rows 35 131 44 268 81 48 64 128 256), losses := [] }

theorem u21780 : Upper (D 6) (R 6) [34,129,40,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21780 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21781 : Route 9 := (fun mask => (mask,id))

def c21781 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21781 : Upper (D 6) (R 6) [34,129,40,260,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,65,64] 13 (by decide) (choices 1) [2,4,16] r21781 c21781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6403
  · exact u6404
  · exact u6405

def b21782 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 268 82 33 84 212 340), lower := (rows 35 131 44 268 82 33 64 128 256), losses := [] }

theorem u21782 : Upper (D 6) (R 6) [34,129,40,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21783 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 268 82 36 81 209 337), lower := (rows 35 131 44 268 82 36 64 128 256), losses := [] }

theorem u21783 : Upper (D 6) (R 6) [34,129,40,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21784 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 268 82 48 69 197 325), lower := (rows 35 131 44 268 82 48 64 128 256), losses := [] }

theorem u21784 : Upper (D 6) (R 6) [34,129,40,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21784 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21785 : Route 9 := (fun mask => (mask,id))

def c21785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21785 : Upper (D 6) (R 6) [34,129,40,260,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,66,64] 13 (by decide) (choices 1) [1,4,16] r21785 c21785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6406
  · exact u6407
  · exact u6408

def b21786 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 268 84 33 82 210 338), lower := (rows 35 131 44 268 84 33 64 128 256), losses := [] }

theorem u21786 : Upper (D 6) (R 6) [34,129,40,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21787 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 268 84 34 81 209 337), lower := (rows 35 131 44 268 84 34 64 128 256), losses := [] }

theorem u21787 : Upper (D 6) (R 6) [34,129,40,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21788 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 131 44 268 84 48 67 195 323), lower := (rows 35 131 44 268 84 48 64 128 256), losses := [] }

theorem u21788 : Upper (D 6) (R 6) [34,129,40,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21788 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21789 : Route 9 := (fun mask => (mask,id))

def c21789 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21789 : Upper (D 6) (R 6) [34,129,40,260,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,68,64] 13 (by decide) (choices 1) [1,2,16] r21789 c21789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6409
  · exact u6410
  · exact u6411

def b21790 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 280 21 34 68 196 324), lower := (rows 35 131 44 280 21 34 64 128 256), losses := [] }

theorem u21790 : Upper (D 6) (R 6) [34,129,40,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21791 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 131 44 280 21 36 66 194 322), lower := (rows 35 131 44 280 21 36 64 128 256), losses := [] }

theorem u21791 : Upper (D 6) (R 6) [34,129,40,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21792 : Route 9 := (fun mask => (mask,id))

def c21792 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21792 : Upper (D 6) (R 6) [34,129,40,272,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,5,64] 13 (by decide) (choices 1) [2,4] r21792 c21792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6412
  · exact u6413

def b21793 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 280 22 33 68 196 324), lower := (rows 35 131 44 280 22 33 64 128 256), losses := [] }

theorem u21793 : Upper (D 6) (R 6) [34,129,40,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21794 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 280 22 36 65 193 321), lower := (rows 35 131 44 280 22 36 64 128 256), losses := [] }

theorem u21794 : Upper (D 6) (R 6) [34,129,40,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21795 : Route 9 := (fun mask => (mask,id))

def c21795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21795 : Upper (D 6) (R 6) [34,129,40,272,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,6,64] 13 (by decide) (choices 1) [1,4] r21795 c21795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6414
  · exact u6415

def b21796 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 280 81 34 68 196 324), lower := (rows 35 131 44 280 81 34 64 128 256), losses := [] }

theorem u21796 : Upper (D 6) (R 6) [34,129,40,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21797 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 280 81 36 70 198 326), lower := (rows 35 131 44 280 81 36 64 128 256), losses := [] }

theorem u21797 : Upper (D 6) (R 6) [34,129,40,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21798 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 280 81 96 70 134 262), lower := (rows 35 131 44 280 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 130 44 316 112 96 96 128 256) }] }

theorem u21798 : Upper (D 6) (R 6) [34,129,40,272,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21799 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 280 82 33 68 196 324), lower := (rows 35 131 44 280 82 33 64 128 256), losses := [] }

theorem u21799 : Upper (D 6) (R 6) [34,129,40,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21800 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 280 82 36 69 197 325), lower := (rows 35 131 44 280 82 36 64 128 256), losses := [] }

theorem u21800 : Upper (D 6) (R 6) [34,129,40,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21801 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 131 44 280 82 96 69 133 261), lower := (rows 35 131 44 280 82 96 64 128 256), losses := [] }

theorem u21801 : Upper (D 6) (R 6) [34,129,40,272,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21802 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 280 84 33 70 198 326), lower := (rows 35 131 44 280 84 33 64 128 256), losses := [] }

theorem u21802 : Upper (D 6) (R 6) [34,129,40,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21803 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 280 84 34 69 197 325), lower := (rows 35 131 44 280 84 34 64 128 256), losses := [] }

theorem u21803 : Upper (D 6) (R 6) [34,129,40,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21804 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 280 84 36 67 195 323), lower := (rows 35 131 44 280 84 36 64 128 256), losses := [] }

theorem u21804 : Upper (D 6) (R 6) [34,129,40,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21805 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 280 84 96 71 135 263), lower := (rows 35 131 44 280 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 130 44 316 116 96 96 128 256) }] }

theorem u21805 : Upper (D 6) (R 6) [34,129,40,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21806 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 328 21 34 84 212 340), lower := (rows 35 131 44 328 21 34 64 128 256), losses := [] }

theorem u21806 : Upper (D 6) (R 6) [34,129,40,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21807 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 131 44 328 21 36 82 210 338), lower := (rows 35 131 44 328 21 36 64 128 256), losses := [] }

theorem u21807 : Upper (D 6) (R 6) [34,129,40,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21808 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 328 21 48 70 198 326), lower := (rows 35 131 44 328 21 48 64 128 256), losses := [] }

theorem u21808 : Upper (D 6) (R 6) [34,129,40,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21808 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21809 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 147, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 328 21 96 86 150 278), lower := (rows 35 131 44 328 21 96 64 128 256), losses := [] }

theorem u21809 : Upper (D 6) (R 6) [34,129,40,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21810 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 328 22 33 84 212 340), lower := (rows 35 131 44 328 22 33 64 128 256), losses := [] }

theorem u21810 : Upper (D 6) (R 6) [34,129,40,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21811 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 328 22 36 81 209 337), lower := (rows 35 131 44 328 22 36 64 128 256), losses := [] }

theorem u21811 : Upper (D 6) (R 6) [34,129,40,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21812 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 328 22 48 69 197 325), lower := (rows 35 131 44 328 22 48 64 128 256), losses := [] }

theorem u21812 : Upper (D 6) (R 6) [34,129,40,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21812 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21813 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 147, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 328 22 96 85 149 277), lower := (rows 35 131 44 328 22 96 64 128 256), losses := [] }

theorem u21813 : Upper (D 6) (R 6) [34,129,40,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21814 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 328 81 34 84 148 276), lower := (rows 35 131 44 328 81 34 64 128 256), losses := [] }

theorem u21814 : Upper (D 6) (R 6) [34,129,40,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21815 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 328 81 36 86 150 278), lower := (rows 35 131 44 328 81 36 64 128 256), losses := [] }

theorem u21815 : Upper (D 6) (R 6) [34,129,40,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21816 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 328 81 48 70 134 262), lower := (rows 35 131 44 328 81 48 64 128 256), losses := [] }

theorem u21816 : Upper (D 6) (R 6) [34,129,40,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21816 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21817 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 328 82 33 84 148 276), lower := (rows 35 131 44 328 82 33 64 128 256), losses := [] }

theorem u21817 : Upper (D 6) (R 6) [34,129,40,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21818 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 328 82 36 85 149 277), lower := (rows 35 131 44 328 82 36 64 128 256), losses := [] }

theorem u21818 : Upper (D 6) (R 6) [34,129,40,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21819 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 328 82 48 69 133 261), lower := (rows 35 131 44 328 82 48 64 128 256), losses := [] }

theorem u21819 : Upper (D 6) (R 6) [34,129,40,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21819 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21820 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 328 84 33 86 150 278), lower := (rows 35 131 44 328 84 33 64 128 256), losses := [] }

theorem u21820 : Upper (D 6) (R 6) [34,129,40,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21821 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 328 84 34 85 149 277), lower := (rows 35 131 44 328 84 34 64 128 256), losses := [] }

theorem u21821 : Upper (D 6) (R 6) [34,129,40,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21822 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 44 328 84 36 83 147 275), lower := (rows 35 131 44 328 84 36 64 128 256), losses := [] }

theorem u21822 : Upper (D 6) (R 6) [34,129,40,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21823 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 328 84 48 71 135 263), lower := (rows 35 131 44 328 84 48 64 128 256), losses := [] }

theorem u21823 : Upper (D 6) (R 6) [34,129,40,320,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21823 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21824 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 131 70 13 52 40 336 464 336), lower := (rows 35 131 70 13 52 40 64 128 256), losses := [] }

theorem u21824 : Upper (D 6) (R 6) [34,129,66,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21824 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21825 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 13 52 48 328 456 328), lower := (rows 35 131 70 13 52 48 64 128 256), losses := [] }

theorem u21825 : Upper (D 6) (R 6) [34,129,66,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21825 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21826 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 70 13 52 96 344 408 280), lower := (rows 35 131 70 13 52 96 64 128 256), losses := [] }

theorem u21826 : Upper (D 6) (R 6) [34,129,66,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21827 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 52 288 88 216 344), lower := (rows 35 131 70 13 52 288 64 128 256), losses := [] }

theorem u21827 : Upper (D 6) (R 6) [34,129,66,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21827 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21828 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 131 70 13 56 36 336 464 336), lower := (rows 35 131 70 13 56 36 64 128 256), losses := [] }

theorem u21828 : Upper (D 6) (R 6) [34,129,66,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21829 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 13 56 48 324 452 324), lower := (rows 35 131 70 13 56 48 64 128 256), losses := [] }

theorem u21829 : Upper (D 6) (R 6) [34,129,66,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21829 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21830 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 70 13 56 96 340 404 276), lower := (rows 35 131 70 13 56 96 64 128 256), losses := [] }

theorem u21830 : Upper (D 6) (R 6) [34,129,66,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21831 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 56 288 84 212 340), lower := (rows 35 131 70 13 56 288 64 128 256), losses := [] }

theorem u21831 : Upper (D 6) (R 6) [34,129,66,5,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21831 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21832 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 131 70 13 88 36 368 432 304), lower := (rows 35 131 70 13 88 36 64 128 256), losses := [] }

theorem u21832 : Upper (D 6) (R 6) [34,129,66,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21833 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 88 48 356 420 292), lower := (rows 35 131 70 13 88 48 64 128 256), losses := [] }

theorem u21833 : Upper (D 6) (R 6) [34,129,66,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21833 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21834 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 88 288 116 180 308), lower := (rows 35 131 70 13 88 288 64 128 256), losses := [] }

theorem u21834 : Upper (D 6) (R 6) [34,129,66,5,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21834 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21835 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 70 13 112 36 344 408 280), lower := (rows 35 131 70 13 112 36 64 128 256), losses := [] }

theorem u21835 : Upper (D 6) (R 6) [34,129,66,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21836 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 13 112 40 340 404 276), lower := (rows 35 131 70 13 112 40 64 128 256), losses := [] }

theorem u21836 : Upper (D 6) (R 6) [34,129,66,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21836 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21837 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 13 112 48 332 396 268), lower := (rows 35 131 70 13 112 48 64 128 256), losses := [] }

theorem u21837 : Upper (D 6) (R 6) [34,129,66,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21837 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21838 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 112 288 92 156 284), lower := (rows 35 131 70 13 112 288 64 128 256), losses := [] }

theorem u21838 : Upper (D 6) (R 6) [34,129,66,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21838 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21839 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 13 276 40 112 240 368), lower := (rows 35 131 70 13 276 40 64 128 256), losses := [] }

theorem u21839 : Upper (D 6) (R 6) [34,129,66,5,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21839 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21839
end Delivery.IrregularNine14.P06
