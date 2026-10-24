import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0072

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16800 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 13 273 36 98 226 354), lower := (rows 11 146 100 13 273 36 64 128 256), losses := [] }

theorem u16800 : Upper (D 6) (R 6) [10,144,96,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16801 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 13 273 96 102 166 294), lower := (rows 11 146 100 13 273 96 64 128 256), losses := [] }

theorem u16801 : Upper (D 6) (R 6) [10,144,96,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16802 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 274 33 100 228 356), lower := (rows 11 146 100 13 274 33 64 128 256), losses := [] }

theorem u16802 : Upper (D 6) (R 6) [10,144,96,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16803 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 108, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 13 274 36 97 225 353), lower := (rows 11 146 100 13 274 36 64 128 256), losses := [] }

theorem u16803 : Upper (D 6) (R 6) [10,144,96,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16804 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 13 274 96 101 165 293), lower := (rows 11 146 100 13 274 96 64 128 256), losses := [] }

theorem u16804 : Upper (D 6) (R 6) [10,144,96,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16805 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 276 33 98 226 354), lower := (rows 11 146 100 13 276 33 64 128 256), losses := [] }

theorem u16805 : Upper (D 6) (R 6) [10,144,96,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m16806_1 : Upper (D 6) (R 6) [10,144,96,5,260,2,1] 13 :=
  permutation_upper _ _ _ [10,144,96,5,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4338

def r16806 : Route 9 := (fun mask => (mask,id))

def c16806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16806 : Upper (D 6) (R 6) [10,144,96,5,260,2] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,260,2] 13 (by decide) (choices 1) [1,32] r16806 c16806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16806_1
  · exact u4339

def b16807 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 13 276 96 99 163 291), lower := (rows 11 146 100 13 276 96 64 128 256), losses := [] }

theorem u16807 : Upper (D 6) (R 6) [10,144,96,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16808 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 304 33 70 198 326), lower := (rows 11 146 100 13 304 33 64 128 256), losses := [] }

theorem u16808 : Upper (D 6) (R 6) [10,144,96,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16809 : Route 9 := (fun mask => (mask,id))

def c16809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16809 : Upper (D 6) (R 6) [10,144,96,5,288,2] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,288,2] 13 (by decide) (choices 1) [1,4] r16809 c16809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4340
  · exact u4341

def r16810 : Route 9 := (fun mask => (mask,id))

def c16810 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16810 : Upper (D 6) (R 6) [10,144,96,5,288,4] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,288,4] 13 (by decide) (choices 1) [1,2] r16810 c16810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4342
  · exact u4343

def b16811 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 13 304 96 71 135 263), lower := (rows 11 146 100 13 304 96 64 128 256), losses := [] }

theorem u16811 : Upper (D 6) (R 6) [10,144,96,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16812 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 22 33 324 452 324), lower := (rows 11 146 100 41 22 33 64 128 256), losses := [] }

theorem u16812 : Upper (D 6) (R 6) [10,144,96,33,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16813 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 11 146 100 41 22 36 321 449 321), lower := (rows 11 146 100 41 22 36 64 128 256), losses := [] }

theorem u16813 : Upper (D 6) (R 6) [10,144,96,33,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16814 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 41 22 96 325 389 261), lower := (rows 11 146 100 41 22 96 64 128 256), losses := [] }

theorem u16814 : Upper (D 6) (R 6) [10,144,96,33,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16815 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 146 100 41 22 288 69 197 325), lower := (rows 11 146 100 41 22 288 64 128 256), losses := [] }

theorem u16815 : Upper (D 6) (R 6) [10,144,96,33,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16815 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16816 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 81 34 324 388 260), lower := (rows 11 146 100 41 81 34 64 128 256), losses := [] }

theorem u16816 : Upper (D 6) (R 6) [10,144,96,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16817 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 41 81 36 326 390 262), lower := (rows 11 146 100 41 81 36 64 128 256), losses := [] }

theorem u16817 : Upper (D 6) (R 6) [10,144,96,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16818 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 146 100 41 81 288 70 134 262), lower := (rows 11 146 100 41 81 288 64 128 256), losses := [] }

theorem u16818 : Upper (D 6) (R 6) [10,144,96,33,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16818 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16819 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 82 33 324 388 260), lower := (rows 11 146 100 41 82 33 64 128 256), losses := [] }

theorem u16819 : Upper (D 6) (R 6) [10,144,96,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16820 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 41 82 36 325 389 261), lower := (rows 11 146 100 41 82 36 64 128 256), losses := [] }

theorem u16820 : Upper (D 6) (R 6) [10,144,96,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16821 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 146 100 41 82 288 69 133 261), lower := (rows 11 146 100 41 82 288 64 128 256), losses := [] }

theorem u16821 : Upper (D 6) (R 6) [10,144,96,33,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16821 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16822 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 273 34 68 196 324), lower := (rows 11 146 100 41 273 34 64 128 256), losses := [] }

theorem u16822 : Upper (D 6) (R 6) [10,144,96,33,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16823 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 41 273 36 70 198 326), lower := (rows 11 146 100 41 273 36 64 128 256), losses := [] }

theorem u16823 : Upper (D 6) (R 6) [10,144,96,33,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16824 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 41 273 96 70 134 262), lower := (rows 11 146 100 41 273 96 64 128 256), losses := [] }

theorem u16824 : Upper (D 6) (R 6) [10,144,96,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16825 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 274 33 68 196 324), lower := (rows 11 146 100 41 274 33 64 128 256), losses := [] }

theorem u16825 : Upper (D 6) (R 6) [10,144,96,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16826 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 108, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 41 274 36 69 197 325), lower := (rows 11 146 100 41 274 36 64 128 256), losses := [] }

theorem u16826 : Upper (D 6) (R 6) [10,144,96,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16827 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 41 274 96 69 133 261), lower := (rows 11 146 100 41 274 96 64 128 256), losses := [] }

theorem u16827 : Upper (D 6) (R 6) [10,144,96,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16828 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 276 33 70 198 326), lower := (rows 11 146 100 41 276 33 64 128 256), losses := [] }

theorem u16828 : Upper (D 6) (R 6) [10,144,96,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16829 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 276 34 69 197 325), lower := (rows 11 146 100 41 276 34 64 128 256), losses := [] }

theorem u16829 : Upper (D 6) (R 6) [10,144,96,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16830 : PairBound 9 := { available := 67, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 11 146 100 41 276 36 67 195 323), lower := (rows 11 146 100 41 276 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 16 52 0 128 256), good := (rows 11 187 36 41 308 36 0 128 256) }] }

theorem u16830 : Upper (D 6) (R 6) [10,144,96,33,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16831 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 41 276 96 71 135 263), lower := (rows 11 146 100 41 276 96 64 128 256), losses := [] }

theorem u16831 : Upper (D 6) (R 6) [10,144,96,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16832 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 336 33 70 134 262), lower := (rows 11 146 100 41 336 33 64 128 256), losses := [] }

theorem u16832 : Upper (D 6) (R 6) [10,144,96,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16833 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 100 41 336 34 69 133 261), lower := (rows 11 146 100 41 336 34 64 128 256), losses := [] }

theorem u16833 : Upper (D 6) (R 6) [10,144,96,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16834 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 41 336 36 71 135 263), lower := (rows 11 146 100 41 336 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 84 9 16 118 64 128 256), good := (rows 41 180 100 41 372 36 100 128 256) }] }

theorem u16834 : Upper (D 6) (R 6) [10,144,96,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16835 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 5, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 265 21 34 100 228 356), lower := (rows 11 146 100 265 21 34 64 128 256), losses := [] }

theorem u16835 : Upper (D 6) (R 6) [10,144,96,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16836 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 265 21 36 98 226 354), lower := (rows 11 146 100 265 21 36 64 128 256), losses := [] }

theorem u16836 : Upper (D 6) (R 6) [10,144,96,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16837 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 265 21 96 102 166 294), lower := (rows 11 146 100 265 21 96 64 128 256), losses := [] }

theorem u16837 : Upper (D 6) (R 6) [10,144,96,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16838 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 265 22 33 100 228 356), lower := (rows 11 146 100 265 22 33 64 128 256), losses := [] }

theorem u16838 : Upper (D 6) (R 6) [10,144,96,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16839 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 265 22 36 97 225 353), lower := (rows 11 146 100 265 22 36 64 128 256), losses := [] }

theorem u16839 : Upper (D 6) (R 6) [10,144,96,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16840 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 265 22 96 101 165 293), lower := (rows 11 146 100 265 22 96 64 128 256), losses := [] }

theorem u16840 : Upper (D 6) (R 6) [10,144,96,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16841 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 146 100 265 49 34 68 196 324), lower := (rows 11 146 100 265 49 34 64 128 256), losses := [] }

theorem u16841 : Upper (D 6) (R 6) [10,144,96,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16842 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 265 49 36 70 198 326), lower := (rows 11 146 100 265 49 36 64 128 256), losses := [] }

theorem u16842 : Upper (D 6) (R 6) [10,144,96,257,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16843 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 265 49 96 70 134 262), lower := (rows 11 146 100 265 49 96 64 128 256), losses := [] }

theorem u16843 : Upper (D 6) (R 6) [10,144,96,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16844 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 265 50 33 68 196 324), lower := (rows 11 146 100 265 50 33 64 128 256), losses := [] }

theorem u16844 : Upper (D 6) (R 6) [10,144,96,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16845 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 265 50 36 69 197 325), lower := (rows 11 146 100 265 50 36 64 128 256), losses := [] }

theorem u16845 : Upper (D 6) (R 6) [10,144,96,257,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16846 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 265 50 96 69 133 261), lower := (rows 11 146 100 265 50 96 64 128 256), losses := [] }

theorem u16846 : Upper (D 6) (R 6) [10,144,96,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16847 : Route 9 := (fun mask => (mask,id))

def c16847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16847 : Upper (D 6) (R 6) [10,144,96,260,5,1] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,5,1] 13 (by decide) (choices 1) [2,32] r16847 c16847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4344
  · exact u4345

theorem m16848_1 : Upper (D 6) (R 6) [10,144,96,260,5,2,1] 13 :=
  permutation_upper _ _ _ [10,144,96,260,5,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4344

def r16848 : Route 9 := (fun mask => (mask,id))

def c16848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16848 : Upper (D 6) (R 6) [10,144,96,260,5,2] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,5,2] 13 (by decide) (choices 1) [1,32] r16848 c16848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16848_1
  · exact u4346

def b16849 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 268 21 96 99 163 291), lower := (rows 11 146 100 268 21 96 64 128 256), losses := [] }

theorem u16849 : Upper (D 6) (R 6) [10,144,96,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16850 : Route 9 := (fun mask => (mask,id))

def c16850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16850 : Upper (D 6) (R 6) [10,144,96,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,6,1] 13 (by decide) (choices 1) [1,32] r16850 c16850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4347
  · exact u4348

def b16851 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 268 22 96 97 161 289), lower := (rows 11 146 100 268 22 96 64 128 256), losses := [] }

theorem u16851 : Upper (D 6) (R 6) [10,144,96,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16852 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 146 100 268 49 33 70 198 326), lower := (rows 11 146 100 268 49 33 64 128 256), losses := [] }

theorem u16852 : Upper (D 6) (R 6) [10,144,96,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16853 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 68, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 146 100 268 49 34 69 197 325), lower := (rows 11 146 100 268 49 34 64 128 256), losses := [] }

theorem u16853 : Upper (D 6) (R 6) [10,144,96,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16854 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 11 146 100 268 49 36 67 195 323), lower := (rows 11 146 100 268 49 36 64 128 256), losses := [] }

theorem u16854 : Upper (D 6) (R 6) [10,144,96,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16855 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 268 49 96 71 135 263), lower := (rows 11 146 100 268 49 96 64 128 256), losses := [] }

theorem u16855 : Upper (D 6) (R 6) [10,144,96,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16856 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 146 100 268 50 33 69 197 325), lower := (rows 11 146 100 268 50 33 64 128 256), losses := [] }

theorem u16856 : Upper (D 6) (R 6) [10,144,96,260,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16857 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 268 50 36 65 193 321), lower := (rows 11 146 100 268 50 36 64 128 256), losses := [] }

theorem u16857 : Upper (D 6) (R 6) [10,144,96,260,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16858 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 268 50 96 69 133 261), lower := (rows 11 146 100 268 50 96 64 128 256), losses := [] }

theorem u16858 : Upper (D 6) (R 6) [10,144,96,260,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16859 : Route 9 := (fun mask => (mask,id))

def c16859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16859 : Upper (D 6) (R 6) [10,144,96,288,5,1] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,5,1] 13 (by decide) (choices 1) [2,4] r16859 c16859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4349
  · exact u4350

#print axioms u16859
end Delivery.IrregularNine14.P06
