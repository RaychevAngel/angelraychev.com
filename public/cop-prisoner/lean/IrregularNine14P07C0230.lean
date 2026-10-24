import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0035
import IrregularNine14P07C0036

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r13800 : Route 9 := (fun mask => (mask,id))

def c13800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13800 : Upper (D 7) (R 7) [6,96,24,33,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,258,128] 13 (by decide) (choices 1) [1,128] r13800 c13800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2139
  · exact u2140

def b13801 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 28 41 336 33 194 130 386), lower := (rows 7 98 28 41 336 33 64 128 256), losses := [] }

theorem u13801 : Upper (D 7) (R 7) [6,96,24,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13802 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 28 41 336 34 193 129 385), lower := (rows 7 98 28 41 336 34 64 128 256), losses := [] }

theorem u13802 : Upper (D 7) (R 7) [6,96,24,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13803 : Route 9 := (fun mask => (mask,id))

def c13803 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13803 : Upper (D 7) (R 7) [6,96,24,33,320,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,320,128] 13 (by decide) (choices 1) [1,2,128] r13803 c13803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2141
  · exact u2142
  · exact u2143

def b13804 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 28 41 400 33 194 194 450), lower := (rows 7 98 28 41 400 33 64 128 256), losses := [] }

theorem u13804 : Upper (D 7) (R 7) [6,96,24,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13805 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 28 41 400 34 193 193 449), lower := (rows 7 98 28 41 400 34 64 128 256), losses := [] }

theorem u13805 : Upper (D 7) (R 7) [6,96,24,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13806 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 41 400 96 195 131 387), lower := (rows 7 98 28 41 400 96 64 128 256), losses := [] }

theorem u13806 : Upper (D 7) (R 7) [6,96,24,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13807 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(4,5)], upper := (rows 7 98 28 41 400 160 67 195 323), lower := (rows 7 98 28 41 400 160 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 66 28 477 400 128 64 128 256) },{ target := 7, region := (rows 5 10 4 8 16 32 77 0 269), good := (rows 327 98 351 363 272 32 64 0 256) }] }

theorem u13807 : Upper (D 7) (R 7) [6,96,24,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13808 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 7 98 28 137 176 33 322 450 322), lower := (rows 7 98 28 137 176 33 64 128 256), losses := [] }

theorem u13808 : Upper (D 7) (R 7) [6,96,24,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13809 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(3,5)], upper := (rows 7 98 28 137 176 34 321 449 321), lower := (rows 7 98 28 137 176 34 64 128 256), losses := [] }

theorem u13809 : Upper (D 7) (R 7) [6,96,24,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13810 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 137 176 96 323 387 259), lower := (rows 7 98 28 137 176 96 64 128 256), losses := [] }

theorem u13810 : Upper (D 7) (R 7) [6,96,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13811 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(1,7),(3,5)], upper := (rows 7 98 28 137 176 288 67 195 323), lower := (rows 7 98 28 137 176 288 64 128 256), losses := [] }

theorem u13811 : Upper (D 7) (R 7) [6,96,24,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13811 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13812 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 226, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,1)], upper := (rows 7 98 28 137 273 34 224 224 480), lower := (rows 7 98 28 137 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 29 9 17 32 98 162 290), good := (rows 477 480 28 157 285 480 64 128 256) }] }

theorem u13812 : Upper (D 7) (R 7) [6,96,24,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13813 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 137 273 96 226 162 418), lower := (rows 7 98 28 137 273 96 64 128 256), losses := [] }

theorem u13813 : Upper (D 7) (R 7) [6,96,24,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13814 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 226, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(4,7)], upper := (rows 7 98 28 137 273 160 98 226 354), lower := (rows 7 98 28 137 273 160 64 128 256), losses := [{ target := 7, region := (rows 1 34 12 8 17 32 98 0 290), good := (rows 343 354 28 29 273 354 64 0 256) }] }

theorem u13814 : Upper (D 7) (R 7) [6,96,24,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13815 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 0, region := 232, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 98 28 137 274 33 224 224 480), lower := (rows 7 98 28 137 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 51 32 98 162 290), good := (rows 470 498 28 156 466 498 64 128 256) }] }

theorem u13815 : Upper (D 7) (R 7) [6,96,24,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13816 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 137 274 96 225 161 417), lower := (rows 7 98 28 137 274 96 64 128 256), losses := [] }

theorem u13816 : Upper (D 7) (R 7) [6,96,24,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m13817_1 : Upper (D 7) (R 7) [6,96,24,129,258,128,1] 13 :=
  permutation_upper _ _ _ [6,96,24,129,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2144

theorem m13817_32 : Upper (D 7) (R 7) [6,96,24,129,258,128,32] 13 :=
  permutation_upper _ _ _ [6,96,24,129,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2145

def r13817 : Route 9 := (fun mask => (mask,id))

def c13817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13817 : Upper (D 7) (R 7) [6,96,24,129,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,258,128] 13 (by decide) (choices 1) [1,32] r13817 c13817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13817_1
  · exact m13817_32

def b13818 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(2,5),(3,5),(4,0)], upper := (rows 7 98 28 137 304 33 194 194 450), lower := (rows 7 98 28 137 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 41 16 0 67 131 259), good := (rows 463 458 28 457 284 457 64 128 256) }] }

theorem u13818 : Upper (D 7) (R 7) [6,96,24,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13819 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 7 98 28 137 304 34 193 193 449), lower := (rows 7 98 28 137 304 34 64 128 256), losses := [] }

theorem u13819 : Upper (D 7) (R 7) [6,96,24,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13820 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 137 304 96 195 131 387), lower := (rows 7 98 28 137 304 96 64 128 256), losses := [] }

theorem u13820 : Upper (D 7) (R 7) [6,96,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13821 : Route 9 := (fun mask => (mask,id))

def c13821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13821 : Upper (D 7) (R 7) [6,96,24,129,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,288,128] 13 (by decide) (choices 1) [1,2] r13821 c13821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2146
  · exact u2147

def b13822 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 28 137 400 33 98 226 354), lower := (rows 7 98 28 137 400 33 64 128 256), losses := [] }

theorem u13822 : Upper (D 7) (R 7) [6,96,24,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m13823_1 : Upper (D 7) (R 7) [6,96,24,129,384,2,1] 13 :=
  permutation_upper _ _ _ [6,96,24,129,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2148

def r13823 : Route 9 := (fun mask => (mask,id))

def c13823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13823 : Upper (D 7) (R 7) [6,96,24,129,384,2] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,384,2] 13 (by decide) (choices 1) [1,32] r13823 c13823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13823_1
  · exact u2149

def b13824 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 137 400 96 99 163 291), lower := (rows 7 98 28 137 400 96 64 128 256), losses := [] }

theorem u13824 : Upper (D 7) (R 7) [6,96,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13825 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 202, targets := 1 },{ cop := 0, region := 496, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 98 28 138 273 33 224 224 480), lower := (rows 7 98 28 138 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 20 43 16 32 98 162 290), good := (rows 462 490 28 458 284 490 64 128 256) }] }

theorem u13825 : Upper (D 7) (R 7) [6,96,24,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13826 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 138 273 96 225 161 417), lower := (rows 7 98 28 138 273 96 64 128 256), losses := [] }

theorem u13826 : Upper (D 7) (R 7) [6,96,24,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m13827_1 : Upper (D 7) (R 7) [6,96,24,130,257,128,1] 13 :=
  permutation_upper _ _ _ [6,96,24,130,257,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2150

theorem m13827_32 : Upper (D 7) (R 7) [6,96,24,130,257,128,32] 13 :=
  permutation_upper _ _ _ [6,96,24,130,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2151

def r13827 : Route 9 := (fun mask => (mask,id))

def c13827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13827 : Upper (D 7) (R 7) [6,96,24,130,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,257,128] 13 (by decide) (choices 1) [1,32] r13827 c13827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13827_1
  · exact m13827_32

def r13828 : Route 9 := (fun mask => (mask,id))

def c13828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13828 : Upper (D 7) (R 7) [6,96,24,130,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,288,1] 13 (by decide) (choices 1) [1,128] r13828 c13828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2152
  · exact u2153

def b13829 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 138 304 96 193 129 385), lower := (rows 7 98 28 138 304 96 64 128 256), losses := [] }

theorem u13829 : Upper (D 7) (R 7) [6,96,24,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13830 : Route 9 := (fun mask => (mask,id))

def c13830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13830 : Upper (D 7) (R 7) [6,96,24,130,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,288,128] 13 (by decide) (choices 1) [1] r13830 c13830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2154

def b13831 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(4,1)], upper := (rows 7 98 28 138 400 33 97 225 353), lower := (rows 7 98 28 138 400 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 51 33 97 161 289), good := (rows 501 496 28 156 400 497 64 128 256) }] }

theorem u13831 : Upper (D 7) (R 7) [6,96,24,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13832 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 138 400 96 97 161 289), lower := (rows 7 98 28 138 400 96 64 128 256), losses := [] }

theorem u13832 : Upper (D 7) (R 7) [6,96,24,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13833 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 202, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(4,5)], upper := (rows 7 98 28 168 273 33 194 194 450), lower := (rows 7 98 28 168 273 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 49 0 67 131 259), good := (rows 471 466 28 156 465 465 64 128 256) }] }

theorem u13833 : Upper (D 7) (R 7) [6,96,24,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13834 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 28 168 273 34 193 193 449), lower := (rows 7 98 28 168 273 34 64 128 256), losses := [] }

theorem u13834 : Upper (D 7) (R 7) [6,96,24,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13835 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 168 273 96 195 131 387), lower := (rows 7 98 28 168 273 96 64 128 256), losses := [] }

theorem u13835 : Upper (D 7) (R 7) [6,96,24,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13836 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 28 168 273 160 67 195 323), lower := (rows 7 98 28 168 273 160 64 128 256), losses := [] }

theorem u13836 : Upper (D 7) (R 7) [6,96,24,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13837 : Route 9 := (fun mask => (mask,id))

def c13837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13837 : Upper (D 7) (R 7) [6,96,24,160,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160,258,1] 13 (by decide) (choices 1) [1,128] r13837 c13837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2155
  · exact u2156

def b13838 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 168 274 96 193 129 385), lower := (rows 7 98 28 168 274 96 64 128 256), losses := [] }

theorem u13838 : Upper (D 7) (R 7) [6,96,24,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13839 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 28 168 274 160 65 193 321), lower := (rows 7 98 28 168 274 160 64 128 256), losses := [] }

theorem u13839 : Upper (D 7) (R 7) [6,96,24,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13840 : Route 9 := (fun mask => (mask,id))

def c13840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13840 : Upper (D 7) (R 7) [6,96,24,160,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160,320,1] 13 (by decide) (choices 1) [1,2,128] r13840 c13840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2157
  · exact u2158
  · exact u2159

def b13841 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 28 168 336 34 193 129 385), lower := (rows 7 98 28 168 336 34 64 128 256), losses := [] }

theorem u13841 : Upper (D 7) (R 7) [6,96,24,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13842 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 28 168 336 160 67 131 259), lower := (rows 7 98 28 168 336 160 64 128 256), losses := [] }

theorem u13842 : Upper (D 7) (R 7) [6,96,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13843 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(4,5)], upper := (rows 7 98 28 168 400 33 67 195 323), lower := (rows 7 98 28 168 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 49 0 65 129 257), good := (rows 471 82 28 156 400 465 64 128 256) }] }

theorem u13843 : Upper (D 7) (R 7) [6,96,24,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13844 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 7 98 28 168 400 34 65 193 321), lower := (rows 7 98 28 168 400 34 64 128 256), losses := [] }

theorem u13844 : Upper (D 7) (R 7) [6,96,24,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13845 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 168 400 96 67 131 259), lower := (rows 7 98 28 168 400 96 64 128 256), losses := [] }

theorem u13845 : Upper (D 7) (R 7) [6,96,24,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13846 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 25 146 33 448 448 448), lower := (rows 7 98 44 25 146 33 64 128 256), losses := [] }

theorem u13846 : Upper (D 7) (R 7) [6,96,40,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13847 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 25 146 96 449 385 385), lower := (rows 7 98 44 25 146 96 64 128 256), losses := [] }

theorem u13847 : Upper (D 7) (R 7) [6,96,40,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13848 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(3,6)], upper := (rows 7 98 44 25 146 160 321 449 321), lower := (rows 7 98 44 25 146 160 64 128 256), losses := [] }

theorem u13848 : Upper (D 7) (R 7) [6,96,40,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13849 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 44 25 146 288 193 193 449), lower := (rows 7 98 44 25 146 288 64 128 256), losses := [] }

theorem u13849 : Upper (D 7) (R 7) [6,96,40,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13849 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13850 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 44 25 208 33 450 386 386), lower := (rows 7 98 44 25 208 33 64 128 256), losses := [] }

theorem u13850 : Upper (D 7) (R 7) [6,96,40,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13851 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 25 208 34 449 385 385), lower := (rows 7 98 44 25 208 34 64 128 256), losses := [] }

theorem u13851 : Upper (D 7) (R 7) [6,96,40,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13852 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 25 208 160 323 387 259), lower := (rows 7 98 44 25 208 160 64 128 256), losses := [] }

theorem u13852 : Upper (D 7) (R 7) [6,96,40,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13853 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 7 98 44 25 208 288 195 131 387), lower := (rows 7 98 44 25 208 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 297 0 129 257), good := (rows 423 34 44 445 144 288 0 128 288) }] }

theorem u13853 : Upper (D 7) (R 7) [6,96,40,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13853 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13854 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 25 274 33 192 192 448), lower := (rows 7 98 44 25 274 33 64 128 256), losses := [] }

theorem u13854 : Upper (D 7) (R 7) [6,96,40,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13855 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 25 274 96 193 129 385), lower := (rows 7 98 44 25 274 96 64 128 256), losses := [] }

theorem u13855 : Upper (D 7) (R 7) [6,96,40,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13856 : Route 9 := (fun mask => (mask,id))

def c13856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13856 : Upper (D 7) (R 7) [6,96,40,17,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,258,128] 13 (by decide) (choices 1) [1,128] r13856 c13856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2160
  · exact u2161

def b13857 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 44 25 336 33 194 130 386), lower := (rows 7 98 44 25 336 33 64 128 256), losses := [] }

theorem u13857 : Upper (D 7) (R 7) [6,96,40,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13858 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 25 336 34 193 129 385), lower := (rows 7 98 44 25 336 34 64 128 256), losses := [] }

theorem u13858 : Upper (D 7) (R 7) [6,96,40,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13859 : Route 9 := (fun mask => (mask,id))

def c13859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13859 : Upper (D 7) (R 7) [6,96,40,17,320,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,320,128] 13 (by decide) (choices 1) [1,2,128] r13859 c13859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2162
  · exact u2163
  · exact u2164

#print axioms u13859
end Delivery.IrregularNine14.P07
