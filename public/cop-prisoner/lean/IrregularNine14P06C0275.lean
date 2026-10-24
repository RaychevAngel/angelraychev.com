import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0069
import IrregularNine14P06C0070

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16500 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 262 104 49 48 69 197 325), lower := (rows 11 134 262 104 49 48 64 128 256), losses := [] }

theorem u16500 : Upper (D 6) (R 6) [10,132,258,96,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16500 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16501 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 104 49 96 85 149 277), lower := (rows 11 134 262 104 49 96 64 128 256), losses := [] }

theorem u16501 : Upper (D 6) (R 6) [10,132,258,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16502 : Route 9 := (fun mask => (mask,id))

def c16502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16502 : Upper (D 6) (R 6) [10,132,258,96,36,1] 13 := by
  apply FastRouting.sound _ _ [10,132,258,96,36,1] 13 (by decide) (choices 1) [1,16] r16502 c16502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4182
  · exact u4183

def b16503 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 262 104 52 48 65 193 321), lower := (rows 11 134 262 104 52 48 64 128 256), losses := [] }

theorem u16503 : Upper (D 6) (R 6) [10,132,258,96,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16503 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16504 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 104 52 96 81 145 273), lower := (rows 11 134 262 104 52 96 64 128 256), losses := [] }

theorem u16504 : Upper (D 6) (R 6) [10,132,258,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16505 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 276 41 52 33 66 194 322), lower := (rows 11 134 276 41 52 33 64 128 256), losses := [] }

theorem u16505 : Upper (D 6) (R 6) [10,132,272,33,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16506 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 276 41 52 34 65 193 321), lower := (rows 11 134 276 41 52 34 64 128 256), losses := [] }

theorem u16506 : Upper (D 6) (R 6) [10,132,272,33,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16507 : Route 9 := (fun mask => (mask,id))

def c16507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16507 : Upper (D 6) (R 6) [10,132,272,33,36,64] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,36,64] 13 (by decide) (choices 1) [1,2] r16507 c16507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4184
  · exact u4185

def b16508 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 276 41 81 34 100 228 356), lower := (rows 11 134 276 41 81 34 64 128 256), losses := [] }

theorem u16508 : Upper (D 6) (R 6) [10,132,272,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16509 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 134 276 41 81 36 98 226 354), lower := (rows 11 134 276 41 81 36 64 128 256), losses := [] }

theorem u16509 : Upper (D 6) (R 6) [10,132,272,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16510 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 276 41 81 96 102 166 294), lower := (rows 11 134 276 41 81 96 64 128 256), losses := [] }

theorem u16510 : Upper (D 6) (R 6) [10,132,272,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16511 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 276 41 82 33 100 228 356), lower := (rows 11 134 276 41 82 33 64 128 256), losses := [] }

theorem u16511 : Upper (D 6) (R 6) [10,132,272,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16512 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6)], upper := (rows 11 134 276 41 82 36 97 225 353), lower := (rows 11 134 276 41 82 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 38 73 137 265), good := (rows 489 164 308 489 112 36 64 128 256) }] }

theorem u16512 : Upper (D 6) (R 6) [10,132,272,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16513 : Route 9 := (fun mask => (mask,id))

def c16513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16513 : Upper (D 6) (R 6) [10,132,272,33,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,66,64] 13 (by decide) (choices 1) [1,4,32] r16513 c16513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4186
  · exact u4187
  · exact u4188

def b16514 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 276 41 84 33 98 226 354), lower := (rows 11 134 276 41 84 33 64 128 256), losses := [] }

theorem u16514 : Upper (D 6) (R 6) [10,132,272,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16515 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 276 41 84 34 97 225 353), lower := (rows 11 134 276 41 84 34 64 128 256), losses := [] }

theorem u16515 : Upper (D 6) (R 6) [10,132,272,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16516 : Route 9 := (fun mask => (mask,id))

def c16516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16516 : Upper (D 6) (R 6) [10,132,272,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,68,64] 13 (by decide) (choices 1) [1,2,32] r16516 c16516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4189
  · exact u4190
  · exact u4191

def b16517 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 276 41 112 33 70 198 326), lower := (rows 11 134 276 41 112 33 64 128 256), losses := [] }

theorem u16517 : Upper (D 6) (R 6) [10,132,272,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16518 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 276 41 112 34 69 197 325), lower := (rows 11 134 276 41 112 34 64 128 256), losses := [] }

theorem u16518 : Upper (D 6) (R 6) [10,132,272,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16519 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6)], upper := (rows 11 134 276 41 112 36 67 195 323), lower := (rows 11 134 276 41 112 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 38 64 128 256), good := (rows 41 164 308 41 112 36 64 128 256) }] }

theorem u16519 : Upper (D 6) (R 6) [10,132,272,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16520 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 276 41 112 96 71 135 263), lower := (rows 11 134 276 41 112 96 64 128 256), losses := [] }

theorem u16520 : Upper (D 6) (R 6) [10,132,272,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16521 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 134 276 44 81 33 98 226 354), lower := (rows 11 134 276 44 81 33 64 128 256), losses := [] }

theorem u16521 : Upper (D 6) (R 6) [10,132,272,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16522 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 134 276 44 81 34 97 225 353), lower := (rows 11 134 276 44 81 34 64 128 256), losses := [] }

theorem u16522 : Upper (D 6) (R 6) [10,132,272,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16523 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 131, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 134 276 44 81 96 99 163 291), lower := (rows 11 134 276 44 81 96 64 128 256), losses := [] }

theorem u16523 : Upper (D 6) (R 6) [10,132,272,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16524 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 134 276 44 82 33 97 225 353), lower := (rows 11 134 276 44 82 33 64 128 256), losses := [] }

theorem u16524 : Upper (D 6) (R 6) [10,132,272,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16525 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 131, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 134 276 44 82 96 97 161 289), lower := (rows 11 134 276 44 82 96 64 128 256), losses := [] }

theorem u16525 : Upper (D 6) (R 6) [10,132,272,36,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16526 : Route 9 := (fun mask => (mask,id))

def c16526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16526 : Upper (D 6) (R 6) [10,132,272,96,5,1] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,5,1] 13 (by decide) (choices 1) [2,32] r16526 c16526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4192
  · exact u4193

theorem m16527_1 : Upper (D 6) (R 6) [10,132,272,96,5,2,1] 13 :=
  permutation_upper _ _ _ [10,132,272,96,5,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4192

def r16527 : Route 9 := (fun mask => (mask,id))

def c16527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16527 : Upper (D 6) (R 6) [10,132,272,96,5,2] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,5,2] 13 (by decide) (choices 1) [1,32] r16527 c16527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16527_1
  · exact u4194

def b16528 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 276 104 21 96 99 163 291), lower := (rows 11 134 276 104 21 96 64 128 256), losses := [] }

theorem u16528 : Upper (D 6) (R 6) [10,132,272,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16529 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 134 276 104 49 33 70 198 326), lower := (rows 11 134 276 104 49 33 64 128 256), losses := [] }

theorem u16529 : Upper (D 6) (R 6) [10,132,272,96,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16530 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 134 276 104 49 34 69 197 325), lower := (rows 11 134 276 104 49 34 64 128 256), losses := [] }

theorem u16530 : Upper (D 6) (R 6) [10,132,272,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16531 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,1)], upper := (rows 11 134 276 104 49 36 67 195 323), lower := (rows 11 134 276 104 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 38 64 128 256), good := (rows 57 164 308 104 49 36 64 128 256) }] }

theorem u16531 : Upper (D 6) (R 6) [10,132,272,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16532 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 276 104 49 96 71 135 263), lower := (rows 11 134 276 104 49 96 64 128 256), losses := [] }

theorem u16532 : Upper (D 6) (R 6) [10,132,272,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16533 : Route 9 := (fun mask => (mask,id))

def c16533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16533 : Upper (D 6) (R 6) [10,132,272,96,34,1] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,34,1] 13 (by decide) (choices 1) [1,4] r16533 c16533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4195
  · exact u4196

def b16534 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 134 276 104 50 36 65 193 321), lower := (rows 11 134 276 104 50 36 64 128 256), losses := [] }

theorem u16534 : Upper (D 6) (R 6) [10,132,272,96,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16535 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 276 104 50 96 69 133 261), lower := (rows 11 134 276 104 50 96 64 128 256), losses := [] }

theorem u16535 : Upper (D 6) (R 6) [10,132,272,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16536 : Route 9 := (fun mask => (mask,id))

def c16536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16536 : Upper (D 6) (R 6) [10,132,272,96,36,1] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,36,1] 13 (by decide) (choices 1) [1,2] r16536 c16536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4197
  · exact u4198

def b16537 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 134 276 104 52 34 65 193 321), lower := (rows 11 134 276 104 52 34 64 128 256), losses := [] }

theorem u16537 : Upper (D 6) (R 6) [10,132,272,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16538 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 276 104 52 96 67 131 259), lower := (rows 11 134 276 104 52 96 64 128 256), losses := [] }

theorem u16538 : Upper (D 6) (R 6) [10,132,272,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16539 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 25 84 33 98 226 354), lower := (rows 11 134 292 25 84 33 64 128 256), losses := [] }

theorem u16539 : Upper (D 6) (R 6) [10,132,288,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16540 : Route 9 := (fun mask => (mask,id))

def c16540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16540 : Upper (D 6) (R 6) [10,132,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17,68,2] 13 (by decide) (choices 1) [1,32] r16540 c16540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4199
  · exact u4200

def r16541 : Route 9 := (fun mask => (mask,id))

def c16541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16541 : Upper (D 6) (R 6) [10,132,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17,68,64] 13 (by decide) (choices 1) [1,2,32] r16541 c16541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4201
  · exact u4202
  · exact u4203

def b16542 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 25 112 33 70 198 326), lower := (rows 11 134 292 25 112 33 64 128 256), losses := [] }

theorem u16542 : Upper (D 6) (R 6) [10,132,288,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16543 : Route 9 := (fun mask => (mask,id))

def c16543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16543 : Upper (D 6) (R 6) [10,132,288,17,96,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17,96,2] 13 (by decide) (choices 1) [1,4] r16543 c16543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4204
  · exact u4205

def b16544 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 25 112 36 67 195 323), lower := (rows 11 134 292 25 112 36 64 128 256), losses := [] }

theorem u16544 : Upper (D 6) (R 6) [10,132,288,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16545 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 292 25 112 96 71 135 263), lower := (rows 11 134 292 25 112 96 64 128 256), losses := [] }

theorem u16545 : Upper (D 6) (R 6) [10,132,288,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16546 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 134 292 28 81 33 98 226 354), lower := (rows 11 134 292 28 81 33 64 128 256), losses := [] }

theorem u16546 : Upper (D 6) (R 6) [10,132,288,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16547 : Route 9 := (fun mask => (mask,id))

def c16547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16547 : Upper (D 6) (R 6) [10,132,288,20,65,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20,65,2] 13 (by decide) (choices 1) [1,32] r16547 c16547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4206
  · exact u4207

def r16548 : Route 9 := (fun mask => (mask,id))

def c16548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16548 : Upper (D 6) (R 6) [10,132,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20,65,64] 13 (by decide) (choices 1) [1,2,32] r16548 c16548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4208
  · exact u4209
  · exact u4210

def r16549 : Route 9 := (fun mask => (mask,id))

def c16549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16549 : Upper (D 6) (R 6) [10,132,288,20,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20,66,1] 13 (by decide) (choices 1) [1,32] r16549 c16549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4211
  · exact u4212

def r16550 : Route 9 := (fun mask => (mask,id))

def c16550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16550 : Upper (D 6) (R 6) [10,132,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20,66,64] 13 (by decide) (choices 1) [1,32] r16550 c16550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4213
  · exact u4214

def b16551 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 292 41 81 34 84 212 340), lower := (rows 11 134 292 41 81 34 64 128 256), losses := [] }

theorem u16551 : Upper (D 6) (R 6) [10,132,288,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16552 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 41 81 36 82 210 338), lower := (rows 11 134 292 41 81 36 64 128 256), losses := [] }

theorem u16552 : Upper (D 6) (R 6) [10,132,288,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16553 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 292 41 81 48 70 198 326), lower := (rows 11 134 292 41 81 48 64 128 256), losses := [] }

theorem u16553 : Upper (D 6) (R 6) [10,132,288,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16553 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16554 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 292 41 81 96 86 150 278), lower := (rows 11 134 292 41 81 96 64 128 256), losses := [] }

theorem u16554 : Upper (D 6) (R 6) [10,132,288,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16555 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 292 41 82 33 84 212 340), lower := (rows 11 134 292 41 82 33 64 128 256), losses := [] }

theorem u16555 : Upper (D 6) (R 6) [10,132,288,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16556 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 41 82 36 81 209 337), lower := (rows 11 134 292 41 82 36 64 128 256), losses := [] }

theorem u16556 : Upper (D 6) (R 6) [10,132,288,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16557 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 134 292 41 82 48 69 197 325), lower := (rows 11 134 292 41 82 48 64 128 256), losses := [] }

theorem u16557 : Upper (D 6) (R 6) [10,132,288,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16557 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16558 : Route 9 := (fun mask => (mask,id))

def c16558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16558 : Upper (D 6) (R 6) [10,132,288,33,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33,66,64] 13 (by decide) (choices 1) [1,4,16] r16558 c16558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4215
  · exact u4216
  · exact u4217

def b16559 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 292 41 84 33 82 210 338), lower := (rows 11 134 292 41 84 33 64 128 256), losses := [] }

theorem u16559 : Upper (D 6) (R 6) [10,132,288,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16559
end Delivery.IrregularNine14.P06
