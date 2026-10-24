import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0074
import IrregularNine14P06C0075

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17040 : Route 9 := (fun mask => (mask,id))

def c17040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17040 : Upper (D 6) (R 6) [10,160,18,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,260,1] 13 (by decide) (choices 1) [1,32] r17040 c17040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4482
  · exact u4483

def r17041 : Route 9 := (fun mask => (mask,id))

def c17041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17041 : Upper (D 6) (R 6) [10,160,18,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,260,64] 13 (by decide) (choices 1) [1,32] r17041 c17041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4484
  · exact u4485

def r17042 : Route 9 := (fun mask => (mask,id))

def c17042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17042 : Upper (D 6) (R 6) [10,160,18,68,288,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,288,1] 13 (by decide) (choices 1) [1,4] r17042 c17042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4486
  · exact u4487

def b17043 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 162 22 76 304 36 65 193 321), lower := (rows 11 162 22 76 304 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 160 52 108 304 36 64 128 256) }] }

theorem u17043 : Upper (D 6) (R 6) [10,160,18,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17044 : Route 9 := (fun mask => (mask,id))

def c17044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17044 : Upper (D 6) (R 6) [10,160,18,68,288,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,288,64] 13 (by decide) (choices 1) [1,4] r17044 c17044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4488
  · exact u4489

def r17045 : Route 9 := (fun mask => (mask,id))

def c17045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17045 : Upper (D 6) (R 6) [10,160,18,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,320,1] 13 (by decide) (choices 1) [1,4,32] r17045 c17045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4490
  · exact u4491
  · exact u4492

def b17046 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 162 22 76 336 36 97 161 289), lower := (rows 11 162 22 76 336 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 160 52 108 336 36 64 128 256) }] }

theorem u17046 : Upper (D 6) (R 6) [10,160,18,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17047 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 22 104 273 33 68 196 324), lower := (rows 11 162 22 104 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 49 68 132 260), good := (rows 41 160 508 104 305 33 64 128 256) }] }

theorem u17047 : Upper (D 6) (R 6) [10,160,18,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17048 : Route 9 := (fun mask => (mask,id))

def c17048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17048 : Upper (D 6) (R 6) [10,160,18,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,257,4] 13 (by decide) (choices 1) [1,4] r17048 c17048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4493
  · exact u4494

def b17049 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 22 104 273 96 69 133 261), lower := (rows 11 162 22 104 273 96 64 128 256), losses := [] }

theorem u17049 : Upper (D 6) (R 6) [10,160,18,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17050 : Route 9 := (fun mask => (mask,id))

def c17050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17050 : Upper (D 6) (R 6) [10,160,18,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,260,1] 13 (by decide) (choices 1) [1,4] r17050 c17050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4495
  · exact u4496

def b17051 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 22 104 276 36 65 193 321), lower := (rows 11 162 22 104 276 36 64 128 256), losses := [] }

theorem u17051 : Upper (D 6) (R 6) [10,160,18,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17052 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 22 104 276 96 69 133 261), lower := (rows 11 162 22 104 276 96 64 128 256), losses := [] }

theorem u17052 : Upper (D 6) (R 6) [10,160,18,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17053 : Route 9 := (fun mask => (mask,id))

def c17053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17053 : Upper (D 6) (R 6) [10,160,18,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,320,1] 13 (by decide) (choices 1) [1,4] r17053 c17053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4497
  · exact u4498

def r17054 : Route 9 := (fun mask => (mask,id))

def c17054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17054 : Upper (D 6) (R 6) [10,160,18,96,320,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,320,4] 13 (by decide) (choices 1) [1,4] r17054 c17054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4499
  · exact u4500

def b17055 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 25 84 34 324 452 324), lower := (rows 11 162 37 25 84 34 64 128 256), losses := [] }

theorem u17055 : Upper (D 6) (R 6) [10,160,33,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17056 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 25 84 36 322 450 322), lower := (rows 11 162 37 25 84 36 64 128 256), losses := [] }

theorem u17056 : Upper (D 6) (R 6) [10,160,33,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17057 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 37 25 84 96 326 390 262), lower := (rows 11 162 37 25 84 96 64 128 256), losses := [] }

theorem u17057 : Upper (D 6) (R 6) [10,160,33,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17058 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 37 25 84 288 70 198 326), lower := (rows 11 162 37 25 84 288 64 128 256), losses := [] }

theorem u17058 : Upper (D 6) (R 6) [10,160,33,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17058 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17059 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 25 276 34 68 196 324), lower := (rows 11 162 37 25 276 34 64 128 256), losses := [] }

theorem u17059 : Upper (D 6) (R 6) [10,160,33,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17060 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 25 276 36 66 194 322), lower := (rows 11 162 37 25 276 36 64 128 256), losses := [] }

theorem u17060 : Upper (D 6) (R 6) [10,160,33,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17061 : Route 9 := (fun mask => (mask,id))

def c17061 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17061 : Upper (D 6) (R 6) [10,160,33,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,17,260,64] 13 (by decide) (choices 1) [2,4] r17061 c17061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4501
  · exact u4502

def b17062 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 25 336 34 68 196 324), lower := (rows 11 162 37 25 336 34 64 128 256), losses := [] }

theorem u17062 : Upper (D 6) (R 6) [10,160,33,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17063 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 25 336 36 70 198 326), lower := (rows 11 162 37 25 336 36 64 128 256), losses := [] }

theorem u17063 : Upper (D 6) (R 6) [10,160,33,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17064 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 37 25 336 96 70 134 262), lower := (rows 11 162 37 25 336 96 64 128 256), losses := [] }

theorem u17064 : Upper (D 6) (R 6) [10,160,33,17,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17065 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 28 81 34 324 452 324), lower := (rows 11 162 37 28 81 34 64 128 256), losses := [] }

theorem u17065 : Upper (D 6) (R 6) [10,160,33,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17066 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 162 37 28 81 36 322 450 322), lower := (rows 11 162 37 28 81 36 64 128 256), losses := [] }

theorem u17066 : Upper (D 6) (R 6) [10,160,33,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17067 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 2 },{ cop := 2, region := 386, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 37 28 81 96 326 390 262), lower := (rows 11 162 37 28 81 96 64 128 256), losses := [] }

theorem u17067 : Upper (D 6) (R 6) [10,160,33,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17068 : Route 9 := (fun mask => (mask,id))

def c17068 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17068 : Upper (D 6) (R 6) [10,160,33,20,65,256] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,65,256] 13 (by decide) (choices 1) [2,4] r17068 c17068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4503
  · exact u4504

def b17069 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 28 82 33 324 452 324), lower := (rows 11 162 37 28 82 33 64 128 256), losses := [] }

theorem u17069 : Upper (D 6) (R 6) [10,160,33,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17070 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 28 82 36 321 449 321), lower := (rows 11 162 37 28 82 36 64 128 256), losses := [] }

theorem u17070 : Upper (D 6) (R 6) [10,160,33,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17071 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 386, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 37 28 82 96 325 389 261), lower := (rows 11 162 37 28 82 96 64 128 256), losses := [{ target := 6, region := (rows 9 6 4 8 16 32 0 140 268), good := (rows 395 162 423 415 18 32 0 128 256) }] }

theorem u17071 : Upper (D 6) (R 6) [10,160,33,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17072 : Route 9 := (fun mask => (mask,id))

def c17072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17072 : Upper (D 6) (R 6) [10,160,33,20,66,256] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,66,256] 13 (by decide) (choices 1) [1,4] r17072 c17072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4505
  · exact u4506

def b17073 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 28 273 34 68 196 324), lower := (rows 11 162 37 28 273 34 64 128 256), losses := [] }

theorem u17073 : Upper (D 6) (R 6) [10,160,33,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17074 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 162 37 28 273 36 66 194 322), lower := (rows 11 162 37 28 273 36 64 128 256), losses := [] }

theorem u17074 : Upper (D 6) (R 6) [10,160,33,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17075 : Route 9 := (fun mask => (mask,id))

def c17075 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17075 : Upper (D 6) (R 6) [10,160,33,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,257,64] 13 (by decide) (choices 1) [2,4] r17075 c17075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4507
  · exact u4508

def b17076 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 28 274 33 68 196 324), lower := (rows 11 162 37 28 274 33 64 128 256), losses := [] }

theorem u17076 : Upper (D 6) (R 6) [10,160,33,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17077 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 28 274 36 65 193 321), lower := (rows 11 162 37 28 274 36 64 128 256), losses := [] }

theorem u17077 : Upper (D 6) (R 6) [10,160,33,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17078 : Route 9 := (fun mask => (mask,id))

def c17078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17078 : Upper (D 6) (R 6) [10,160,33,20,258,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,258,64] 13 (by decide) (choices 1) [1,4] r17078 c17078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4509
  · exact u4510

def b17079 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 28 336 33 70 198 326), lower := (rows 11 162 37 28 336 33 64 128 256), losses := [] }

theorem u17079 : Upper (D 6) (R 6) [10,160,33,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17080 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 28 336 34 69 197 325), lower := (rows 11 162 37 28 336 34 64 128 256), losses := [] }

theorem u17080 : Upper (D 6) (R 6) [10,160,33,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17081 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 28 336 36 67 195 323), lower := (rows 11 162 37 28 336 36 64 128 256), losses := [] }

theorem u17081 : Upper (D 6) (R 6) [10,160,33,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17082 : Route 9 := (fun mask => (mask,id))

def c17082 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17082 : Upper (D 6) (R 6) [10,160,33,20,320,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,320,64] 13 (by decide) (choices 1) [1,2,4] r17082 c17082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4511
  · exact u4512
  · exact u4513

def b17083 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 73 274 36 84 212 340), lower := (rows 11 162 37 73 274 36 64 128 256), losses := [] }

theorem u17083 : Upper (D 6) (R 6) [10,160,33,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17084 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 37 73 274 48 68 196 324), lower := (rows 11 162 37 73 274 48 64 128 256), losses := [] }

theorem u17084 : Upper (D 6) (R 6) [10,160,33,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17084 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17085 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 37 73 274 96 84 148 276), lower := (rows 11 162 37 73 274 96 64 128 256), losses := [] }

theorem u17085 : Upper (D 6) (R 6) [10,160,33,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17086 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 73 276 34 84 212 340), lower := (rows 11 162 37 73 276 34 64 128 256), losses := [] }

theorem u17086 : Upper (D 6) (R 6) [10,160,33,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17087 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 73 276 36 82 210 338), lower := (rows 11 162 37 73 276 36 64 128 256), losses := [] }

theorem u17087 : Upper (D 6) (R 6) [10,160,33,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17088 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 37 73 276 48 70 198 326), lower := (rows 11 162 37 73 276 48 64 128 256), losses := [] }

theorem u17088 : Upper (D 6) (R 6) [10,160,33,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17088 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17089 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 37 73 276 96 86 150 278), lower := (rows 11 162 37 73 276 96 64 128 256), losses := [] }

theorem u17089 : Upper (D 6) (R 6) [10,160,33,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17090 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 73 336 34 84 148 276), lower := (rows 11 162 37 73 336 34 64 128 256), losses := [] }

theorem u17090 : Upper (D 6) (R 6) [10,160,33,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17091 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 73 336 36 86 150 278), lower := (rows 11 162 37 73 336 36 64 128 256), losses := [] }

theorem u17091 : Upper (D 6) (R 6) [10,160,33,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17092 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 37 73 336 48 70 134 262), lower := (rows 11 162 37 73 336 48 64 128 256), losses := [] }

theorem u17092 : Upper (D 6) (R 6) [10,160,33,65,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17092 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17093 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 76 22 33 336 464 336), lower := (rows 11 162 37 76 22 33 64 128 256), losses := [] }

theorem u17093 : Upper (D 6) (R 6) [10,160,33,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17094 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 162 37 76 22 48 321 449 321), lower := (rows 11 162 37 76 22 48 64 128 256), losses := [] }

theorem u17094 : Upper (D 6) (R 6) [10,160,33,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17094 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17095 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(1,6),(4,6)], upper := (rows 11 162 37 76 22 96 337 401 273), lower := (rows 11 162 37 76 22 96 64 128 256), losses := [] }

theorem u17095 : Upper (D 6) (R 6) [10,160,33,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17096 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 37 76 22 288 81 209 337), lower := (rows 11 162 37 76 22 288 64 128 256), losses := [] }

theorem u17096 : Upper (D 6) (R 6) [10,160,33,68,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17096 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17097 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 76 81 34 340 404 276), lower := (rows 11 162 37 76 81 34 64 128 256), losses := [] }

theorem u17097 : Upper (D 6) (R 6) [10,160,33,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17098 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 76 81 36 338 402 274), lower := (rows 11 162 37 76 81 36 64 128 256), losses := [] }

theorem u17098 : Upper (D 6) (R 6) [10,160,33,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17099 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 162 37 76 81 48 326 390 262), lower := (rows 11 162 37 76 81 48 64 128 256), losses := [] }

theorem u17099 : Upper (D 6) (R 6) [10,160,33,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17099 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17099
end Delivery.IrregularNine14.P06
