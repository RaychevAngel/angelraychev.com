import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0168
import IrregularNine14P07C0169

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27480 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 322 69 26 145 34 232 168 424), lower := (rows 37 322 69 26 145 34 64 128 256), losses := [] }

theorem u27480 : Upper (D 7) (R 7) [36,320,65,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27481 : Route 9 := (fun mask => (mask,id))

def c27481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27481 : Upper (D 7) (R 7) [36,320,65,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,129,8] 13 (by decide) (choices 1) [2,32,128] r27481 c27481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10102
  · exact u10103
  · exact u10104

def r27482 : Route 9 := (fun mask => (mask,id))

def c27482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27482 : Upper (D 7) (R 7) [36,320,65,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,129,128] 13 (by decide) (choices 1) [2,8,32] r27482 c27482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10105
  · exact u10106
  · exact u10107

def b27483 : PairBound 9 := { available := 162, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 26 152 33 226 162 418), lower := (rows 37 322 69 26 152 33 64 128 256), losses := [] }

theorem u27483 : Upper (D 7) (R 7) [36,320,65,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27484 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 26 152 34 225 161 417), lower := (rows 37 322 69 26 152 34 64 128 256), losses := [] }

theorem u27484 : Upper (D 7) (R 7) [36,320,65,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27485 : Route 9 := (fun mask => (mask,id))

def c27485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27485 : Upper (D 7) (R 7) [36,320,65,18,136,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,136,128] 13 (by decide) (choices 1) [1,2,32] r27485 c27485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10108
  · exact u10109
  · exact u10110

def b27486 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 322 69 26 176 33 202 138 394), lower := (rows 37 322 69 26 176 33 64 128 256), losses := [] }

theorem u27486 : Upper (D 7) (R 7) [36,320,65,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27487 : Route 9 := (fun mask => (mask,id))

def c27487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27487 : Upper (D 7) (R 7) [36,320,65,18,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,160,2] 13 (by decide) (choices 1) [1,8,128] r27487 c27487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10111
  · exact u10112
  · exact u10113

def r27488 : Route 9 := (fun mask => (mask,id))

def c27488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27488 : Upper (D 7) (R 7) [36,320,65,18,160,8] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,160,8] 13 (by decide) (choices 1) [1,2,128] r27488 c27488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10114
  · exact u10115
  · exact u10116

def b27489 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 69 26 176 160 75 139 267), lower := (rows 37 322 69 26 176 160 64 128 256), losses := [] }

theorem u27489 : Upper (D 7) (R 7) [36,320,65,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27490 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 322 69 42 145 34 216 152 408), lower := (rows 37 322 69 42 145 34 64 128 256), losses := [] }

theorem u27490 : Upper (D 7) (R 7) [36,320,65,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27491 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 69 42 145 40 210 146 402), lower := (rows 37 322 69 42 145 40 64 128 256), losses := [] }

theorem u27491 : Upper (D 7) (R 7) [36,320,65,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27491 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27492 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 322 69 42 145 48 202 138 394), lower := (rows 37 322 69 42 145 48 64 128 256), losses := [] }

theorem u27492 : Upper (D 7) (R 7) [36,320,65,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27492 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27493 : Route 9 := (fun mask => (mask,id))

def c27493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27493 : Upper (D 7) (R 7) [36,320,65,34,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,129,128] 13 (by decide) (choices 1) [2,8,16] r27493 c27493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10117
  · exact u10118
  · exact u10119

def b27494 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 69 42 146 33 216 152 408), lower := (rows 37 322 69 42 146 33 64 128 256), losses := [] }

theorem u27494 : Upper (D 7) (R 7) [36,320,65,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27495 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 69 42 146 40 209 145 401), lower := (rows 37 322 69 42 146 40 64 128 256), losses := [] }

theorem u27495 : Upper (D 7) (R 7) [36,320,65,34,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27495 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27496 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 322 69 42 146 48 201 137 393), lower := (rows 37 322 69 42 146 48 64 128 256), losses := [] }

theorem u27496 : Upper (D 7) (R 7) [36,320,65,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27496 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27497 : Route 9 := (fun mask => (mask,id))

def c27497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27497 : Upper (D 7) (R 7) [36,320,65,34,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,130,128] 13 (by decide) (choices 1) [1,8,16] r27497 c27497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10120
  · exact u10121
  · exact u10122

def b27498 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 69 42 152 33 210 146 402), lower := (rows 37 322 69 42 152 33 64 128 256), losses := [] }

theorem u27498 : Upper (D 7) (R 7) [36,320,65,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27499 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 322 69 42 152 34 209 145 401), lower := (rows 37 322 69 42 152 34 64 128 256), losses := [] }

theorem u27499 : Upper (D 7) (R 7) [36,320,65,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27500 : Route 9 := (fun mask => (mask,id))

def c27500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27500 : Upper (D 7) (R 7) [36,320,65,34,136,16] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,136,16] 13 (by decide) (choices 1) [1,2,128] r27500 c27500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10123
  · exact u10124
  · exact u10125

def r27501 : Route 9 := (fun mask => (mask,id))

def c27501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27501 : Upper (D 7) (R 7) [36,320,65,34,136,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,136,128] 13 (by decide) (choices 1) [1,2,16] r27501 c27501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10126
  · exact u10127
  · exact u10128

def b27502 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 322 69 56 145 34 202 138 394), lower := (rows 37 322 69 56 145 34 64 128 256), losses := [] }

theorem u27502 : Upper (D 7) (R 7) [36,320,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27503 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 69 56 145 40 194 130 386), lower := (rows 37 322 69 56 145 40 64 128 256), losses := [] }

theorem u27503 : Upper (D 7) (R 7) [36,320,65,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27503 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27504 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 322 69 56 145 160 74 138 266), lower := (rows 37 322 69 56 145 160 64 128 256), losses := [] }

theorem u27504 : Upper (D 7) (R 7) [36,320,65,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27505 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 69 56 146 33 202 138 394), lower := (rows 37 322 69 56 146 33 64 128 256), losses := [] }

theorem u27505 : Upper (D 7) (R 7) [36,320,65,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27506 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(3,7)], upper := (rows 37 322 69 56 146 34 201 137 393), lower := (rows 37 322 69 56 146 34 64 128 256), losses := [] }

theorem u27506 : Upper (D 7) (R 7) [36,320,65,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27507 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 322 69 56 146 40 195 131 387), lower := (rows 37 322 69 56 146 40 64 128 256), losses := [] }

theorem u27507 : Upper (D 7) (R 7) [36,320,65,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27507 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27508 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 322 69 56 146 160 75 139 267), lower := (rows 37 322 69 56 146 160 64 128 256), losses := [] }

theorem u27508 : Upper (D 7) (R 7) [36,320,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27509 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 69 56 152 33 194 130 386), lower := (rows 37 322 69 56 152 33 64 128 256), losses := [] }

theorem u27509 : Upper (D 7) (R 7) [36,320,65,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27510 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 37 322 69 56 152 34 195 131 387), lower := (rows 37 322 69 56 152 34 64 128 256), losses := [] }

theorem u27510 : Upper (D 7) (R 7) [36,320,65,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27511 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 37 322 69 56 152 160 67 131 259), lower := (rows 37 322 69 56 152 160 64 128 256), losses := [] }

theorem u27511 : Upper (D 7) (R 7) [36,320,65,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27512 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 69 137 146 34 120 184 312), lower := (rows 37 322 69 137 146 34 64 128 256), losses := [] }

theorem u27512 : Upper (D 7) (R 7) [36,320,65,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27513 : Route 9 := (fun mask => (mask,id))

def c27513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27513 : Upper (D 7) (R 7) [36,320,65,129,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,65,129,130,8] 13 (by decide) (choices 1) [2,16,32] r27513 c27513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10129
  · exact u10130
  · exact u10131

def r27514 : Route 9 := (fun mask => (mask,id))

def c27514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27514 : Upper (D 7) (R 7) [36,320,65,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,320,65,129,130,16] 13 (by decide) (choices 1) [2,8,32] r27514 c27514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10132
  · exact u10133
  · exact u10134

def b27515 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 69 137 176 34 90 154 282), lower := (rows 37 322 69 137 176 34 64 128 256), losses := [] }

theorem u27515 : Upper (D 7) (R 7) [36,320,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27516 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 69 137 176 40 82 146 274), lower := (rows 37 322 69 137 176 40 64 128 256), losses := [] }

theorem u27516 : Upper (D 7) (R 7) [36,320,65,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27516 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27517 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 69 137 176 48 74 138 266), lower := (rows 37 322 69 137 176 48 64 128 256), losses := [] }

theorem u27517 : Upper (D 7) (R 7) [36,320,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27517 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27518 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 322 69 138 176 33 90 154 282), lower := (rows 37 322 69 138 176 33 64 128 256), losses := [] }

theorem u27518 : Upper (D 7) (R 7) [36,320,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27519 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 48, targets := 65 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 37 322 69 138 176 34 89 153 281), lower := (rows 37 322 69 138 176 34 64 128 256), losses := [] }

theorem u27519 : Upper (D 7) (R 7) [36,320,65,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27520 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 322 69 138 176 40 83 147 275), lower := (rows 37 322 69 138 176 40 64 128 256), losses := [] }

theorem u27520 : Upper (D 7) (R 7) [36,320,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27520 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27521 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 69 138 176 48 75 139 267), lower := (rows 37 322 69 138 176 48 64 128 256), losses := [] }

theorem u27521 : Upper (D 7) (R 7) [36,320,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27521 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27522 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 76 11 50 33 208 144 400), lower := (rows 37 322 76 11 50 33 64 128 256), losses := [] }

theorem u27522 : Upper (D 7) (R 7) [36,320,72,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27523 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 76 11 50 48 193 129 385), lower := (rows 37 322 76 11 50 48 64 128 256), losses := [] }

theorem u27523 : Upper (D 7) (R 7) [36,320,72,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27523 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27524 : Route 9 := (fun mask => (mask,id))

def c27524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27524 : Upper (D 7) (R 7) [36,320,72,3,34,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,34,128] 13 (by decide) (choices 1) [1,16,128] r27524 c27524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10135
  · exact u10136
  · exact u10137

def b27525 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 322 76 11 145 34 240 176 432), lower := (rows 37 322 76 11 145 34 64 128 256), losses := [] }

theorem u27525 : Upper (D 7) (R 7) [36,320,72,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27526 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 3, region := 176, targets := 64 }], pairs := [(1,0),(2,0),(4,6)], upper := (rows 37 322 76 11 145 48 226 162 418), lower := (rows 37 322 76 11 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 59 12 8 16 48 113 177 305), good := (rows 486 322 78 462 498 498 64 128 256) }] }

theorem u27526 : Upper (D 7) (R 7) [36,320,72,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27526 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27527 : Route 9 := (fun mask => (mask,id))

def c27527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27527 : Upper (D 7) (R 7) [36,320,72,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,129,128] 13 (by decide) (choices 1) [2,16,32] r27527 c27527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10138
  · exact u10139
  · exact u10140

def b27528 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 76 11 146 33 240 176 432), lower := (rows 37 322 76 11 146 33 64 128 256), losses := [] }

theorem u27528 : Upper (D 7) (R 7) [36,320,72,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27529 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 37 322 76 11 146 48 225 161 417), lower := (rows 37 322 76 11 146 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 48 65 129 257), good := (rows 485 320 76 461 176 48 64 128 256) },{ target := 6, region := (rows 5 2 4 8 24 60 0 141 269), good := (rows 421 258 445 443 178 48 0 128 256) }] }

theorem u27529 : Upper (D 7) (R 7) [36,320,72,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27529 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27530 : Route 9 := (fun mask => (mask,id))

def c27530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27530 : Upper (D 7) (R 7) [36,320,72,3,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,130,128] 13 (by decide) (choices 1) [1,16,32] r27530 c27530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10141
  · exact u10142
  · exact u10143

def b27531 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 76 11 176 33 210 146 402), lower := (rows 37 322 76 11 176 33 64 128 256), losses := [] }

theorem u27531 : Upper (D 7) (R 7) [36,320,72,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27532 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 322 76 11 176 34 209 145 401), lower := (rows 37 322 76 11 176 34 64 128 256), losses := [] }

theorem u27532 : Upper (D 7) (R 7) [36,320,72,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27533 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 76 11 176 48 195 131 387), lower := (rows 37 322 76 11 176 48 64 128 256), losses := [] }

theorem u27533 : Upper (D 7) (R 7) [36,320,72,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27533 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27534 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 76 11 176 160 83 147 275), lower := (rows 37 322 76 11 176 160 64 128 256), losses := [] }

theorem u27534 : Upper (D 7) (R 7) [36,320,72,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27535 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 76 25 50 33 194 130 386), lower := (rows 37 322 76 25 50 33 64 128 256), losses := [] }

theorem u27535 : Upper (D 7) (R 7) [36,320,72,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27536 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 76 25 50 34 193 129 385), lower := (rows 37 322 76 25 50 34 64 128 256), losses := [] }

theorem u27536 : Upper (D 7) (R 7) [36,320,72,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27537 : Route 9 := (fun mask => (mask,id))

def c27537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27537 : Upper (D 7) (R 7) [36,320,72,17,34,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,34,128] 13 (by decide) (choices 1) [1,2,128] r27537 c27537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10144
  · exact u10145
  · exact u10146

def b27538 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 76 25 146 33 226 162 418), lower := (rows 37 322 76 25 146 33 64 128 256), losses := [] }

theorem u27538 : Upper (D 7) (R 7) [36,320,72,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27539 : Route 9 := (fun mask => (mask,id))

def c27539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27539 : Upper (D 7) (R 7) [36,320,72,17,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,130,2] 13 (by decide) (choices 1) [1,32,128] r27539 c27539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10147
  · exact u10148
  · exact u10149

#print axioms u27539
end Delivery.IrregularNine14.P07
