import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0302
import IrregularNine14P06C0303

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34500 : Route 9 := (fun mask => (mask,id))

def c34500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34500 : Upper (D 6) (R 6) [10,384,34,20,65] 13 := by
  apply FastRouting.sound _ _ [10,384,34,20,65] 13 (by decide) (choices 1) [1,4,64] r34500 c34500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18131
  · exact u18132
  · exact u18133

def b34501 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 386 38 28 84 97 97 225 353), lower := (rows 11 386 38 28 84 32 64 128 256), losses := [] }

theorem u34501 : Upper (D 6) (R 6) [10,384,34,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34502 : Route 9 := (fun mask => (mask,id))

def c34502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34502 : Upper (D 6) (R 6) [10,384,34,20,96] 13 := by
  apply FastRouting.sound _ _ [10,384,34,20,96] 13 (by decide) (choices 1) [1,4,64] r34502 c34502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18134
  · exact u18135
  · exact u18136

def b34503 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 386 38 56 21 101 69 197 325), lower := (rows 11 386 38 56 21 32 64 128 256), losses := [] }

theorem u34503 : Upper (D 6) (R 6) [10,384,34,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34504 : Route 9 := (fun mask => (mask,id))

def c34504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34504 : Upper (D 6) (R 6) [10,384,34,48,65] 13 := by
  apply FastRouting.sound _ _ [10,384,34,48,65] 13 (by decide) (choices 1) [1,4,64] r34504 c34504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18137
  · exact u18138
  · exact u18139

def r34505 : Route 9 := (fun mask => (mask,id))

def c34505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34505 : Upper (D 6) (R 6) [10,384,34,48,68] 13 := by
  apply FastRouting.sound _ _ [10,384,34,48,68] 13 (by decide) (choices 1) [1,4,64] r34505 c34505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18140
  · exact u18141
  · exact u18142

def b34506 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 386 38 73 21 116 116 244 372), lower := (rows 11 386 38 73 21 32 64 128 256), losses := [] }

theorem u34506 : Upper (D 6) (R 6) [10,384,34,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34507 : Route 9 := (fun mask => (mask,id))

def c34507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34507 : Upper (D 6) (R 6) [10,384,34,65,33] 13 := by
  apply FastRouting.sound _ _ [10,384,34,65,33] 13 (by decide) (choices 1) [4,16,64] r34507 c34507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18143
  · exact u18144
  · exact u18145

def b34508 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 38 73 52 117 85 213 341), lower := (rows 11 386 38 73 52 32 64 128 256), losses := [] }

theorem u34508 : Upper (D 6) (R 6) [10,384,34,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34509 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 386 38 73 81 52 116 180 308), lower := (rows 11 386 38 73 81 32 64 128 256), losses := [] }

theorem u34509 : Upper (D 6) (R 6) [10,384,34,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34510 : Route 9 := (fun mask => (mask,id))

def c34510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34510 : Upper (D 6) (R 6) [10,384,34,65,68] 13 := by
  apply FastRouting.sound _ _ [10,384,34,65,68] 13 (by decide) (choices 1) [1,4,16] r34510 c34510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18146
  · exact u18147
  · exact u18148

def r34511 : Route 9 := (fun mask => (mask,id))

def c34511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34511 : Upper (D 6) (R 6) [10,384,34,65,96] 13 := by
  apply FastRouting.sound _ _ [10,384,34,65,96] 13 (by decide) (choices 1) [1,4,16] r34511 c34511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18149
  · exact u18150
  · exact u18151

def r34512 : Route 9 := (fun mask => (mask,id))

def c34512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34512 : Upper (D 6) (R 6) [10,384,34,68,5] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68,5] 13 (by decide) (choices 1) [1,16,64] r34512 c34512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18152
  · exact u18153
  · exact u18154

def r34513 : Route 9 := (fun mask => (mask,id))

def c34513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34513 : Upper (D 6) (R 6) [10,384,34,68,33] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68,33] 13 (by decide) (choices 1) [1,4,16,64] r34513 c34513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18155
  · exact u18156
  · exact u18157
  · exact u18158

def b34514 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 38 76 52 113 81 209 337), lower := (rows 11 386 38 76 52 32 64 128 256), losses := [] }

theorem u34514 : Upper (D 6) (R 6) [10,384,34,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34515 : Route 9 := (fun mask => (mask,id))

def c34515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34515 : Upper (D 6) (R 6) [10,384,34,68,65] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68,65] 13 (by decide) (choices 1) [1,4,16] r34515 c34515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18159
  · exact u18160
  · exact u18161

def b34516 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 386 38 76 84 49 113 177 305), lower := (rows 11 386 38 76 84 32 64 128 256), losses := [] }

theorem u34516 : Upper (D 6) (R 6) [10,384,34,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34517 : Route 9 := (fun mask => (mask,id))

def c34517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34517 : Upper (D 6) (R 6) [10,384,34,68,96] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68,96] 13 (by decide) (choices 1) [1,4,16] r34517 c34517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18162
  · exact u18163
  · exact u18164

def r34518 : Route 9 := (fun mask => (mask,id))

def c34518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34518 : Upper (D 6) (R 6) [10,384,34,80,5] 13 := by
  apply FastRouting.sound _ _ [10,384,34,80,5] 13 (by decide) (choices 1) [1,4,64] r34518 c34518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18165
  · exact u18166
  · exact u18167

def r34519 : Route 9 := (fun mask => (mask,id))

def c34519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34519 : Upper (D 6) (R 6) [10,384,34,80,33] 13 := by
  apply FastRouting.sound _ _ [10,384,34,80,33] 13 (by decide) (choices 1) [1,4,64] r34519 c34519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18168
  · exact u18169
  · exact u18170

def b34520 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 38 88 52 101 69 197 325), lower := (rows 11 386 38 88 52 32 64 128 256), losses := [] }

theorem u34520 : Upper (D 6) (R 6) [10,384,34,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34521 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 386 38 88 81 37 101 165 293), lower := (rows 11 386 38 88 81 32 64 128 256), losses := [] }

theorem u34521 : Upper (D 6) (R 6) [10,384,34,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34522 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 386 38 88 84 37 101 165 293), lower := (rows 11 386 38 88 84 32 64 128 256), losses := [] }

theorem u34522 : Upper (D 6) (R 6) [10,384,34,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34523 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 386 38 88 112 37 69 133 261), lower := (rows 11 386 38 88 112 32 64 128 256), losses := [] }

theorem u34523 : Upper (D 6) (R 6) [10,384,34,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34524 : Route 9 := (fun mask => (mask,id))

def c34524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34524 : Upper (D 6) (R 6) [10,384,34,96,5] 13 := by
  apply FastRouting.sound _ _ [10,384,34,96,5] 13 (by decide) (choices 1) [1,4,16,64] r34524 c34524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18171
  · exact u18172
  · exact u18173
  · exact u18174

def r34525 : Route 9 := (fun mask => (mask,id))

def c34525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34525 : Upper (D 6) (R 6) [10,384,34,96,65] 13 := by
  apply FastRouting.sound _ _ [10,384,34,96,65] 13 (by decide) (choices 1) [1,4,16] r34525 c34525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18175
  · exact u18176
  · exact u18177

def r34526 : Route 9 := (fun mask => (mask,id))

def c34526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34526 : Upper (D 6) (R 6) [10,384,34,96,68] 13 := by
  apply FastRouting.sound _ _ [10,384,34,96,68] 13 (by decide) (choices 1) [1,4,16] r34526 c34526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18178
  · exact u18179
  · exact u18180

def b34527 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 52 13 19 100 100 228 356), lower := (rows 11 386 52 13 19 32 64 128 256), losses := [] }

theorem u34527 : Upper (D 6) (R 6) [10,384,48,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34528 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 386 52 13 21 98 98 226 354), lower := (rows 11 386 52 13 21 32 64 128 256), losses := [] }

theorem u34528 : Upper (D 6) (R 6) [10,384,48,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34529 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 52 13 22 97 97 225 353), lower := (rows 11 386 52 13 22 32 64 128 256), losses := [] }

theorem u34529 : Upper (D 6) (R 6) [10,384,48,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34530 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 386 52 13 49 102 70 198 326), lower := (rows 11 386 52 13 49 32 64 128 256), losses := [] }

theorem u34530 : Upper (D 6) (R 6) [10,384,48,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34531 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 13 50 101 69 197 325), lower := (rows 11 386 52 13 50 32 64 128 256), losses := [] }

theorem u34531 : Upper (D 6) (R 6) [10,384,48,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34532 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 386 52 13 52 99 67 195 323), lower := (rows 11 386 52 13 52 32 64 128 256), losses := [] }

theorem u34532 : Upper (D 6) (R 6) [10,384,48,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34533 : Route 9 := (fun mask => (mask,id))

def c34533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34533 : Upper (D 6) (R 6) [10,384,48,5,65] 13 := by
  apply FastRouting.sound _ _ [10,384,48,5,65] 13 (by decide) (choices 1) [2,4,64] r34533 c34533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18181
  · exact u18182
  · exact u18183

def r34534 : Route 9 := (fun mask => (mask,id))

def c34534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34534 : Upper (D 6) (R 6) [10,384,48,5,66] 13 := by
  apply FastRouting.sound _ _ [10,384,48,5,66] 13 (by decide) (choices 1) [1,4,64] r34534 c34534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18184
  · exact u18185
  · exact u18186

def r34535 : Route 9 := (fun mask => (mask,id))

def c34535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34535 : Upper (D 6) (R 6) [10,384,48,5,68] 13 := by
  apply FastRouting.sound _ _ [10,384,48,5,68] 13 (by decide) (choices 1) [1,2,64] r34535 c34535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18187
  · exact u18188
  · exact u18189

def b34536 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 13 112 103 71 199 327), lower := (rows 11 386 52 13 112 32 64 128 256), losses := [] }

theorem u34536 : Upper (D 6) (R 6) [10,384,48,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34537 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 52 41 19 100 68 196 324), lower := (rows 11 386 52 41 19 32 64 128 256), losses := [] }

theorem u34537 : Upper (D 6) (R 6) [10,384,48,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34538 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 386 52 41 21 102 70 198 326), lower := (rows 11 386 52 41 21 32 64 128 256), losses := [] }

theorem u34538 : Upper (D 6) (R 6) [10,384,48,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34539 : PairBound 9 := { available := 69, camps := [], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 386 52 41 22 101 69 197 325), lower := (rows 11 386 52 41 22 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 32 64 128 256), good := (rows 30 386 52 60 22 32 64 128 256) },{ target := 2, region := (rows 17 2 0 12 16 32 64 128 256), good := (rows 11 386 57 41 27 32 64 128 256) }] }

theorem u34539 : Upper (D 6) (R 6) [10,384,48,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34540 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 386 52 41 81 102 70 198 326), lower := (rows 11 386 52 41 81 32 64 128 256), losses := [] }

theorem u34540 : Upper (D 6) (R 6) [10,384,48,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34541 : Route 9 := (fun mask => (mask,id))

def c34541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34541 : Upper (D 6) (R 6) [10,384,48,33,66] 13 := by
  apply FastRouting.sound _ _ [10,384,48,33,66] 13 (by decide) (choices 1) [1,4,64] r34541 c34541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18190
  · exact u18191
  · exact u18192

def r34542 : Route 9 := (fun mask => (mask,id))

def c34542 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34542 : Upper (D 6) (R 6) [10,384,48,33,68] 13 := by
  apply FastRouting.sound _ _ [10,384,48,33,68] 13 (by decide) (choices 1) [1,2,4,64] r34542 c34542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18193
  · exact u18194
  · exact u18195
  · exact u18196

def b34543 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 52 73 19 100 100 228 356), lower := (rows 11 386 52 73 19 32 64 128 256), losses := [] }

theorem u34543 : Upper (D 6) (R 6) [10,384,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34544 : Route 9 := (fun mask => (mask,id))

def c34544 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34544 : Upper (D 6) (R 6) [10,384,48,65,5] 13 := by
  apply FastRouting.sound _ _ [10,384,48,65,5] 13 (by decide) (choices 1) [2,4,64] r34544 c34544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18197
  · exact u18198
  · exact u18199

def r34545 : Route 9 := (fun mask => (mask,id))

def c34545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34545 : Upper (D 6) (R 6) [10,384,48,65,6] 13 := by
  apply FastRouting.sound _ _ [10,384,48,65,6] 13 (by decide) (choices 1) [1,4,64] r34545 c34545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18200
  · exact u18201
  · exact u18202

def b34546 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 73 49 102 70 198 326), lower := (rows 11 386 52 73 49 32 64 128 256), losses := [] }

theorem u34546 : Upper (D 6) (R 6) [10,384,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34547 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 73 50 101 69 197 325), lower := (rows 11 386 52 73 50 32 64 128 256), losses := [] }

theorem u34547 : Upper (D 6) (R 6) [10,384,48,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34548 : PairBound 9 := { available := 71, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 386 52 73 52 103 71 199 327), lower := (rows 11 386 52 73 52 32 64 128 256), losses := [] }

theorem u34548 : Upper (D 6) (R 6) [10,384,48,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34549 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 386 52 73 81 38 102 166 294), lower := (rows 11 386 52 73 81 32 64 128 256), losses := [] }

theorem u34549 : Upper (D 6) (R 6) [10,384,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34550 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 386 52 73 82 37 101 165 293), lower := (rows 11 386 52 73 82 32 64 128 256), losses := [] }

theorem u34550 : Upper (D 6) (R 6) [10,384,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34551 : Route 9 := (fun mask => (mask,id))

def c34551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34551 : Upper (D 6) (R 6) [10,384,48,65,68] 13 := by
  apply FastRouting.sound _ _ [10,384,48,65,68] 13 (by decide) (choices 1) [1,2,4] r34551 c34551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18203
  · exact u18204
  · exact u18205

def b34552 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 73 112 39 71 135 263), lower := (rows 11 386 52 73 112 32 64 128 256), losses := [] }

theorem u34552 : Upper (D 6) (R 6) [10,384,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34553 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 52 76 19 101 101 229 357), lower := (rows 11 386 52 76 19 32 64 128 256), losses := [] }

theorem u34553 : Upper (D 6) (R 6) [10,384,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34554 : Route 9 := (fun mask => (mask,id))

def c34554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34554 : Upper (D 6) (R 6) [10,384,48,68,5] 13 := by
  apply FastRouting.sound _ _ [10,384,48,68,5] 13 (by decide) (choices 1) [1,2,64] r34554 c34554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18206
  · exact u18207
  · exact u18208

def r34555 : Route 9 := (fun mask => (mask,id))

def c34555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34555 : Upper (D 6) (R 6) [10,384,48,68,6] 13 := by
  apply FastRouting.sound _ _ [10,384,48,68,6] 13 (by decide) (choices 1) [1,64] r34555 c34555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18209
  · exact u18210

def b34556 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 76 49 103 71 199 327), lower := (rows 11 386 52 76 49 32 64 128 256), losses := [] }

theorem u34556 : Upper (D 6) (R 6) [10,384,48,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34557 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 52 76 50 101 69 197 325), lower := (rows 11 386 52 76 50 32 64 128 256), losses := [] }

theorem u34557 : Upper (D 6) (R 6) [10,384,48,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34558 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 386 52 76 52 99 67 195 323), lower := (rows 11 386 52 76 52 32 64 128 256), losses := [] }

theorem u34558 : Upper (D 6) (R 6) [10,384,48,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34559 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 52 76 81 39 103 167 295), lower := (rows 11 386 52 76 81 32 64 128 256), losses := [] }

theorem u34559 : Upper (D 6) (R 6) [10,384,48,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34559
end Delivery.IrregularNine14.P06
