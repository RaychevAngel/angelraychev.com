import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0251
import IrregularNine14P06C0252

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32520 : Route 9 := (fun mask => (mask,id))

def c32520 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32520 : Upper (D 6) (R 6) [10,96,160,5,257] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,257] 13 (by decide) (choices 1) [2,4,16,64] r32520 c32520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15065
  · exact u15066
  · exact u15067
  · exact u15068

def r32521 : Route 9 := (fun mask => (mask,id))

def c32521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32521 : Upper (D 6) (R 6) [10,96,160,5,258] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,258] 13 (by decide) (choices 1) [1,4,16,64] r32521 c32521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15069
  · exact u15070
  · exact u15071
  · exact u15072

def r32522 : Route 9 := (fun mask => (mask,id))

def c32522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32522 : Upper (D 6) (R 6) [10,96,160,5,260] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,260] 13 (by decide) (choices 1) [1,2,16,64] r32522 c32522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15073
  · exact u15074
  · exact u15075
  · exact u15076

def r32523 : Route 9 := (fun mask => (mask,id))

def c32523 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32523 : Upper (D 6) (R 6) [10,96,160,5,320] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,320] 13 (by decide) (choices 1) [1,2,4,16] r32523 c32523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15077
  · exact u15078
  · exact u15079
  · exact u15080

def b32524 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 164 25 19 356 324 452 324), lower := (rows 11 98 164 25 19 32 64 128 256), losses := [] }

theorem u32524 : Upper (D 6) (R 6) [10,96,160,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32525 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 98 164 25 21 358 326 454 326), lower := (rows 11 98 164 25 21 32 64 128 256), losses := [] }

theorem u32525 : Upper (D 6) (R 6) [10,96,160,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32526 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 164 25 22 357 325 453 325), lower := (rows 11 98 164 25 22 32 64 128 256), losses := [] }

theorem u32526 : Upper (D 6) (R 6) [10,96,160,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32527 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 164 25 81 294 326 390 262), lower := (rows 11 98 164 25 81 32 64 128 256), losses := [] }

theorem u32527 : Upper (D 6) (R 6) [10,96,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32528 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 164 25 82 293 325 389 261), lower := (rows 11 98 164 25 82 32 64 128 256), losses := [] }

theorem u32528 : Upper (D 6) (R 6) [10,96,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32529 : Route 9 := (fun mask => (mask,id))

def c32529 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32529 : Upper (D 6) (R 6) [10,96,160,17,68] 13 := by
  apply FastRouting.sound _ _ [10,96,160,17,68] 13 (by decide) (choices 1) [1,2,4,256] r32529 c32529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15081
  · exact u15082
  · exact u15083
  · exact u15084

def b32530 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 98 164 25 273 102 70 198 326), lower := (rows 11 98 164 25 273 32 64 128 256), losses := [] }

theorem u32530 : Upper (D 6) (R 6) [10,96,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32531 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 164 25 274 101 69 197 325), lower := (rows 11 98 164 25 274 32 64 128 256), losses := [] }

theorem u32531 : Upper (D 6) (R 6) [10,96,160,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32532 : Route 9 := (fun mask => (mask,id))

def c32532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32532 : Upper (D 6) (R 6) [10,96,160,17,260] 13 := by
  apply FastRouting.sound _ _ [10,96,160,17,260] 13 (by decide) (choices 1) [1,2,4,64] r32532 c32532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15085
  · exact u15086
  · exact u15087
  · exact u15088

def r32533 : Route 9 := (fun mask => (mask,id))

def c32533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32533 : Upper (D 6) (R 6) [10,96,160,17,320] 13 := by
  apply FastRouting.sound _ _ [10,96,160,17,320] 13 (by decide) (choices 1) [1,2,4] r32533 c32533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15089
  · exact u15090
  · exact u15091

def b32534 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 164 28 19 357 325 453 325), lower := (rows 11 98 164 28 19 32 64 128 256), losses := [] }

theorem u32534 : Upper (D 6) (R 6) [10,96,160,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32535 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 164 28 21 355 323 451 323), lower := (rows 11 98 164 28 21 32 64 128 256), losses := [] }

theorem u32535 : Upper (D 6) (R 6) [10,96,160,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32536 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 4, region := 8, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 98 164 28 22 353 321 449 321), lower := (rows 11 98 164 28 22 32 64 128 256), losses := [] }

theorem u32536 : Upper (D 6) (R 6) [10,96,160,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32537 : Route 9 := (fun mask => (mask,id))

def c32537 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32537 : Upper (D 6) (R 6) [10,96,160,20,65] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,65] 13 (by decide) (choices 1) [1,2,4,256] r32537 c32537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15092
  · exact u15093
  · exact u15094
  · exact u15095

def b32538 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 164 28 82 293 325 389 261), lower := (rows 11 98 164 28 82 32 64 128 256), losses := [] }

theorem u32538 : Upper (D 6) (R 6) [10,96,160,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32539 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 164 28 84 291 323 387 259), lower := (rows 11 98 164 28 84 32 64 128 256), losses := [] }

theorem u32539 : Upper (D 6) (R 6) [10,96,160,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32540 : Route 9 := (fun mask => (mask,id))

def c32540 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32540 : Upper (D 6) (R 6) [10,96,160,20,257] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,257] 13 (by decide) (choices 1) [1,2,4,64] r32540 c32540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15096
  · exact u15097
  · exact u15098
  · exact u15099

def r32541 : Route 9 := (fun mask => (mask,id))

def c32541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32541 : Upper (D 6) (R 6) [10,96,160,20,258] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,258] 13 (by decide) (choices 1) [1,4,64] r32541 c32541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15100
  · exact u15101
  · exact u15102

def b32542 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 164 28 276 99 67 195 323), lower := (rows 11 98 164 28 276 32 64 128 256), losses := [] }

theorem u32542 : Upper (D 6) (R 6) [10,96,160,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32543 : Route 9 := (fun mask => (mask,id))

def c32543 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32543 : Upper (D 6) (R 6) [10,96,160,20,320] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,320] 13 (by decide) (choices 1) [1,2,4] r32543 c32543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15103
  · exact u15104
  · exact u15105

def b32544 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 164 76 19 309 341 405 277), lower := (rows 11 98 164 76 19 32 64 128 256), losses := [] }

theorem u32544 : Upper (D 6) (R 6) [10,96,160,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32545 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 98 164 76 21 307 339 403 275), lower := (rows 11 98 164 76 21 32 64 128 256), losses := [] }

theorem u32545 : Upper (D 6) (R 6) [10,96,160,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32546 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 98 164 76 22 305 337 401 273), lower := (rows 11 98 164 76 22 32 64 128 256), losses := [] }

theorem u32546 : Upper (D 6) (R 6) [10,96,160,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32547 : Route 9 := (fun mask => (mask,id))

def c32547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32547 : Upper (D 6) (R 6) [10,96,160,68,257] 13 := by
  apply FastRouting.sound _ _ [10,96,160,68,257] 13 (by decide) (choices 1) [1,2,4,16] r32547 c32547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15106
  · exact u15107
  · exact u15108
  · exact u15109

def r32548 : Route 9 := (fun mask => (mask,id))

def c32548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32548 : Upper (D 6) (R 6) [10,96,160,68,258] 13 := by
  apply FastRouting.sound _ _ [10,96,160,68,258] 13 (by decide) (choices 1) [1,4,16] r32548 c32548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15110
  · exact u15111
  · exact u15112

def r32549 : Route 9 := (fun mask => (mask,id))

def c32549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32549 : Upper (D 6) (R 6) [10,96,160,68,260] 13 := by
  apply FastRouting.sound _ _ [10,96,160,68,260] 13 (by decide) (choices 1) [1,2,16] r32549 c32549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15113
  · exact u15114
  · exact u15115

def b32550 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 164 88 19 293 325 389 261), lower := (rows 11 98 164 88 19 32 64 128 256), losses := [] }

theorem u32550 : Upper (D 6) (R 6) [10,96,160,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32551 : Route 9 := (fun mask => (mask,id))

def c32551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32551 : Upper (D 6) (R 6) [10,96,160,80,5] 13 := by
  apply FastRouting.sound _ _ [10,96,160,80,5] 13 (by decide) (choices 1) [1,2,4,256] r32551 c32551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15116
  · exact u15117
  · exact u15118
  · exact u15119

def b32552 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 98 164 88 22 293 325 389 261), lower := (rows 11 98 164 88 22 32 64 128 256), losses := [] }

theorem u32552 : Upper (D 6) (R 6) [10,96,160,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32553 : Route 9 := (fun mask => (mask,id))

def c32553 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32553 : Upper (D 6) (R 6) [10,96,160,80,257] 13 := by
  apply FastRouting.sound _ _ [10,96,160,80,257] 13 (by decide) (choices 1) [1,2,4] r32553 c32553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15120
  · exact u15121
  · exact u15122

def b32554 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 0, region := 164, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 164 88 274 37 69 133 261), lower := (rows 11 98 164 88 274 32 64 128 256), losses := [] }

theorem u32554 : Upper (D 6) (R 6) [10,96,160,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32555 : Route 9 := (fun mask => (mask,id))

def c32555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32555 : Upper (D 6) (R 6) [10,96,160,80,260] 13 := by
  apply FastRouting.sound _ _ [10,96,160,80,260] 13 (by decide) (choices 1) [1,2,4] r32555 c32555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15123
  · exact u15124
  · exact u15125

def b32556 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 164 265 19 116 84 212 340), lower := (rows 11 98 164 265 19 32 64 128 256), losses := [] }

theorem u32556 : Upper (D 6) (R 6) [10,96,160,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32557 : Route 9 := (fun mask => (mask,id))

def c32557 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32557 : Upper (D 6) (R 6) [10,96,160,257,5] 13 := by
  apply FastRouting.sound _ _ [10,96,160,257,5] 13 (by decide) (choices 1) [2,4,16,64] r32557 c32557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15126
  · exact u15127
  · exact u15128
  · exact u15129

def r32558 : Route 9 := (fun mask => (mask,id))

def c32558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32558 : Upper (D 6) (R 6) [10,96,160,257,6] 13 := by
  apply FastRouting.sound _ _ [10,96,160,257,6] 13 (by decide) (choices 1) [1,4,16,64] r32558 c32558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15130
  · exact u15131
  · exact u15132
  · exact u15133

def r32559 : Route 9 := (fun mask => (mask,id))

def c32559 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32559 : Upper (D 6) (R 6) [10,96,160,257,65] 13 := by
  apply FastRouting.sound _ _ [10,96,160,257,65] 13 (by decide) (choices 1) [2,4,16] r32559 c32559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15134
  · exact u15135
  · exact u15136

def b32560 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 164 265 82 53 85 149 277), lower := (rows 11 98 164 265 82 32 64 128 256), losses := [] }

theorem u32560 : Upper (D 6) (R 6) [10,96,160,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32561 : Route 9 := (fun mask => (mask,id))

def c32561 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32561 : Upper (D 6) (R 6) [10,96,160,257,68] 13 := by
  apply FastRouting.sound _ _ [10,96,160,257,68] 13 (by decide) (choices 1) [1,2,4,16] r32561 c32561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15137
  · exact u15138
  · exact u15139
  · exact u15140

def b32562 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 164 268 19 117 85 213 341), lower := (rows 11 98 164 268 19 32 64 128 256), losses := [] }

theorem u32562 : Upper (D 6) (R 6) [10,96,160,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32563 : Route 9 := (fun mask => (mask,id))

def c32563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32563 : Upper (D 6) (R 6) [10,96,160,260,5] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,5] 13 (by decide) (choices 1) [1,2,16,64] r32563 c32563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15141
  · exact u15142
  · exact u15143
  · exact u15144

def r32564 : Route 9 := (fun mask => (mask,id))

def c32564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32564 : Upper (D 6) (R 6) [10,96,160,260,6] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,6] 13 (by decide) (choices 1) [1,16,64] r32564 c32564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15145
  · exact u15146
  · exact u15147

def r32565 : Route 9 := (fun mask => (mask,id))

def c32565 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32565 : Upper (D 6) (R 6) [10,96,160,260,65] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,65] 13 (by decide) (choices 1) [1,2,4,16] r32565 c32565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15148
  · exact u15149
  · exact u15150
  · exact u15151

def b32566 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 164 268 82 53 85 149 277), lower := (rows 11 98 164 268 82 32 64 128 256), losses := [] }

theorem u32566 : Upper (D 6) (R 6) [10,96,160,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32567 : Route 9 := (fun mask => (mask,id))

def c32567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32567 : Upper (D 6) (R 6) [10,96,160,260,68] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,68] 13 (by decide) (choices 1) [1,2,16] r32567 c32567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15152
  · exact u15153
  · exact u15154

def b32568 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 164 280 19 101 69 197 325), lower := (rows 11 98 164 280 19 32 64 128 256), losses := [] }

theorem u32568 : Upper (D 6) (R 6) [10,96,160,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32569 : Route 9 := (fun mask => (mask,id))

def c32569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32569 : Upper (D 6) (R 6) [10,96,160,272,5] 13 := by
  apply FastRouting.sound _ _ [10,96,160,272,5] 13 (by decide) (choices 1) [1,2,4,64] r32569 c32569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15155
  · exact u15156
  · exact u15157
  · exact u15158

def b32570 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 98 164 280 22 101 69 197 325), lower := (rows 11 98 164 280 22 32 64 128 256), losses := [] }

theorem u32570 : Upper (D 6) (R 6) [10,96,160,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32571 : Route 9 := (fun mask => (mask,id))

def c32571 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32571 : Upper (D 6) (R 6) [10,96,160,272,65] 13 := by
  apply FastRouting.sound _ _ [10,96,160,272,65] 13 (by decide) (choices 1) [1,2,4] r32571 c32571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15159
  · exact u15160
  · exact u15161

def b32572 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 164 280 82 37 69 133 261), lower := (rows 11 98 164 280 82 32 64 128 256), losses := [] }

theorem u32572 : Upper (D 6) (R 6) [10,96,160,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32573 : Route 9 := (fun mask => (mask,id))

def c32573 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32573 : Upper (D 6) (R 6) [10,96,160,272,68] 13 := by
  apply FastRouting.sound _ _ [10,96,160,272,68] 13 (by decide) (choices 1) [1,2,4] r32573 c32573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15162
  · exact u15163
  · exact u15164

def b32574 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 164 328 19 53 85 149 277), lower := (rows 11 98 164 328 19 32 64 128 256), losses := [] }

theorem u32574 : Upper (D 6) (R 6) [10,96,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32575 : Route 9 := (fun mask => (mask,id))

def c32575 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32575 : Upper (D 6) (R 6) [10,96,160,320,5] 13 := by
  apply FastRouting.sound _ _ [10,96,160,320,5] 13 (by decide) (choices 1) [1,2,4,16] r32575 c32575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15165
  · exact u15166
  · exact u15167
  · exact u15168

def b32576 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 180, targets := 64 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 98 164 328 22 53 85 149 277), lower := (rows 11 98 164 328 22 32 64 128 256), losses := [] }

theorem u32576 : Upper (D 6) (R 6) [10,96,160,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32577 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 388 13 19 116 116 244 372), lower := (rows 11 98 388 13 19 32 64 128 256), losses := [] }

theorem u32577 : Upper (D 6) (R 6) [10,96,384,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32578 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 388 13 21 114 114 242 370), lower := (rows 11 98 388 13 21 32 64 128 256), losses := [] }

theorem u32578 : Upper (D 6) (R 6) [10,96,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32579 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 388 13 22 113 113 241 369), lower := (rows 11 98 388 13 22 32 64 128 256), losses := [] }

theorem u32579 : Upper (D 6) (R 6) [10,96,384,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32579
end Delivery.IrregularNine14.P06
