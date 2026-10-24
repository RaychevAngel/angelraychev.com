import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0432
import IrregularNine14P06C0433
import IrregularNine14P06C0434

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39540 : PairBound 9 := { available := 325, camps := [], pairs := [(0,1),(2,5),(4,5)], upper := (rows 41 98 134 26 21 357 325 453 325), lower := (rows 41 98 134 26 21 32 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 48 80 144 272), good := (rows 41 96 132 505 501 32 64 128 256) },{ target := 5, region := (rows 1 2 12 8 17 0 81 145 273), good := (rows 477 66 134 478 469 0 64 128 256) }] }

theorem u39540 : Upper (D 6) (R 6) [40,96,130,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39541 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 26 81 293 325 389 261), lower := (rows 41 98 134 26 81 32 64 128 256), losses := [] }

theorem u39541 : Upper (D 6) (R 6) [40,96,130,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39542 : Route 9 := (fun mask => (mask,id))

def c39542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39542 : Upper (D 6) (R 6) [40,96,130,18,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18,68] 13 (by decide) (choices 1) [1,4,256] r39542 c39542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25972
  · exact u25973
  · exact u25974

def r39543 : Route 9 := (fun mask => (mask,id))

def c39543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39543 : Upper (D 6) (R 6) [40,96,130,18,257] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18,257] 13 (by decide) (choices 1) [1,4,64] r39543 c39543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25975
  · exact u25976
  · exact u25977

def r39544 : Route 9 := (fun mask => (mask,id))

def c39544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39544 : Upper (D 6) (R 6) [40,96,130,18,260] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18,260] 13 (by decide) (choices 1) [1,4,64] r39544 c39544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25978
  · exact u25979
  · exact u25980

def r39545 : Route 9 := (fun mask => (mask,id))

def c39545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39545 : Upper (D 6) (R 6) [40,96,130,18,320] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18,320] 13 (by decide) (choices 1) [1,4] r39545 c39545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25981
  · exact u25982

def b39546 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 3, region := 353, targets := 2 }], pairs := [(0,1),(2,5),(3,5)], upper := (rows 41 98 134 28 19 357 325 453 325), lower := (rows 41 98 134 28 19 32 64 128 256), losses := [] }

theorem u39546 : Upper (D 6) (R 6) [40,96,130,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39547 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 134 28 21 355 323 451 323), lower := (rows 41 98 134 28 21 32 64 128 256), losses := [] }

theorem u39547 : Upper (D 6) (R 6) [40,96,130,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39548 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 98 134 28 22 353 321 449 321), lower := (rows 41 98 134 28 22 32 64 128 256), losses := [] }

theorem u39548 : Upper (D 6) (R 6) [40,96,130,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39549 : Route 9 := (fun mask => (mask,id))

def c39549 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39549 : Upper (D 6) (R 6) [40,96,130,20,65] 13 := by
  apply FastRouting.sound _ _ [40,96,130,20,65] 13 (by decide) (choices 1) [1,2,4,256] r39549 c39549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25983
  · exact u25984
  · exact u25985
  · exact u25986

def b39550 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 134 28 82 293 325 389 261), lower := (rows 41 98 134 28 82 32 64 128 256), losses := [] }

theorem u39550 : Upper (D 6) (R 6) [40,96,130,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39551 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 134 28 84 291 323 387 259), lower := (rows 41 98 134 28 84 32 64 128 256), losses := [] }

theorem u39551 : Upper (D 6) (R 6) [40,96,130,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39552 : Route 9 := (fun mask => (mask,id))

def c39552 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39552 : Upper (D 6) (R 6) [40,96,130,20,257] 13 := by
  apply FastRouting.sound _ _ [40,96,130,20,257] 13 (by decide) (choices 1) [1,2,4,64] r39552 c39552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25987
  · exact u25988
  · exact u25989
  · exact u25990

def r39553 : Route 9 := (fun mask => (mask,id))

def c39553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39553 : Upper (D 6) (R 6) [40,96,130,20,258] 13 := by
  apply FastRouting.sound _ _ [40,96,130,20,258] 13 (by decide) (choices 1) [1,4,64] r39553 c39553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25991
  · exact u25992
  · exact u25993

def b39554 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 134 28 276 99 67 195 323), lower := (rows 41 98 134 28 276 32 64 128 256), losses := [] }

theorem u39554 : Upper (D 6) (R 6) [40,96,130,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39555 : Route 9 := (fun mask => (mask,id))

def c39555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39555 : Upper (D 6) (R 6) [40,96,130,20,320] 13 := by
  apply FastRouting.sound _ _ [40,96,130,20,320] 13 (by decide) (choices 1) [1,2,4] r39555 c39555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25994
  · exact u25995
  · exact u25996

def b39556 : PairBound 9 := { available := 277, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 134 76 19 309 341 405 277), lower := (rows 41 98 134 76 19 32 64 128 256), losses := [] }

theorem u39556 : Upper (D 6) (R 6) [40,96,130,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39557 : Route 9 := (fun mask => (mask,id))

def c39557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39557 : Upper (D 6) (R 6) [40,96,130,68,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,5] 13 (by decide) (choices 1) [1,2,16,256] r39557 c39557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25997
  · exact u25998
  · exact u25999
  · exact u26000

def b39558 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 76 22 305 337 401 273), lower := (rows 41 98 134 76 22 32 64 128 256), losses := [] }

theorem u39558 : Upper (D 6) (R 6) [40,96,130,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39559 : Route 9 := (fun mask => (mask,id))

def c39559 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39559 : Upper (D 6) (R 6) [40,96,130,68,257] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,257] 13 (by decide) (choices 1) [1,2,4,16] r39559 c39559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26001
  · exact u26002
  · exact u26003
  · exact u26004

def r39560 : Route 9 := (fun mask => (mask,id))

def c39560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39560 : Upper (D 6) (R 6) [40,96,130,68,258] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,258] 13 (by decide) (choices 1) [1,4,16] r39560 c39560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26005
  · exact u26006
  · exact u26007

def r39561 : Route 9 := (fun mask => (mask,id))

def c39561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39561 : Upper (D 6) (R 6) [40,96,130,68,260] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,260] 13 (by decide) (choices 1) [1,2,16] r39561 c39561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26008
  · exact u26009
  · exact u26010

def b39562 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 88 19 293 325 389 261), lower := (rows 41 98 134 88 19 32 64 128 256), losses := [] }

theorem u39562 : Upper (D 6) (R 6) [40,96,130,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39563 : Route 9 := (fun mask => (mask,id))

def c39563 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39563 : Upper (D 6) (R 6) [40,96,130,80,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,5] 13 (by decide) (choices 1) [1,2,4,256] r39563 c39563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26011
  · exact u26012
  · exact u26013
  · exact u26014

def b39564 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 88 22 293 325 389 261), lower := (rows 41 98 134 88 22 32 64 128 256), losses := [] }

theorem u39564 : Upper (D 6) (R 6) [40,96,130,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39565 : Route 9 := (fun mask => (mask,id))

def c39565 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39565 : Upper (D 6) (R 6) [40,96,130,80,257] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,257] 13 (by decide) (choices 1) [1,2,4] r39565 c39565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26015
  · exact u26016
  · exact u26017

def r39566 : Route 9 := (fun mask => (mask,id))

def c39566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39566 : Upper (D 6) (R 6) [40,96,130,80,258] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,258] 13 (by decide) (choices 1) [1,4] r39566 c39566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26018
  · exact u26019

def r39567 : Route 9 := (fun mask => (mask,id))

def c39567 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39567 : Upper (D 6) (R 6) [40,96,130,80,260] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,260] 13 (by decide) (choices 1) [1,2,4] r39567 c39567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26020
  · exact u26021
  · exact u26022

def b39568 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 134 265 19 116 84 212 340), lower := (rows 41 98 134 265 19 32 64 128 256), losses := [] }

theorem u39568 : Upper (D 6) (R 6) [40,96,130,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39569 : Route 9 := (fun mask => (mask,id))

def c39569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39569 : Upper (D 6) (R 6) [40,96,130,257,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257,5] 13 (by decide) (choices 1) [2,4,16,64] r39569 c39569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26023
  · exact u26024
  · exact u26025
  · exact u26026

def b39570 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 265 22 117 85 213 341), lower := (rows 41 98 134 265 22 32 64 128 256), losses := [] }

theorem u39570 : Upper (D 6) (R 6) [40,96,130,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39571 : Route 9 := (fun mask => (mask,id))

def c39571 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39571 : Upper (D 6) (R 6) [40,96,130,257,65] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257,65] 13 (by decide) (choices 1) [2,4,16] r39571 c39571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26027
  · exact u26028
  · exact u26029

def b39572 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 134 265 82 53 85 149 277), lower := (rows 41 98 134 265 82 32 64 128 256), losses := [] }

theorem u39572 : Upper (D 6) (R 6) [40,96,130,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39573 : Route 9 := (fun mask => (mask,id))

def c39573 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39573 : Upper (D 6) (R 6) [40,96,130,257,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257,68] 13 (by decide) (choices 1) [1,2,4,16] r39573 c39573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26030
  · exact u26031
  · exact u26032
  · exact u26033

def r39574 : Route 9 := (fun mask => (mask,id))

def c39574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39574 : Upper (D 6) (R 6) [40,96,130,258,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,5] 13 (by decide) (choices 1) [1,4,16,64] r39574 c39574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26034
  · exact u26035
  · exact u26036
  · exact u26037

def r39575 : Route 9 := (fun mask => (mask,id))

def c39575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39575 : Upper (D 6) (R 6) [40,96,130,258,65] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,65] 13 (by decide) (choices 1) [1,4,16] r39575 c39575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26038
  · exact u26039
  · exact u26040

def r39576 : Route 9 := (fun mask => (mask,id))

def c39576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39576 : Upper (D 6) (R 6) [40,96,130,258,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,68] 13 (by decide) (choices 1) [1,4,16] r39576 c39576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26041
  · exact u26042
  · exact u26043

def r39577 : Route 9 := (fun mask => (mask,id))

def c39577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39577 : Upper (D 6) (R 6) [40,96,130,260,3] 13 := by
  apply FastRouting.sound _ _ [40,96,130,260,3] 13 (by decide) (choices 1) [1,4,16,64] r39577 c39577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26044
  · exact u26045
  · exact u26046
  · exact u26047

def r39578 : Route 9 := (fun mask => (mask,id))

def c39578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39578 : Upper (D 6) (R 6) [40,96,130,260,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,260,5] 13 (by decide) (choices 1) [1,2,16,64] r39578 c39578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26048
  · exact u26049
  · exact u26050
  · exact u26051

def b39579 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 268 22 113 81 209 337), lower := (rows 41 98 134 268 22 32 64 128 256), losses := [] }

theorem u39579 : Upper (D 6) (R 6) [40,96,130,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39580 : Route 9 := (fun mask => (mask,id))

def c39580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39580 : Upper (D 6) (R 6) [40,96,130,260,65] 13 := by
  apply FastRouting.sound _ _ [40,96,130,260,65] 13 (by decide) (choices 1) [1,2,4,16] r39580 c39580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26052
  · exact u26053
  · exact u26054
  · exact u26055

def b39581 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 134 268 82 53 85 149 277), lower := (rows 41 98 134 268 82 32 64 128 256), losses := [] }

theorem u39581 : Upper (D 6) (R 6) [40,96,130,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39582 : Route 9 := (fun mask => (mask,id))

def c39582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39582 : Upper (D 6) (R 6) [40,96,130,260,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,260,68] 13 (by decide) (choices 1) [1,2,16] r39582 c39582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26056
  · exact u26057
  · exact u26058

def r39583 : Route 9 := (fun mask => (mask,id))

def c39583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39583 : Upper (D 6) (R 6) [40,96,130,272,3] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272,3] 13 (by decide) (choices 1) [1,4,64] r39583 c39583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26059
  · exact u26060
  · exact u26061

def r39584 : Route 9 := (fun mask => (mask,id))

def c39584 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39584 : Upper (D 6) (R 6) [40,96,130,272,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272,5] 13 (by decide) (choices 1) [1,2,4,64] r39584 c39584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26062
  · exact u26063
  · exact u26064
  · exact u26065

def b39585 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 280 22 101 69 197 325), lower := (rows 41 98 134 280 22 32 64 128 256), losses := [] }

theorem u39585 : Upper (D 6) (R 6) [40,96,130,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39586 : Route 9 := (fun mask => (mask,id))

def c39586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39586 : Upper (D 6) (R 6) [40,96,130,272,65] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272,65] 13 (by decide) (choices 1) [1,2,4] r39586 c39586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26066
  · exact u26067
  · exact u26068

def b39587 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 134 280 82 37 69 133 261), lower := (rows 41 98 134 280 82 32 64 128 256), losses := [] }

theorem u39587 : Upper (D 6) (R 6) [40,96,130,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39588 : Route 9 := (fun mask => (mask,id))

def c39588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39588 : Upper (D 6) (R 6) [40,96,130,272,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272,68] 13 (by decide) (choices 1) [1,2,4] r39588 c39588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26069
  · exact u26070
  · exact u26071

def b39589 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 134 328 19 53 85 149 277), lower := (rows 41 98 134 328 19 32 64 128 256), losses := [] }

theorem u39589 : Upper (D 6) (R 6) [40,96,130,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39590 : Route 9 := (fun mask => (mask,id))

def c39590 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39590 : Upper (D 6) (R 6) [40,96,130,320,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,320,5] 13 (by decide) (choices 1) [1,2,4,16] r39590 c39590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26072
  · exact u26073
  · exact u26074
  · exact u26075

def b39591 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 328 22 53 85 149 277), lower := (rows 41 98 134 328 22 32 64 128 256), losses := [] }

theorem u39591 : Upper (D 6) (R 6) [40,96,130,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39592 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 148 13 19 358 326 454 326), lower := (rows 41 98 148 13 19 32 64 128 256), losses := [] }

theorem u39592 : Upper (D 6) (R 6) [40,96,144,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39593 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 148 13 21 354 322 450 322), lower := (rows 41 98 148 13 21 32 64 128 256), losses := [] }

theorem u39593 : Upper (D 6) (R 6) [40,96,144,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39594 : Route 9 := (fun mask => (mask,id))

def c39594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39594 : Upper (D 6) (R 6) [40,96,144,5,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,6] 13 (by decide) (choices 1) [1,2,64,256] r39594 c39594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26076
  · exact u26077
  · exact u26078
  · exact u26079

def r39595 : Route 9 := (fun mask => (mask,id))

def c39595 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39595 : Upper (D 6) (R 6) [40,96,144,5,65] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,65] 13 (by decide) (choices 1) [2,4,256] r39595 c39595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26080
  · exact u26081
  · exact u26082

def b39596 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 148 13 82 295 327 391 263), lower := (rows 41 98 148 13 82 32 64 128 256), losses := [] }

theorem u39596 : Upper (D 6) (R 6) [40,96,144,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39597 : Route 9 := (fun mask => (mask,id))

def c39597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39597 : Upper (D 6) (R 6) [40,96,144,5,68] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,68] 13 (by decide) (choices 1) [1,2,256] r39597 c39597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26083
  · exact u26084
  · exact u26085

def r39598 : Route 9 := (fun mask => (mask,id))

def c39598 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39598 : Upper (D 6) (R 6) [40,96,144,5,257] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,257] 13 (by decide) (choices 1) [2,4,64] r39598 c39598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26086
  · exact u26087
  · exact u26088

def r39599 : Route 9 := (fun mask => (mask,id))

def c39599 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39599 : Upper (D 6) (R 6) [40,96,144,5,258] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,258] 13 (by decide) (choices 1) [1,2,4,64] r39599 c39599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26089
  · exact u26090
  · exact u26091
  · exact u26092

#print axioms u39599
end Delivery.IrregularNine14.P06
