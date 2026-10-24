import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0183
import IrregularNine14P06C0184

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29520 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 388 26 56 101 69 197 325), lower := (rows 7 98 388 26 56 32 64 128 256), losses := [] }

theorem u29520 : Upper (D 6) (R 6) [6,96,384,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29520
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29521 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 388 26 112 45 77 141 269), lower := (rows 7 98 388 26 112 32 64 128 256), losses := [] }

theorem u29521 : Upper (D 6) (R 6) [6,96,384,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29521
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29522 : Route 9 := (fun mask => (mask,id))

def c29522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29522 : Upper (D 6) (R 6) [6,96,384,20,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,20,33] 13 (by decide) (choices 1) [1,2,8,64] r29522 c29522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10981
  · exact u10982
  · exact u10983
  · exact u10984

def b29523 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 388 28 50 105 73 201 329), lower := (rows 7 98 388 28 50 32 64 128 256), losses := [] }

theorem u29523 : Upper (D 6) (R 6) [6,96,384,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29523
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29524 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 98 388 28 56 99 67 195 323), lower := (rows 7 98 388 28 56 32 64 128 256), losses := [] }

theorem u29524 : Upper (D 6) (R 6) [6,96,384,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29524
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29525 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 388 28 112 43 75 139 267), lower := (rows 7 98 388 28 112 32 64 128 256), losses := [] }

theorem u29525 : Upper (D 6) (R 6) [6,96,384,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29525
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29526 : Route 9 := (fun mask => (mask,id))

def c29526 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29526 : Upper (D 6) (R 6) [6,96,384,33,65] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,65] 13 (by decide) (choices 1) [2,4,8,16] r29526 c29526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10985
  · exact u10986
  · exact u10987
  · exact u10988

def b29527 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 7 98 388 41 82 61 93 157 285), lower := (rows 7 98 388 41 82 32 64 128 256), losses := [] }

theorem u29527 : Upper (D 6) (R 6) [6,96,384,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29527
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29528 : Route 9 := (fun mask => (mask,id))

def c29528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29528 : Upper (D 6) (R 6) [6,96,384,33,68] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,68] 13 (by decide) (choices 1) [1,2,8,16] r29528 c29528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10989
  · exact u10990
  · exact u10991
  · exact u10992

def r29529 : Route 9 := (fun mask => (mask,id))

def c29529 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29529 : Upper (D 6) (R 6) [6,96,384,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,72] 13 (by decide) (choices 1) [1,2,4,16] r29529 c29529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10993
  · exact u10994
  · exact u10995
  · exact u10996

def b29530 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 388 42 84 57 89 153 281), lower := (rows 7 98 388 42 84 32 64 128 256), losses := [] }

theorem u29530 : Upper (D 6) (R 6) [6,96,384,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29530
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29531 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 388 42 88 53 85 149 277), lower := (rows 7 98 388 42 88 32 64 128 256), losses := [] }

theorem u29531 : Upper (D 6) (R 6) [6,96,384,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29531
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29532 : Route 9 := (fun mask => (mask,id))

def c29532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29532 : Upper (D 6) (R 6) [6,96,384,36,72] 13 := by
  apply FastRouting.sound _ _ [6,96,384,36,72] 13 (by decide) (choices 1) [1,2,16] r29532 c29532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10997
  · exact u10998
  · exact u10999

def b29533 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 388 56 88 39 71 135 263), lower := (rows 7 98 388 56 88 32 64 128 256), losses := [] }

theorem u29533 : Upper (D 6) (R 6) [6,96,384,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29533
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29534 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 14 56 112 112 240 368), lower := (rows 7 131 261 14 56 32 64 128 256), losses := [] }

theorem u29534 : Upper (D 6) (R 6) [6,129,257,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29534
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29535 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 14 112 120 120 248 376), lower := (rows 7 131 261 14 112 32 64 128 256), losses := [] }

theorem u29535 : Upper (D 6) (R 6) [6,129,257,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29535
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29536 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 261 26 28 96 96 224 352), lower := (rows 7 131 261 26 28 32 64 128 256), losses := [] }

theorem u29536 : Upper (D 6) (R 6) [6,129,257,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29536
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29537 : Route 9 := (fun mask => (mask,id))

def c29537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29537 : Upper (D 6) (R 6) [6,129,257,18,36] 13 := by
  apply FastRouting.sound _ _ [6,129,257,18,36] 13 (by decide) (choices 1) [8,64] r29537 c29537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11000
  · exact u11001

def b29538 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 131 261 26 56 100 100 228 356), lower := (rows 7 131 261 26 56 32 64 128 256), losses := [] }

theorem u29538 : Upper (D 6) (R 6) [6,129,257,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29538
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29539 : Route 9 := (fun mask => (mask,id))

def c29539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29539 : Upper (D 6) (R 6) [6,129,257,18,96] 13 := by
  apply FastRouting.sound _ _ [6,129,257,18,96] 13 (by decide) (choices 1) [4,8,64] r29539 c29539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11002
  · exact u11003
  · exact u11004

theorem m29540_16 : Upper (D 6) (R 6) [6,129,257,34,36,16] 13 :=
  permutation_upper _ _ _ [6,129,257,34,36,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11005

def r29540 : Route 9 := (fun mask => (mask,id))

def c29540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29540 : Upper (D 6) (R 6) [6,129,257,34,36] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,36] 13 (by decide) (choices 1) [8,16,64] r29540 c29540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11005
  · exact m29540_16
  · exact u11006

def b29541 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 42 56 116 84 212 340), lower := (rows 7 131 261 42 56 32 64 128 256), losses := [] }

theorem u29541 : Upper (D 6) (R 6) [6,129,257,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29541
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29542 : Route 9 := (fun mask => (mask,id))

def c29542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29542 : Upper (D 6) (R 6) [6,129,257,34,68] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,68] 13 (by decide) (choices 1) [8,16,64] r29542 c29542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11007
  · exact u11008
  · exact u11009

def r29543 : Route 9 := (fun mask => (mask,id))

def c29543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29543 : Upper (D 6) (R 6) [6,129,257,34,72] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,72] 13 (by decide) (choices 1) [4,16,64] r29543 c29543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11010
  · exact u11011
  · exact u11012

def r29544 : Route 9 := (fun mask => (mask,id))

def c29544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29544 : Upper (D 6) (R 6) [6,129,257,34,96] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,96] 13 (by decide) (choices 1) [4,8,16,64] r29544 c29544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11013
  · exact u11014
  · exact u11015
  · exact u11016

def b29545 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 261 56 56 102 70 198 326), lower := (rows 7 131 261 56 56 32 64 128 256), losses := [] }

theorem u29545 : Upper (D 6) (R 6) [6,129,257,48,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29545
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m29546_4 : Upper (D 6) (R 6) [6,129,257,48,72,4] 13 :=
  permutation_upper _ _ _ [6,129,257,48,72,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11017

def r29546 : Route 9 := (fun mask => (mask,id))

def c29546 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29546 : Upper (D 6) (R 6) [6,129,257,48,72] 13 := by
  apply FastRouting.sound _ _ [6,129,257,48,72] 13 (by decide) (choices 1) [2,4,64] r29546 c29546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11017
  · exact m29546_4
  · exact u11018

def b29547 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 261 56 112 110 78 206 334), lower := (rows 7 131 261 56 112 32 64 128 256), losses := [] }

theorem u29547 : Upper (D 6) (R 6) [6,129,257,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29547
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29548 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 104 112 62 94 158 286), lower := (rows 7 131 261 104 112 32 64 128 256), losses := [] }

theorem u29548 : Upper (D 6) (R 6) [6,129,257,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29548
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29549 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 268 25 22 96 96 224 352), lower := (rows 7 131 268 25 22 32 64 128 256), losses := [] }

theorem u29549 : Upper (D 6) (R 6) [6,129,264,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29549
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29550 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 0, region := 112, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 25 50 100 100 228 356), lower := (rows 7 131 268 25 50 32 64 128 256), losses := [] }

theorem u29550 : Upper (D 6) (R 6) [6,129,264,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29550
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29551 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 112, targets := 1 },{ cop := 0, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 131 268 25 52 98 98 226 354), lower := (rows 7 131 268 25 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 35 67 131 259), good := (rows 502 498 284 508 52 32 64 128 256) }] }

theorem u29551 : Upper (D 6) (R 6) [6,129,264,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29551
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29552 : Route 9 := (fun mask => (mask,id))

def c29552 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29552 : Upper (D 6) (R 6) [6,129,264,17,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,17,96] 13 (by decide) (choices 1) [2,4,64] r29552 c29552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11019
  · exact u11020
  · exact u11021

def b29553 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 268 26 21 96 96 224 352), lower := (rows 7 131 268 26 21 32 64 128 256), losses := [] }

theorem u29553 : Upper (D 6) (R 6) [6,129,264,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29553
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29554 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 131 268 26 49 100 100 228 356), lower := (rows 7 131 268 26 49 32 64 128 256), losses := [] }

theorem u29554 : Upper (D 6) (R 6) [6,129,264,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29554
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29555 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 226, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 131 268 26 52 97 97 225 353), lower := (rows 7 131 268 26 52 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 35 67 131 259), good := (rows 501 497 284 508 52 32 64 128 256) }] }

theorem u29555 : Upper (D 6) (R 6) [6,129,264,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29555
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29556 : Route 9 := (fun mask => (mask,id))

def c29556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29556 : Upper (D 6) (R 6) [6,129,264,18,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,18,96] 13 (by decide) (choices 1) [1,4,64] r29556 c29556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11022
  · exact u11023
  · exact u11024

def b29557 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 268 28 19 96 96 224 352), lower := (rows 7 131 268 28 19 32 64 128 256), losses := [] }

theorem u29557 : Upper (D 6) (R 6) [6,129,264,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29557
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29558 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 242, targets := 4 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 131 268 28 49 98 98 226 354), lower := (rows 7 131 268 28 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 268 28 508 32 64 128 256) }] }

theorem u29558 : Upper (D 6) (R 6) [6,129,264,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29558
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29559 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 242, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 131 268 28 50 97 97 225 353), lower := (rows 7 131 268 28 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 268 28 508 32 64 128 256) }] }

theorem u29559 : Upper (D 6) (R 6) [6,129,264,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29559
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29560 : Route 9 := (fun mask => (mask,id))

def c29560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29560 : Upper (D 6) (R 6) [6,129,264,20,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,20,96] 13 (by decide) (choices 1) [1,2,64] r29560 c29560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11025
  · exact u11026
  · exact u11027

def b29561 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 131 268 41 22 112 112 240 368), lower := (rows 7 131 268 41 22 32 64 128 256), losses := [] }

theorem u29561 : Upper (D 6) (R 6) [6,129,264,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29561
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29562 : Route 9 := (fun mask => (mask,id))

def c29562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29562 : Upper (D 6) (R 6) [6,129,264,33,34] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,34] 13 (by decide) (choices 1) [4,16,64] r29562 c29562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11028
  · exact u11029
  · exact u11030

def b29563 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 1 }], pairs := [(0,5),(1,5),(4,0)], upper := (rows 7 131 268 41 52 114 82 210 338), lower := (rows 7 131 268 41 52 32 64 128 256), losses := [] }

theorem u29563 : Upper (D 6) (R 6) [6,129,264,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29563
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29564 : Route 9 := (fun mask => (mask,id))

def c29564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29564 : Upper (D 6) (R 6) [6,129,264,33,66] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,66] 13 (by decide) (choices 1) [4,16,64] r29564 c29564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11031
  · exact u11032
  · exact u11033

def r29565 : Route 9 := (fun mask => (mask,id))

def c29565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29565 : Upper (D 6) (R 6) [6,129,264,33,68] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,68] 13 (by decide) (choices 1) [2,16,64] r29565 c29565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11034
  · exact u11035
  · exact u11036

def r29566 : Route 9 := (fun mask => (mask,id))

def c29566 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29566 : Upper (D 6) (R 6) [6,129,264,33,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,96] 13 (by decide) (choices 1) [2,4,16,64] r29566 c29566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11037
  · exact u11038
  · exact u11039
  · exact u11040

def b29567 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 131 268 42 21 112 112 240 368), lower := (rows 7 131 268 42 21 32 64 128 256), losses := [] }

theorem u29567 : Upper (D 6) (R 6) [6,129,264,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29567
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29568 : Route 9 := (fun mask => (mask,id))

def c29568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29568 : Upper (D 6) (R 6) [6,129,264,34,33] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,33] 13 (by decide) (choices 1) [4,16,64] r29568 c29568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11041
  · exact u11042
  · exact u11043

def b29569 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 2 }], pairs := [(0,5),(1,5),(4,1)], upper := (rows 7 131 268 42 52 113 81 209 337), lower := (rows 7 131 268 42 52 32 64 128 256), losses := [] }

theorem u29569 : Upper (D 6) (R 6) [6,129,264,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29569
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29570 : Route 9 := (fun mask => (mask,id))

def c29570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29570 : Upper (D 6) (R 6) [6,129,264,34,65] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,65] 13 (by decide) (choices 1) [4,16,64] r29570 c29570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11044
  · exact u11045
  · exact u11046

def r29571 : Route 9 := (fun mask => (mask,id))

def c29571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29571 : Upper (D 6) (R 6) [6,129,264,34,68] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,68] 13 (by decide) (choices 1) [1,16,64] r29571 c29571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11047
  · exact u11048
  · exact u11049

def r29572 : Route 9 := (fun mask => (mask,id))

def c29572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29572 : Upper (D 6) (R 6) [6,129,264,34,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,96] 13 (by decide) (choices 1) [1,4,16,64] r29572 c29572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11050
  · exact u11051
  · exact u11052
  · exact u11053

def b29573 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 44 19 112 112 240 368), lower := (rows 7 131 268 44 19 32 64 128 256), losses := [] }

theorem u29573 : Upper (D 6) (R 6) [6,129,264,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29573
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29574 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 242, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 131 268 44 49 114 82 210 338), lower := (rows 7 131 268 44 49 32 64 128 256), losses := [] }

theorem u29574 : Upper (D 6) (R 6) [6,129,264,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29574
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29575 : Route 9 := (fun mask => (mask,id))

def c29575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29575 : Upper (D 6) (R 6) [6,129,264,36,34] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,34] 13 (by decide) (choices 1) [1,16,64] r29575 c29575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11054
  · exact u11055
  · exact u11056

def r29576 : Route 9 := (fun mask => (mask,id))

def c29576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29576 : Upper (D 6) (R 6) [6,129,264,36,65] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,65] 13 (by decide) (choices 1) [2,16,64] r29576 c29576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11057
  · exact u11058
  · exact u11059

def r29577 : Route 9 := (fun mask => (mask,id))

def c29577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29577 : Upper (D 6) (R 6) [6,129,264,36,66] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,66] 13 (by decide) (choices 1) [1,16,64] r29577 c29577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11060
  · exact u11061
  · exact u11062

def r29578 : Route 9 := (fun mask => (mask,id))

def c29578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29578 : Upper (D 6) (R 6) [6,129,264,36,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,96] 13 (by decide) (choices 1) [1,2,16,64] r29578 c29578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11063
  · exact u11064
  · exact u11065
  · exact u11066

def b29579 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 56 19 100 100 228 356), lower := (rows 7 131 268 56 19 32 64 128 256), losses := [] }

theorem u29579 : Upper (D 6) (R 6) [6,129,264,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29579
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29579
end Delivery.IrregularNine14.P06
