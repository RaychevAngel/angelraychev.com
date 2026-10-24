import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0659
import IrregularNine14P06C0660
import IrregularNine14P06C0661
import IrregularNine14P06C0662
import IrregularNine14P06C0663

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43380 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 9, targets := 2 },{ cop := 1, region := 9, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 98 134 73 279 311 343 407 279), lower := (rows 41 98 134 73 16 32 64 128 256), losses := [] }

theorem u43380 : Upper (D 6) (R 6) [40,96,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43381 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 41 98 134 74 277 309 341 405 277), lower := (rows 41 98 134 74 16 32 64 128 256), losses := [] }

theorem u43381 : Upper (D 6) (R 6) [40,96,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43382 : Route 9 := (fun mask => (mask,id))

def c43382 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43382 : Upper (D 6) (R 6) [40,96,130,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43382 c43382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39556
  · exact u39557
  · exact u39558
  · exact u39559
  · exact u39560
  · exact u39561

def r43383 : Route 9 := (fun mask => (mask,id))

def c43383 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43383 : Upper (D 6) (R 6) [40,96,130,80] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43383 c43383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39562
  · exact u39563
  · exact u39564
  · exact u39565
  · exact u39566
  · exact u39567

def r43384 : Route 9 := (fun mask => (mask,id))

def c43384 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43384 : Upper (D 6) (R 6) [40,96,130,257] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43384 c43384
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39568
  · exact u39569
  · exact u39570
  · exact u39571
  · exact u39572
  · exact u39573

def r43385 : Route 9 := (fun mask => (mask,id))

def c43385 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43385 : Upper (D 6) (R 6) [40,96,130,258] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258] 13 (by decide) (choices 2) [5,65,68] r43385 c43385
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39574
  · exact u39575
  · exact u39576

def r43386 : Route 9 := (fun mask => (mask,id))

def c43386 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43386 : Upper (D 6) (R 6) [40,96,130,260] 13 := by
  apply FastRouting.sound _ _ [40,96,130,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43386 c43386
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39577
  · exact u39578
  · exact u39579
  · exact u39580
  · exact u39581
  · exact u39582

def r43387 : Route 9 := (fun mask => (mask,id))

def c43387 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43387 : Upper (D 6) (R 6) [40,96,130,272] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43387 c43387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39583
  · exact u39584
  · exact u39585
  · exact u39586
  · exact u39587
  · exact u39588

def r43388 : Route 9 := (fun mask => (mask,id))

def c43388 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43388 : Upper (D 6) (R 6) [40,96,130,320] 13 := by
  apply FastRouting.sound _ _ [40,96,130,320] 13 (by decide) (choices 2) [3,5,6] r43388 c43388
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39589
  · exact u39590
  · exact u39591

def b43389 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 148 11 343 359 327 455 327), lower := (rows 41 98 148 11 16 32 64 128 256), losses := [] }

theorem u43389 : Upper (D 6) (R 6) [40,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43390 : Route 9 := (fun mask => (mask,id))

def c43390 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43390 : Upper (D 6) (R 6) [40,96,144,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43390 c43390
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39592
  · exact u39593
  · exact u39594
  · exact u39595
  · exact u39596
  · exact u39597
  · exact u39598
  · exact u39599
  · exact u39600
  · exact u39601

def r43391 : Route 9 := (fun mask => (mask,id))

def c43391 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43391 : Upper (D 6) (R 6) [40,96,144,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43391 c43391
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39602
  · exact u39603
  · exact u39604
  · exact u39605
  · exact u39606
  · exact u39607
  · exact u39608
  · exact u39609
  · exact u39610
  · exact u39611

def b43392 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 9, targets := 2 },{ cop := 1, region := 9, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 98 148 73 279 295 327 391 263), lower := (rows 41 98 148 73 16 32 64 128 256), losses := [] }

theorem u43392 : Upper (D 6) (R 6) [40,96,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43393 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 41 98 148 74 279 295 327 391 263), lower := (rows 41 98 148 74 16 32 64 128 256), losses := [] }

theorem u43393 : Upper (D 6) (R 6) [40,96,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43394 : Route 9 := (fun mask => (mask,id))

def c43394 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43394 : Upper (D 6) (R 6) [40,96,144,68] 13 := by
  apply FastRouting.sound _ _ [40,96,144,68] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43394 c43394
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39612
  · exact u39613
  · exact u39614
  · exact u39615
  · exact u39616
  · exact u39617

def r43395 : Route 9 := (fun mask => (mask,id))

def c43395 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43395 : Upper (D 6) (R 6) [40,96,144,257] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43395 c43395
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39618
  · exact u39619
  · exact u39620
  · exact u39621
  · exact u39622
  · exact u39623

def r43396 : Route 9 := (fun mask => (mask,id))

def c43396 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43396 : Upper (D 6) (R 6) [40,96,144,258] 13 := by
  apply FastRouting.sound _ _ [40,96,144,258] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43396 c43396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39624
  · exact u39625
  · exact u39626
  · exact u39627
  · exact u39628
  · exact u39629

def r43397 : Route 9 := (fun mask => (mask,id))

def c43397 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43397 : Upper (D 6) (R 6) [40,96,144,260] 13 := by
  apply FastRouting.sound _ _ [40,96,144,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43397 c43397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39630
  · exact u39631
  · exact u39632
  · exact u39633
  · exact u39634
  · exact u39635

def r43398 : Route 9 := (fun mask => (mask,id))

def c43398 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43398 : Upper (D 6) (R 6) [40,96,144,320] 13 := by
  apply FastRouting.sound _ _ [40,96,144,320] 13 (by decide) (choices 2) [3,5,6] r43398 c43398
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39636
  · exact u39637
  · exact u39638

def b43399 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 196 11 279 311 343 407 279), lower := (rows 41 98 196 11 16 32 64 128 256), losses := [] }

theorem u43399 : Upper (D 6) (R 6) [40,96,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43400 : Route 9 := (fun mask => (mask,id))

def c43400 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43400 : Upper (D 6) (R 6) [40,96,192,5] 13 := by
  apply FastRouting.sound _ _ [40,96,192,5] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43400 c43400
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39639
  · exact u39640
  · exact u39641
  · exact u39642
  · exact u39643
  · exact u39644

def r43401 : Route 9 := (fun mask => (mask,id))

def c43401 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43401 : Upper (D 6) (R 6) [40,96,192,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,6] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43401 c43401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39645
  · exact u39646
  · exact u39647
  · exact u39648
  · exact u39649
  · exact u39650

def r43402 : Route 9 := (fun mask => (mask,id))

def c43402 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43402 : Upper (D 6) (R 6) [40,96,192,17] 13 := by
  apply FastRouting.sound _ _ [40,96,192,17] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43402 c43402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39651
  · exact u39652
  · exact u39653
  · exact u39654
  · exact u39655
  · exact u39656

def r43403 : Route 9 := (fun mask => (mask,id))

def c43403 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43403 : Upper (D 6) (R 6) [40,96,192,18] 13 := by
  apply FastRouting.sound _ _ [40,96,192,18] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43403 c43403
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39657
  · exact u39658
  · exact u39659
  · exact u39660
  · exact u39661
  · exact u39662

def r43404 : Route 9 := (fun mask => (mask,id))

def c43404 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43404 : Upper (D 6) (R 6) [40,96,192,20] 13 := by
  apply FastRouting.sound _ _ [40,96,192,20] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43404 c43404
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39663
  · exact u39664
  · exact u39665
  · exact u39666
  · exact u39667
  · exact u39668

def r43405 : Route 9 := (fun mask => (mask,id))

def c43405 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43405 : Upper (D 6) (R 6) [40,96,192,257] 13 := by
  apply FastRouting.sound _ _ [40,96,192,257] 13 (by decide) (choices 2) [3,5,6] r43405 c43405
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39669
  · exact u39670
  · exact u39671

def r43406 : Route 9 := (fun mask => (mask,id))

def c43406 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43406 : Upper (D 6) (R 6) [40,96,192,258] 13 := by
  apply FastRouting.sound _ _ [40,96,192,258] 13 (by decide) (choices 2) [3,5,6] r43406 c43406
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39672
  · exact u39673
  · exact u39674

def r43407 : Route 9 := (fun mask => (mask,id))

def c43407 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43407 : Upper (D 6) (R 6) [40,96,192,260] 13 := by
  apply FastRouting.sound _ _ [40,96,192,260] 13 (by decide) (choices 2) [3,5,6] r43407 c43407
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39675
  · exact u39676
  · exact u39677

def r43408 : Route 9 := (fun mask => (mask,id))

def c43408 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43408 : Upper (D 6) (R 6) [40,96,192,272] 13 := by
  apply FastRouting.sound _ _ [40,96,192,272] 13 (by decide) (choices 2) [3,5,6] r43408 c43408
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39678
  · exact u39679
  · exact u39680

def b43409 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 388 11 87 119 87 215 343), lower := (rows 41 98 388 11 16 32 64 128 256), losses := [] }

theorem u43409 : Upper (D 6) (R 6) [40,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43410 : Route 9 := (fun mask => (mask,id))

def c43410 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43410 : Upper (D 6) (R 6) [40,96,384,5] 13 := by
  apply FastRouting.sound _ _ [40,96,384,5] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43410 c43410
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39681
  · exact u39682
  · exact u39683
  · exact u39684
  · exact u39685
  · exact u39686

def r43411 : Route 9 := (fun mask => (mask,id))

def c43411 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43411 : Upper (D 6) (R 6) [40,96,384,6] 13 := by
  apply FastRouting.sound _ _ [40,96,384,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43411 c43411
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39687
  · exact u39688
  · exact u39689
  · exact u39690
  · exact u39691
  · exact u39692

def r43412 : Route 9 := (fun mask => (mask,id))

def c43412 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43412 : Upper (D 6) (R 6) [40,96,384,17] 13 := by
  apply FastRouting.sound _ _ [40,96,384,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43412 c43412
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39693
  · exact u39694
  · exact u39695
  · exact u39696
  · exact u39697
  · exact u39698

def r43413 : Route 9 := (fun mask => (mask,id))

def c43413 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43413 : Upper (D 6) (R 6) [40,96,384,18] 13 := by
  apply FastRouting.sound _ _ [40,96,384,18] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43413 c43413
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39699
  · exact u39700
  · exact u39701
  · exact u39702
  · exact u39703
  · exact u39704

def r43414 : Route 9 := (fun mask => (mask,id))

def c43414 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43414 : Upper (D 6) (R 6) [40,96,384,20] 13 := by
  apply FastRouting.sound _ _ [40,96,384,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43414 c43414
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39705
  · exact u39706
  · exact u39707
  · exact u39708
  · exact u39709
  · exact u39710

def b43415 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 9, targets := 2 },{ cop := 1, region := 9, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 98 388 73 23 55 87 151 279), lower := (rows 41 98 388 73 16 32 64 128 256), losses := [] }

theorem u43415 : Upper (D 6) (R 6) [40,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43416 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 41 98 388 74 23 55 87 151 279), lower := (rows 41 98 388 74 16 32 64 128 256), losses := [] }

theorem u43416 : Upper (D 6) (R 6) [40,96,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43417 : Route 9 := (fun mask => (mask,id))

def c43417 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43417 : Upper (D 6) (R 6) [40,96,384,68] 13 := by
  apply FastRouting.sound _ _ [40,96,384,68] 13 (by decide) (choices 2) [3,5,6] r43417 c43417
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39711
  · exact u39712
  · exact u39713

def r43418 : Route 9 := (fun mask => (mask,id))

def c43418 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43418 : Upper (D 6) (R 6) [40,96,384,80] 13 := by
  apply FastRouting.sound _ _ [40,96,384,80] 13 (by decide) (choices 2) [3,5,6] r43418 c43418
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39714
  · exact u39715
  · exact u39716

theorem m43419_36 : Upper (D 6) (R 6) [40,129,257,6,36] 13 :=
  permutation_upper _ _ _ [40,129,257,6,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39718

theorem m43419_68 : Upper (D 6) (R 6) [40,129,257,6,68] 13 :=
  permutation_upper _ _ _ [40,129,257,6,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39719

def r43419 : Route 9 := (fun mask => (mask,id))

def c43419 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43419 : Upper (D 6) (R 6) [40,129,257,6] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43419 c43419
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39717
  · exact u39718
  · exact m43419_36
  · exact u39719
  · exact m43419_68
  · exact u39720

def r43420 : Route 9 := (fun mask => (mask,id))

def c43420 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43420 : Upper (D 6) (R 6) [40,129,257,18] 13 := by
  apply FastRouting.sound _ _ [40,129,257,18] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43420 c43420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39721
  · exact u39722
  · exact u39723
  · exact u39724
  · exact u39725
  · exact u39726

def b43421 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 261 42 86 118 86 214 342), lower := (rows 41 131 261 42 16 32 64 128 256), losses := [] }

theorem u43421 : Upper (D 6) (R 6) [40,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43422 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 261 56 86 102 70 198 326), lower := (rows 41 131 261 56 16 32 64 128 256), losses := [] }

theorem u43422 : Upper (D 6) (R 6) [40,129,257,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43423 : Route 9 := (fun mask => (mask,id))

def c43423 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43423 : Upper (D 6) (R 6) [40,129,257,66] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43423 c43423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39727
  · exact u39728
  · exact u39729
  · exact u39730
  · exact u39731
  · exact u39732

theorem m43424_36 : Upper (D 6) (R 6) [40,129,257,80,36] 13 :=
  permutation_upper _ _ _ [40,129,257,80,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39734

theorem m43424_68 : Upper (D 6) (R 6) [40,129,257,80,68] 13 :=
  permutation_upper _ _ _ [40,129,257,80,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39735

def r43424 : Route 9 := (fun mask => (mask,id))

def c43424 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43424 : Upper (D 6) (R 6) [40,129,257,80] 13 := by
  apply FastRouting.sound _ _ [40,129,257,80] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43424 c43424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39733
  · exact u39734
  · exact m43424_36
  · exact u39735
  · exact m43424_68
  · exact u39736

def b43425 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 261 104 86 118 86 214 342), lower := (rows 41 131 261 104 16 32 64 128 256), losses := [] }

theorem u43425 : Upper (D 6) (R 6) [40,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43426 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 262 11 116 116 116 244 372), lower := (rows 41 131 262 11 16 32 64 128 256), losses := [] }

theorem u43426 : Upper (D 6) (R 6) [40,129,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43427 : Route 9 := (fun mask => (mask,id))

def c43427 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43427 : Upper (D 6) (R 6) [40,129,258,5] 13 := by
  apply FastRouting.sound _ _ [40,129,258,5] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43427 c43427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39737
  · exact u39738
  · exact u39739
  · exact u39740
  · exact u39741
  · exact u39742

def b43428 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 131 262 14 117 117 117 245 373), lower := (rows 41 131 262 14 16 32 64 128 256), losses := [] }

theorem u43428 : Upper (D 6) (R 6) [40,129,258,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43429 : Route 9 := (fun mask => (mask,id))

def c43429 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43429 : Upper (D 6) (R 6) [40,129,258,17] 13 := by
  apply FastRouting.sound _ _ [40,129,258,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43429 c43429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39743
  · exact u39744
  · exact u39745
  · exact u39746
  · exact u39747
  · exact u39748

def r43430 : Route 9 := (fun mask => (mask,id))

def c43430 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43430 : Upper (D 6) (R 6) [40,129,258,18] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43430 c43430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39749
  · exact u39750
  · exact u39751
  · exact u39752
  · exact u39753
  · exact u39754

def r43431 : Route 9 := (fun mask => (mask,id))

def c43431 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43431 : Upper (D 6) (R 6) [40,129,258,20] 13 := by
  apply FastRouting.sound _ _ [40,129,258,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43431 c43431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39755
  · exact u39756
  · exact u39757
  · exact u39758
  · exact u39759
  · exact u39760
  · exact u39761
  · exact u39762
  · exact u39763
  · exact u39764

def b43432 : PairBound 9 := { available := 86, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 41 86 118 86 214 342), lower := (rows 41 131 262 41 16 32 64 128 256), losses := [] }

theorem u43432 : Upper (D 6) (R 6) [40,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43433 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 262 42 85 117 85 213 341), lower := (rows 41 131 262 42 16 32 64 128 256), losses := [] }

theorem u43433 : Upper (D 6) (R 6) [40,129,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43434 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 262 44 87 119 87 215 343), lower := (rows 41 131 262 44 16 32 64 128 256), losses := [] }

theorem u43434 : Upper (D 6) (R 6) [40,129,258,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43435 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 262 56 87 103 71 199 327), lower := (rows 41 131 262 56 16 32 64 128 256), losses := [] }

theorem u43435 : Upper (D 6) (R 6) [40,129,258,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43436 : Route 9 := (fun mask => (mask,id))

def c43436 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43436 : Upper (D 6) (R 6) [40,129,258,65] 13 := by
  apply FastRouting.sound _ _ [40,129,258,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43436 c43436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39765
  · exact u39766
  · exact u39767
  · exact u39768
  · exact u39769
  · exact u39770

def r43437 : Route 9 := (fun mask => (mask,id))

def c43437 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43437 : Upper (D 6) (R 6) [40,129,258,66] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43437 c43437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39771
  · exact u39772
  · exact u39773
  · exact u39774
  · exact u39775
  · exact u39776

def r43438 : Route 9 := (fun mask => (mask,id))

def c43438 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43438 : Upper (D 6) (R 6) [40,129,258,68] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43438 c43438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39777
  · exact u39778
  · exact u39779
  · exact u39780
  · exact u39781
  · exact u39782
  · exact u39783
  · exact u39784
  · exact u39785
  · exact u39786

def r43439 : Route 9 := (fun mask => (mask,id))

def c43439 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43439 : Upper (D 6) (R 6) [40,129,258,80] 13 := by
  apply FastRouting.sound _ _ [40,129,258,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43439 c43439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39787
  · exact u39788
  · exact u39789
  · exact u39790
  · exact u39791
  · exact u39792
  · exact u39793
  · exact u39794
  · exact u39795
  · exact u39796

#print axioms u43439
end Delivery.IrregularNine14.P06
