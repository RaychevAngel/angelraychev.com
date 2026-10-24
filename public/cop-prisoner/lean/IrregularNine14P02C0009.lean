import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0001
import IrregularNine14P02C0002

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r540 : Route 9 := (fun mask => (mask,id))

def c540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u540 : Upper (D 2) (R 2) [22,33,96,192,128] 13 := by
  apply FastRouting.sound _ _ [22,33,96,192,128] 13 (by decide) (choices 1) [8,16,256] r540 c540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u111
  · exact u112
  · exact u113

def r541 : Route 9 := (fun mask => (mask,id))

def c541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u541 : Upper (D 2) (R 2) [22,33,96,192,256] 13 := by
  apply FastRouting.sound _ _ [22,33,96,192,256] 13 (by decide) (choices 1) [8,16,128,256] r541 c541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u114
  · exact u115
  · exact u116
  · exact u117

def b542 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 100 392 24 496 464 464 464), lower := (rows 23 35 100 392 24 32 64 128 256), losses := [] }

theorem u542 : Upper (D 2) (R 2) [22,33,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b542
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 19, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 23 35 100 392 80 440 472 408 408), lower := (rows 23 35 100 392 80 32 64 128 256), losses := [] }

theorem u543 : Upper (D 2) (R 2) [22,33,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b543
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r544 : Route 9 := (fun mask => (mask,id))

def c544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u544 : Upper (D 2) (R 2) [22,33,96,384,128] 13 := by
  apply FastRouting.sound _ _ [22,33,96,384,128] 13 (by decide) (choices 1) [8,16,64,256] r544 c544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u118
  · exact u119
  · exact u120
  · exact u121

def b545 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 196 88 24 416 480 416 416), lower := (rows 23 35 196 88 24 32 64 128 256), losses := [] }

theorem u545 : Upper (D 2) (R 2) [22,33,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b545
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 35 196 88 48 424 456 392 392), lower := (rows 23 35 196 88 48 32 64 128 256), losses := [] }

theorem u546 : Upper (D 2) (R 2) [22,33,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b546
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 35 196 88 144 296 360 424 296), lower := (rows 23 35 196 88 144 32 64 128 256), losses := [] }

theorem u547 : Upper (D 2) (R 2) [22,33,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b547
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r548 : Route 9 := (fun mask => (mask,id))

def c548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u548 : Upper (D 2) (R 2) [22,33,192,80,256] 13 := by
  apply FastRouting.sound _ _ [22,33,192,80,256] 13 (by decide) (choices 1) [8,128,256] r548 c548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u122
  · exact u123
  · exact u124

def b549 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 104 24 432 464 400 400), lower := (rows 23 35 196 104 24 32 64 128 256), losses := [] }

theorem u549 : Upper (D 2) (R 2) [22,33,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b549
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 35 196 104 144 312 344 408 280), lower := (rows 23 35 196 104 144 32 64 128 256), losses := [] }

theorem u550 : Upper (D 2) (R 2) [22,33,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b550
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r551 : Route 9 := (fun mask => (mask,id))

def c551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u551 : Upper (D 2) (R 2) [22,33,192,96,256] 13 := by
  apply FastRouting.sound _ _ [22,33,192,96,256] 13 (by decide) (choices 1) [8,16,128,256] r551 c551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u125
  · exact u126
  · exact u127
  · exact u128

def b552 : PairBound 9 := { available := 480, camps := [{ cop := 8, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 196 280 24 480 480 480 480), lower := (rows 23 35 196 280 24 32 64 128 256), losses := [] }

theorem u552 : Upper (D 2) (R 2) [22,33,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b552
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 35 196 280 48 488 456 456 456), lower := (rows 23 35 196 280 48 32 64 128 256), losses := [] }

theorem u553 : Upper (D 2) (R 2) [22,33,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b553
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 35 196 280 80 424 488 424 424), lower := (rows 23 35 196 280 80 32 64 128 256), losses := [] }

theorem u554 : Upper (D 2) (R 2) [22,33,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b554
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 35 196 280 272 232 232 232 488), lower := (rows 23 35 196 280 272 32 64 128 256), losses := [] }

theorem u555 : Upper (D 2) (R 2) [22,33,192,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b555
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 296 24 496 464 464 464), lower := (rows 23 35 196 296 24 32 64 128 256), losses := [] }

theorem u556 : Upper (D 2) (R 2) [22,33,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b556
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 35 196 296 80 440 472 408 408), lower := (rows 23 35 196 296 80 32 64 128 256), losses := [] }

theorem u557 : Upper (D 2) (R 2) [22,33,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b557
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r558 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u558 : Upper (D 2) (R 2) [22,33,192,288,256] 13 := by
  apply FastRouting.sound _ _ [22,33,192,288,256] 13 (by decide) (choices 1) [8,16,64] r558 c558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u129
  · exact u130
  · exact u131

def b559 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 328 24 432 496 432 432), lower := (rows 23 35 196 328 24 32 64 128 256), losses := [] }

theorem u559 : Upper (D 2) (R 2) [22,33,192,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b559
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 35 196 328 48 440 472 408 408), lower := (rows 23 35 196 328 48 32 64 128 256), losses := [] }

theorem u560 : Upper (D 2) (R 2) [22,33,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b560
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 35 196 328 144 312 376 440 312), lower := (rows 23 35 196 328 144 32 64 128 256), losses := [] }

theorem u561 : Upper (D 2) (R 2) [22,33,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b561
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r562 : Route 9 := (fun mask => (mask,id))

def c562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u562 : Upper (D 2) (R 2) [22,33,192,320,256] 13 := by
  apply FastRouting.sound _ _ [22,33,192,320,256] 13 (by decide) (choices 1) [8,16,128] r562 c562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u132
  · exact u133
  · exact u134

def b563 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 42 100 137 80 432 464 400 400), lower := (rows 23 42 100 137 80 32 64 128 256), losses := [] }

theorem u563 : Upper (D 2) (R 2) [22,40,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b563
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7),(3,5)], upper := (rows 23 42 100 137 144 368 336 464 336), lower := (rows 23 42 100 137 144 32 64 128 256), losses := [] }

theorem u564 : Upper (D 2) (R 2) [22,40,96,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b564
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r565 : Route 9 := (fun mask => (mask,id))

def c565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u565 : Upper (D 2) (R 2) [22,40,96,129,256] 13 := by
  apply FastRouting.sound _ _ [22,40,96,129,256] 13 (by decide) (choices 1) [16,64,128,256] r565 c565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u135
  · exact u136
  · exact u137
  · exact u138

def b566 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 100 200 17 432 464 400 400), lower := (rows 23 42 100 200 17 32 64 128 256), losses := [] }

theorem u566 : Upper (D 2) (R 2) [22,40,96,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b566
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7),(3,5)], upper := (rows 23 42 100 200 144 305 337 401 273), lower := (rows 23 42 100 200 144 32 64 128 256), losses := [] }

theorem u567 : Upper (D 2) (R 2) [22,40,96,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b567
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r568 : Route 9 := (fun mask => (mask,id))

def c568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u568 : Upper (D 2) (R 2) [22,40,96,192,256] 13 := by
  apply FastRouting.sound _ _ [22,40,96,192,256] 13 (by decide) (choices 1) [1,16,128,256] r568 c568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u139
  · exact u140
  · exact u141
  · exact u142

def b569 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 100 392 17 496 464 464 464), lower := (rows 23 42 100 392 17 32 64 128 256), losses := [] }

theorem u569 : Upper (D 2) (R 2) [22,40,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b569
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 42 100 392 80 433 465 401 401), lower := (rows 23 42 100 392 80 32 64 128 256), losses := [] }

theorem u570 : Upper (D 2) (R 2) [22,40,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b570
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7),(3,5)], upper := (rows 23 42 100 392 144 369 337 465 337), lower := (rows 23 42 100 392 144 32 64 128 256), losses := [] }

theorem u571 : Upper (D 2) (R 2) [22,40,96,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b571
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 42 196 73 48 432 464 400 400), lower := (rows 23 42 196 73 48 32 64 128 256), losses := [] }

theorem u572 : Upper (D 2) (R 2) [22,40,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b572
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 42 196 73 144 304 368 432 304), lower := (rows 23 42 196 73 144 32 64 128 256), losses := [] }

theorem u573 : Upper (D 2) (R 2) [22,40,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b573
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r574 : Route 9 := (fun mask => (mask,id))

def c574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u574 : Upper (D 2) (R 2) [22,40,192,65,256] 13 := by
  apply FastRouting.sound _ _ [22,40,192,65,256] 13 (by decide) (choices 1) [16,128,256] r574 c574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u143
  · exact u144
  · exact u145

def b575 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 88 17 416 480 416 416), lower := (rows 23 42 196 88 17 32 64 128 256), losses := [] }

theorem u575 : Upper (D 2) (R 2) [22,40,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b575
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 42 196 88 48 417 449 385 385), lower := (rows 23 42 196 88 48 32 64 128 256), losses := [] }

theorem u576 : Upper (D 2) (R 2) [22,40,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b576
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 42 196 88 144 289 353 417 289), lower := (rows 23 42 196 88 144 32 64 128 256), losses := [] }

theorem u577 : Upper (D 2) (R 2) [22,40,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b577
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r578 : Route 9 := (fun mask => (mask,id))

def c578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u578 : Upper (D 2) (R 2) [22,40,192,80,256] 13 := by
  apply FastRouting.sound _ _ [22,40,192,80,256] 13 (by decide) (choices 1) [1,128,256] r578 c578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u146
  · exact u147
  · exact u148

def b579 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 42 196 265 48 496 464 464 464), lower := (rows 23 42 196 265 48 32 64 128 256), losses := [] }

theorem u579 : Upper (D 2) (R 2) [22,40,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b579
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 42 196 265 80 432 496 432 432), lower := (rows 23 42 196 265 80 32 64 128 256), losses := [] }

theorem u580 : Upper (D 2) (R 2) [22,40,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b580
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 23 42 196 265 272 240 240 240 496), lower := (rows 23 42 196 265 272 32 64 128 256), losses := [{ target := 8, region := (rows 1 10 29 8 16 49 81 145 0), good := (rows 247 46 196 239 244 32 64 128 0) }] }

theorem u581 : Upper (D 2) (R 2) [22,40,192,257,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b581
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 280 17 480 480 480 480), lower := (rows 23 42 196 280 17 32 64 128 256), losses := [] }

theorem u582 : Upper (D 2) (R 2) [22,40,192,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b582
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 42 196 280 48 481 449 449 449), lower := (rows 23 42 196 280 48 32 64 128 256), losses := [] }

theorem u583 : Upper (D 2) (R 2) [22,40,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b583
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 42 196 280 80 417 481 417 417), lower := (rows 23 42 196 280 80 32 64 128 256), losses := [] }

theorem u584 : Upper (D 2) (R 2) [22,40,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b584
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 42 196 280 272 225 225 225 481), lower := (rows 23 42 196 280 272 32 64 128 256), losses := [] }

theorem u585 : Upper (D 2) (R 2) [22,40,192,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b585
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r586 : Route 9 := (fun mask => (mask,id))

def c586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u586 : Upper (D 2) (R 2) [22,40,192,320,1] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,1] 13 (by decide) (choices 1) [16,128,256] r586 c586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u149
  · exact u150
  · exact u151

def b587 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 42 196 328 48 433 465 401 401), lower := (rows 23 42 196 328 48 32 64 128 256), losses := [] }

theorem u587 : Upper (D 2) (R 2) [22,40,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b587
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 42 196 328 144 305 369 433 305), lower := (rows 23 42 196 328 144 32 64 128 256), losses := [] }

theorem u588 : Upper (D 2) (R 2) [22,40,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b588
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r589 : Route 9 := (fun mask => (mask,id))

def c589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u589 : Upper (D 2) (R 2) [22,40,192,320,256] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,256] 13 (by decide) (choices 1) [1,16,128] r589 c589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u152
  · exact u153
  · exact u154

def b590 : PairBound 9 := { available := 392, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 164 88 17 424 456 392 392), lower := (rows 23 98 164 88 17 32 64 128 256), losses := [] }

theorem u590 : Upper (D 2) (R 2) [22,96,160,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b590
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 88 24 417 449 385 385), lower := (rows 23 98 164 88 24 32 64 128 256), losses := [] }

theorem u591 : Upper (D 2) (R 2) [22,96,160,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b591
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 98 164 88 144 297 329 393 265), lower := (rows 23 98 164 88 144 32 64 128 256), losses := [] }

theorem u592 : Upper (D 2) (R 2) [22,96,160,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b592
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r593 : Route 9 := (fun mask => (mask,id))

def c593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u593 : Upper (D 2) (R 2) [22,96,160,80,256] 13 := by
  apply FastRouting.sound _ _ [22,96,160,80,256] 13 (by decide) (choices 1) [1,8,128,256] r593 c593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u155
  · exact u156
  · exact u157
  · exact u158

def b594 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 200 17 312 344 408 280), lower := (rows 23 98 164 200 17 32 64 128 256), losses := [] }

theorem u594 : Upper (D 2) (R 2) [22,96,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b594
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 200 24 305 337 401 273), lower := (rows 23 98 164 200 24 32 64 128 256), losses := [] }

theorem u595 : Upper (D 2) (R 2) [22,96,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b595
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r596 : Route 9 := (fun mask => (mask,id))

def c596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u596 : Upper (D 2) (R 2) [22,96,160,192,256] 13 := by
  apply FastRouting.sound _ _ [22,96,160,192,256] 13 (by decide) (choices 1) [1,8,16,256] r596 c596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u159
  · exact u160
  · exact u161
  · exact u162

def b597 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 265 24 496 464 464 464), lower := (rows 23 98 164 265 24 32 64 128 256), losses := [] }

theorem u597 : Upper (D 2) (R 2) [22,96,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b597
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 23 98 164 265 80 440 472 408 408), lower := (rows 23 98 164 265 80 32 64 128 256), losses := [] }

theorem u598 : Upper (D 2) (R 2) [22,96,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b598
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m599_128 : Upper (D 2) (R 2) [22,96,160,257,256,128] 13 :=
  permutation_upper _ _ _ [22,96,160,257,256,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u165

def r599 : Route 9 := (fun mask => (mask,id))

def c599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u599 : Upper (D 2) (R 2) [22,96,160,257,256] 13 := by
  apply FastRouting.sound _ _ [22,96,160,257,256] 13 (by decide) (choices 1) [8,16,64,128] r599 c599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u163
  · exact u164
  · exact u165
  · exact m599_128

#print axioms u599
end Delivery.IrregularNine14.P02
