import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0002
import IrregularNine14P02C0003

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b600 : PairBound 9 := { available := 456, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 164 280 17 488 456 456 456), lower := (rows 23 98 164 280 17 32 64 128 256), losses := [] }

theorem u600 : Upper (D 2) (R 2) [22,96,160,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b600
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 449, camps := [{ cop := 8, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 280 24 481 449 449 449), lower := (rows 23 98 164 280 24 32 64 128 256), losses := [] }

theorem u601 : Upper (D 2) (R 2) [22,96,160,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b601
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 23 98 164 280 80 425 457 393 393), lower := (rows 23 98 164 280 80 32 64 128 256), losses := [] }

theorem u602 : Upper (D 2) (R 2) [22,96,160,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b602
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 98 164 280 272 233 201 201 457), lower := (rows 23 98 164 280 272 32 64 128 256), losses := [] }

theorem u603 : Upper (D 2) (R 2) [22,96,160,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b603
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 328 17 440 472 408 408), lower := (rows 23 98 164 328 17 32 64 128 256), losses := [] }

theorem u604 : Upper (D 2) (R 2) [22,96,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b604
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 328 24 433 465 401 401), lower := (rows 23 98 164 328 24 32 64 128 256), losses := [] }

theorem u605 : Upper (D 2) (R 2) [22,96,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b605
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 98 164 328 144 313 345 409 281), lower := (rows 23 98 164 328 144 32 64 128 256), losses := [] }

theorem u606 : Upper (D 2) (R 2) [22,96,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b606
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r607 : Route 9 := (fun mask => (mask,id))

def c607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u607 : Upper (D 2) (R 2) [22,96,160,320,256] 13 := by
  apply FastRouting.sound _ _ [22,96,160,320,256] 13 (by decide) (choices 1) [1,8,16,128] r607 c607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u166
  · exact u167
  · exact u168
  · exact u169

def b608 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 388 41 24 496 464 464 464), lower := (rows 23 98 388 41 24 32 64 128 256), losses := [] }

theorem u608 : Upper (D 2) (R 2) [22,96,384,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b608
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 23 98 388 41 80 440 472 408 408), lower := (rows 23 98 388 41 80 32 64 128 256), losses := [] }

theorem u609 : Upper (D 2) (R 2) [22,96,384,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b609
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 98 388 41 144 376 344 472 344), lower := (rows 23 98 388 41 144 32 64 128 256), losses := [] }

theorem u610 : Upper (D 2) (R 2) [22,96,384,33,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b610
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 456, camps := [{ cop := 3, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 388 56 17 488 456 456 456), lower := (rows 23 98 388 56 17 32 64 128 256), losses := [] }

theorem u611 : Upper (D 2) (R 2) [22,96,384,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b611
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 23 98 388 56 24 481 449 449 449), lower := (rows 23 98 388 56 24 32 64 128 256), losses := [] }

theorem u612 : Upper (D 2) (R 2) [22,96,384,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b612
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 23 98 388 56 80 425 457 393 393), lower := (rows 23 98 388 56 80 32 64 128 256), losses := [] }

theorem u613 : Upper (D 2) (R 2) [22,96,384,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b613
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 23 98 388 56 144 361 329 457 329), lower := (rows 23 98 388 56 144 32 64 128 256), losses := [] }

theorem u614 : Upper (D 2) (R 2) [22,96,384,48,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b614
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r615 : Route 9 := (fun mask => (mask,id))

def c615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u615 : Upper (D 2) (R 2) [22,96,384,160,1] 13 := by
  apply FastRouting.sound _ _ [22,96,384,160,1] 13 (by decide) (choices 1) [8,16,64,256] r615 c615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u170
  · exact u171
  · exact u172
  · exact u173

def b616 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 388 168 24 369 337 465 337), lower := (rows 23 98 388 168 24 32 64 128 256), losses := [] }

theorem u616 : Upper (D 2) (R 2) [22,96,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b616
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 23 98 388 168 80 313 345 409 281), lower := (rows 23 98 388 168 80 32 64 128 256), losses := [] }

theorem u617 : Upper (D 2) (R 2) [22,96,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b617
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 28 200 48 480 448 448 448), lower := (rows 51 7 28 200 48 32 64 128 256), losses := [] }

theorem u618 : Upper (D 2) (R 2) [50,5,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b618
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 20, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 51 7 28 200 80 416 480 416 416), lower := (rows 51 7 28 200 80 32 64 128 256), losses := [] }

theorem u619 : Upper (D 2) (R 2) [50,5,24,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b619
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r620 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u620 : Upper (D 2) (R 2) [50,5,24,192,256] 13 := by
  apply FastRouting.sound _ _ [50,5,24,192,256] 13 (by decide) (choices 1) [64,256] r620 c620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u174
  · exact u175

def b621 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 76 152 48 480 448 448 448), lower := (rows 51 7 76 152 48 32 64 128 256), losses := [] }

theorem u621 : Upper (D 2) (R 2) [50,5,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b621
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 392, targets := 64 },{ cop := 3, region := 356, targets := 16 }], pairs := [(2,4),(3,6)], upper := (rows 51 7 76 152 80 416 480 416 416), lower := (rows 51 7 76 152 80 32 64 128 256), losses := [] }

theorem u622 : Upper (D 2) (R 2) [50,5,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b622
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 7 76 152 144 352 352 480 352), lower := (rows 51 7 76 152 144 32 64 128 256), losses := [] }

theorem u623 : Upper (D 2) (R 2) [50,5,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b623
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r624 : Route 9 := (fun mask => (mask,id))

def c624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u624 : Upper (D 2) (R 2) [50,5,72,144,256] 13 := by
  apply FastRouting.sound _ _ [50,5,72,144,256] 13 (by decide) (choices 1) [64,128,256] r624 c624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u176
  · exact u177
  · exact u178

def b625 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 76 392 48 496 464 464 464), lower := (rows 51 7 76 392 48 32 64 128 256), losses := [] }

theorem u625 : Upper (D 2) (R 2) [50,5,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b625
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m626_16 : Upper (D 2) (R 2) [50,5,72,384,64,16] 13 :=
  permutation_upper _ _ _ [50,5,72,384,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u179

def r626 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u626 : Upper (D 2) (R 2) [50,5,72,384,64] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384,64] 13 (by decide) (choices 1) [16,128] r626 c626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m626_16
  · exact u181

theorem m627_16 : Upper (D 2) (R 2) [50,5,72,384,128,16] 13 :=
  permutation_upper _ _ _ [50,5,72,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u180

theorem m627_64 : Upper (D 2) (R 2) [50,5,72,384,128,64] 13 :=
  permutation_upper _ _ _ [50,5,72,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u181

def r627 : Route 9 := (fun mask => (mask,id))

def c627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u627 : Upper (D 2) (R 2) [50,5,72,384,128] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384,128] 13 (by decide) (choices 1) [16,64,256] r627 c627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m627_16
  · exact m627_64
  · exact u182

def b628 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 7 84 200 24 416 480 416 416), lower := (rows 51 7 84 200 24 32 64 128 256), losses := [] }

theorem u628 : Upper (D 2) (R 2) [50,5,80,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b628
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 84 200 48 424 456 392 392), lower := (rows 51 7 84 200 48 32 64 128 256), losses := [] }

theorem u629 : Upper (D 2) (R 2) [50,5,80,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b629
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 20, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 51 7 84 200 144 296 360 424 296), lower := (rows 51 7 84 200 144 32 64 128 256), losses := [] }

theorem u630 : Upper (D 2) (R 2) [50,5,80,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b630
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r631 : Route 9 := (fun mask => (mask,id))

def c631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u631 : Upper (D 2) (R 2) [50,5,80,192,256] 13 := by
  apply FastRouting.sound _ _ [50,5,80,192,256] 13 (by decide) (choices 1) [8,128,256] r631 c631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u183
  · exact u184
  · exact u185

def b632 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 7 84 392 24 480 480 480 480), lower := (rows 51 7 84 392 24 32 64 128 256), losses := [] }

theorem u632 : Upper (D 2) (R 2) [50,5,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b632
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 84 392 48 488 456 456 456), lower := (rows 51 7 84 392 48 32 64 128 256), losses := [] }

theorem u633 : Upper (D 2) (R 2) [50,5,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b633
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 51 7 84 392 80 424 488 424 424), lower := (rows 51 7 84 392 80 32 64 128 256), losses := [] }

theorem u634 : Upper (D 2) (R 2) [50,5,80,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b634
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r635 : Route 9 := (fun mask => (mask,id))

def c635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u635 : Upper (D 2) (R 2) [50,5,80,384,128] 13 := by
  apply FastRouting.sound _ _ [50,5,80,384,128] 13 (by decide) (choices 1) [8,64,256] r635 c635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u186
  · exact u187
  · exact u188

def b636 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 196 88 24 416 480 416 416), lower := (rows 51 7 196 88 24 32 64 128 256), losses := [] }

theorem u636 : Upper (D 2) (R 2) [50,5,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b636
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 196 88 48 424 456 392 392), lower := (rows 51 7 196 88 48 32 64 128 256), losses := [] }

theorem u637 : Upper (D 2) (R 2) [50,5,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b637
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 24, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 51 7 196 88 144 296 360 424 296), lower := (rows 51 7 196 88 144 32 64 128 256), losses := [] }

theorem u638 : Upper (D 2) (R 2) [50,5,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b638
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r639 : Route 9 := (fun mask => (mask,id))

def c639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u639 : Upper (D 2) (R 2) [50,5,192,80,256] 13 := by
  apply FastRouting.sound _ _ [50,5,192,80,256] 13 (by decide) (choices 1) [8,128,256] r639 c639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u189
  · exact u190
  · exact u191

def b640 : PairBound 9 := { available := 480, camps := [{ cop := 8, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 196 280 24 480 480 480 480), lower := (rows 51 7 196 280 24 32 64 128 256), losses := [] }

theorem u640 : Upper (D 2) (R 2) [50,5,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b640
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 196 280 48 488 456 456 456), lower := (rows 51 7 196 280 48 32 64 128 256), losses := [] }

theorem u641 : Upper (D 2) (R 2) [50,5,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b641
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 392, targets := 64 },{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4),(3,6)], upper := (rows 51 7 196 280 80 424 488 424 424), lower := (rows 51 7 196 280 80 32 64 128 256), losses := [] }

theorem u642 : Upper (D 2) (R 2) [50,5,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b642
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 7 196 280 272 232 232 232 488), lower := (rows 51 7 196 280 272 32 64 128 256), losses := [] }

theorem u643 : Upper (D 2) (R 2) [50,5,192,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b643
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r644 : Route 9 := (fun mask => (mask,id))

def c644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u644 : Upper (D 2) (R 2) [50,5,192,320,8] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320,8] 13 (by decide) (choices 1) [16,128,256] r644 c644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u192
  · exact u193
  · exact u194

def b645 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 196 328 48 440 472 408 408), lower := (rows 51 7 196 328 48 32 64 128 256), losses := [] }

theorem u645 : Upper (D 2) (R 2) [50,5,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b645
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m646_8 : Upper (D 2) (R 2) [50,5,192,320,128,8] 13 :=
  permutation_upper _ _ _ [50,5,192,320,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u193

theorem m646_16 : Upper (D 2) (R 2) [50,5,192,320,128,16] 13 :=
  permutation_upper _ _ _ [50,5,192,320,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u195

def r646 : Route 9 := (fun mask => (mask,id))

def c646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u646 : Upper (D 2) (R 2) [50,5,192,320,128] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320,128] 13 (by decide) (choices 1) [8,16,256] r646 c646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m646_8
  · exact m646_16
  · exact u197

theorem m647_8 : Upper (D 2) (R 2) [50,5,192,320,256,8] 13 :=
  permutation_upper _ _ _ [50,5,192,320,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u194

theorem m647_16 : Upper (D 2) (R 2) [50,5,192,320,256,16] 13 :=
  permutation_upper _ _ _ [50,5,192,320,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u196

theorem m647_128 : Upper (D 2) (R 2) [50,5,192,320,256,128] 13 :=
  permutation_upper _ _ _ [50,5,192,320,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u197

def r647 : Route 9 := (fun mask => (mask,id))

def c647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u647 : Upper (D 2) (R 2) [50,5,192,320,256] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320,256] 13 (by decide) (choices 1) [8,16,128] r647 c647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m647_8
  · exact m647_16
  · exact m647_128

def b648 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 69 152 48 480 448 448 448), lower := (rows 51 14 69 152 48 32 64 128 256), losses := [] }

theorem u648 : Upper (D 2) (R 2) [50,12,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b648
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 452, targets := 16 },{ cop := 0, region := 392, targets := 64 }], pairs := [(2,4),(3,6)], upper := (rows 51 14 69 152 80 416 480 416 416), lower := (rows 51 14 69 152 80 32 64 128 256), losses := [] }

theorem u649 : Upper (D 2) (R 2) [50,12,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b649
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 14 69 152 144 352 352 480 352), lower := (rows 51 14 69 152 144 32 64 128 256), losses := [] }

theorem u650 : Upper (D 2) (R 2) [50,12,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b650
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r651 : Route 9 := (fun mask => (mask,id))

def c651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u651 : Upper (D 2) (R 2) [50,12,65,144,256] 13 := by
  apply FastRouting.sound _ _ [50,12,65,144,256] 13 (by decide) (choices 1) [64,128,256] r651 c651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u198
  · exact u199
  · exact u200

def b652 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 69 200 48 432 464 400 400), lower := (rows 51 14 69 200 48 32 64 128 256), losses := [] }

theorem u652 : Upper (D 2) (R 2) [50,12,65,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b652
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 324, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,7)], upper := (rows 51 14 69 200 144 304 368 432 304), lower := (rows 51 14 69 200 144 32 64 128 256), losses := [] }

theorem u653 : Upper (D 2) (R 2) [50,12,65,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b653
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m654_16 : Upper (D 2) (R 2) [50,12,65,192,256,16] 13 :=
  permutation_upper _ _ _ [50,12,65,192,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u201

theorem m654_128 : Upper (D 2) (R 2) [50,12,65,192,256,128] 13 :=
  permutation_upper _ _ _ [50,12,65,192,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u202

def r654 : Route 9 := (fun mask => (mask,id))

def c654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u654 : Upper (D 2) (R 2) [50,12,65,192,256] 13 := by
  apply FastRouting.sound _ _ [50,12,65,192,256] 13 (by decide) (choices 1) [16,128,256] r654 c654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m654_16
  · exact m654_128
  · exact u203

def b655 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 69 392 48 496 464 464 464), lower := (rows 51 14 69 392 48 32 64 128 256), losses := [] }

theorem u655 : Upper (D 2) (R 2) [50,12,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b655
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 51 14 69 392 80 432 496 432 432), lower := (rows 51 14 69 392 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 29 16 49 0 145 273), good := (rows 443 14 431 392 440 32 0 128 256) }] }

theorem u656 : Upper (D 2) (R 2) [50,12,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b656
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m657_16 : Upper (D 2) (R 2) [50,12,65,384,128,16] 13 :=
  permutation_upper _ _ _ [50,12,65,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u204

theorem m657_64 : Upper (D 2) (R 2) [50,12,65,384,128,64] 13 :=
  permutation_upper _ _ _ [50,12,65,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u205

def r657 : Route 9 := (fun mask => (mask,id))

def c657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u657 : Upper (D 2) (R 2) [50,12,65,384,128] 13 := by
  apply FastRouting.sound _ _ [50,12,65,384,128] 13 (by decide) (choices 1) [16,64,256] r657 c657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m657_16
  · exact m657_64
  · exact u206

def b658 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 51 14 84 392 17 480 480 480 480), lower := (rows 51 14 84 392 17 32 64 128 256), losses := [] }

theorem u658 : Upper (D 2) (R 2) [50,12,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b658
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 84 392 48 481 449 449 449), lower := (rows 51 14 84 392 48 32 64 128 256), losses := [] }

theorem u659 : Upper (D 2) (R 2) [50,12,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b659
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P02
