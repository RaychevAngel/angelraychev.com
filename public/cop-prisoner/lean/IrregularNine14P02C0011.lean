import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0003

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 51 14 84 392 80 417 481 417 417), lower := (rows 51 14 84 392 80 32 64 128 256), losses := [] }

theorem u660 : Upper (D 2) (R 2) [50,12,80,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b660
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 324, targets := 128 }], pairs := [(2,7),(3,4)], upper := (rows 51 14 84 392 144 353 353 481 353), lower := (rows 51 14 84 392 144 32 64 128 256), losses := [] }

theorem u661 : Upper (D 2) (R 2) [50,12,80,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b661
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 196 328 17 432 496 432 432), lower := (rows 51 14 196 328 17 32 64 128 256), losses := [] }

theorem u662 : Upper (D 2) (R 2) [50,12,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b662
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 196 328 48 433 465 401 401), lower := (rows 51 14 196 328 48 32 64 128 256), losses := [] }

theorem u663 : Upper (D 2) (R 2) [50,12,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b663
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7)], upper := (rows 51 14 196 328 144 305 369 433 305), lower := (rows 51 14 196 328 144 32 64 128 256), losses := [] }

theorem u664 : Upper (D 2) (R 2) [50,12,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b664
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 28 392 20 480 480 480 480), lower := (rows 51 67 28 392 20 32 64 128 256), losses := [] }

theorem u665 : Upper (D 2) (R 2) [50,65,24,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b665
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 28 392 48 484 452 452 452), lower := (rows 51 67 28 392 48 32 64 128 256), losses := [] }

theorem u666 : Upper (D 2) (R 2) [50,65,24,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b666
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 67 28 392 80 420 484 420 420), lower := (rows 51 67 28 392 80 32 64 128 256), losses := [] }

theorem u667 : Upper (D 2) (R 2) [50,65,24,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b667
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 67 28 392 144 356 356 484 356), lower := (rows 51 67 28 392 144 32 64 128 256), losses := [] }

theorem u668 : Upper (D 2) (R 2) [50,65,24,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b668
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 67 76 392 20 432 496 432 432), lower := (rows 51 67 76 392 20 32 64 128 256), losses := [] }

theorem u669 : Upper (D 2) (R 2) [50,65,72,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b669
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 76 392 48 436 468 404 404), lower := (rows 51 67 76 392 48 32 64 128 256), losses := [] }

theorem u670 : Upper (D 2) (R 2) [50,65,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b670
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m671_4 : Upper (D 2) (R 2) [50,65,72,384,128,4] 13 :=
  permutation_upper _ _ _ [50,65,72,384,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u207

theorem m671_16 : Upper (D 2) (R 2) [50,65,72,384,128,16] 13 :=
  permutation_upper _ _ _ [50,65,72,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u208

def r671 : Route 9 := (fun mask => (mask,id))

def c671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u671 : Upper (D 2) (R 2) [50,65,72,384,128] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384,128] 13 (by decide) (choices 1) [4,16,256] r671 c671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m671_4
  · exact m671_16
  · exact u209

def b672 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 140 268 48 496 464 464 464), lower := (rows 51 67 140 268 48 32 64 128 256), losses := [] }

theorem u672 : Upper (D 2) (R 2) [50,65,136,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b672
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 67 140 268 80 432 496 432 432), lower := (rows 51 67 140 268 80 32 64 128 256), losses := [] }

theorem u673 : Upper (D 2) (R 2) [50,65,136,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b673
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 67 140 268 144 368 368 496 368), lower := (rows 51 67 140 268 144 32 64 128 256), losses := [] }

theorem u674 : Upper (D 2) (R 2) [50,65,136,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b674
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 140 280 20 480 480 480 480), lower := (rows 51 67 140 280 20 32 64 128 256), losses := [] }

theorem u675 : Upper (D 2) (R 2) [50,65,136,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b675
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 140 280 48 484 452 452 452), lower := (rows 51 67 140 280 48 32 64 128 256), losses := [] }

theorem u676 : Upper (D 2) (R 2) [50,65,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b676
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 67 140 280 80 420 484 420 420), lower := (rows 51 67 140 280 80 32 64 128 256), losses := [] }

theorem u677 : Upper (D 2) (R 2) [50,65,136,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b677
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r678 : Route 9 := (fun mask => (mask,id))

def c678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u678 : Upper (D 2) (R 2) [50,65,136,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272,128] 13 (by decide) (choices 1) [4,64,256] r678 c678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u210
  · exact u211
  · exact u212

def b679 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 67 140 280 272 228 228 228 484), lower := (rows 51 67 140 280 272 32 64 128 256), losses := [] }

theorem u679 : Upper (D 2) (R 2) [50,65,136,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b679
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 328 20 432 496 432 432), lower := (rows 51 67 140 328 20 32 64 128 256), losses := [] }

theorem u680 : Upper (D 2) (R 2) [50,65,136,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b680
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 140 328 48 436 468 404 404), lower := (rows 51 67 140 328 48 32 64 128 256), losses := [] }

theorem u681 : Upper (D 2) (R 2) [50,65,136,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b681
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m682_4 : Upper (D 2) (R 2) [50,65,136,320,128,4] 13 :=
  permutation_upper _ _ _ [50,65,136,320,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u213

theorem m682_16 : Upper (D 2) (R 2) [50,65,136,320,128,16] 13 :=
  permutation_upper _ _ _ [50,65,136,320,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u215

def r682 : Route 9 := (fun mask => (mask,id))

def c682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u682 : Upper (D 2) (R 2) [50,65,136,320,128] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320,128] 13 (by decide) (choices 1) [4,16,256] r682 c682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m682_4
  · exact m682_16
  · exact u217

theorem m683_4 : Upper (D 2) (R 2) [50,65,136,320,256,4] 13 :=
  permutation_upper _ _ _ [50,65,136,320,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u214

theorem m683_16 : Upper (D 2) (R 2) [50,65,136,320,256,16] 13 :=
  permutation_upper _ _ _ [50,65,136,320,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u216

theorem m683_128 : Upper (D 2) (R 2) [50,65,136,320,256,128] 13 :=
  permutation_upper _ _ _ [50,65,136,320,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u217

def r683 : Route 9 := (fun mask => (mask,id))

def c683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u683 : Upper (D 2) (R 2) [50,65,136,320,256] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320,256] 13 (by decide) (choices 1) [4,16,128] r683 c683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m683_4
  · exact m683_16
  · exact m683_128

def b684 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 148 392 20 360 360 488 360), lower := (rows 51 67 148 392 20 32 64 128 256), losses := [] }

theorem u684 : Upper (D 2) (R 2) [50,65,144,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b684
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 148 392 24 356 356 484 356), lower := (rows 51 67 148 392 24 32 64 128 256), losses := [] }

theorem u685 : Upper (D 2) (R 2) [50,65,144,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b685
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 148 392 48 364 332 460 332), lower := (rows 51 67 148 392 48 32 64 128 256), losses := [] }

theorem u686 : Upper (D 2) (R 2) [50,65,144,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b686
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 67 148 392 80 300 364 428 300), lower := (rows 51 67 148 392 80 32 64 128 256), losses := [] }

theorem u687 : Upper (D 2) (R 2) [50,65,144,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b687
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 108, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 67 148 392 272 108 108 236 364), lower := (rows 51 67 148 392 272 32 64 128 256), losses := [] }

theorem u688 : Upper (D 2) (R 2) [50,65,144,384,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b688
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 67 196 392 20 312 376 440 312), lower := (rows 51 67 196 392 20 32 64 128 256), losses := [] }

theorem u689 : Upper (D 2) (R 2) [50,65,192,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b689
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 51 67 196 392 24 308 372 436 308), lower := (rows 51 67 196 392 24 32 64 128 256), losses := [] }

theorem u690 : Upper (D 2) (R 2) [50,65,192,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b690
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 196 392 48 316 348 412 284), lower := (rows 51 67 196 392 48 32 64 128 256), losses := [] }

theorem u691 : Upper (D 2) (R 2) [50,65,192,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b691
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m692_4 : Upper (D 2) (R 2) [50,65,192,384,256,4] 13 :=
  permutation_upper _ _ _ [50,65,192,384,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u218

theorem m692_8 : Upper (D 2) (R 2) [50,65,192,384,256,8] 13 :=
  permutation_upper _ _ _ [50,65,192,384,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u219

theorem m692_16 : Upper (D 2) (R 2) [50,65,192,384,256,16] 13 :=
  permutation_upper _ _ _ [50,65,192,384,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u220

def r692 : Route 9 := (fun mask => (mask,id))

def c692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u692 : Upper (D 2) (R 2) [50,65,192,384,256] 13 := by
  apply FastRouting.sound _ _ [50,65,192,384,256] 13 (by decide) (choices 1) [4,8,16] r692 c692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m692_4
  · exact m692_8
  · exact m692_16

def b693 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 13 152 48 480 448 448 448), lower := (rows 51 70 13 152 48 32 64 128 256), losses := [] }

theorem u693 : Upper (D 2) (R 2) [50,68,9,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b693
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 13 152 80 416 480 416 416), lower := (rows 51 70 13 152 80 32 64 128 256), losses := [] }

theorem u694 : Upper (D 2) (R 2) [50,68,9,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b694
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 70 13 152 144 352 352 480 352), lower := (rows 51 70 13 152 144 32 64 128 256), losses := [] }

theorem u695 : Upper (D 2) (R 2) [50,68,9,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b695
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r696 : Route 9 := (fun mask => (mask,id))

def c696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u696 : Upper (D 2) (R 2) [50,68,9,144,256] 13 := by
  apply FastRouting.sound _ _ [50,68,9,144,256] 13 (by decide) (choices 1) [64,128,256] r696 c696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u221
  · exact u222
  · exact u223

def b697 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 13 200 48 432 464 400 400), lower := (rows 51 70 13 200 48 32 64 128 256), losses := [] }

theorem u697 : Upper (D 2) (R 2) [50,68,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b697
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,7)], upper := (rows 51 70 13 200 144 304 368 432 304), lower := (rows 51 70 13 200 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 49 81 0 273), good := (rows 371 70 367 72 368 32 64 0 256) }] }

theorem u698 : Upper (D 2) (R 2) [50,68,9,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b698
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m699_16 : Upper (D 2) (R 2) [50,68,9,192,256,16] 13 :=
  permutation_upper _ _ _ [50,68,9,192,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u224

theorem m699_128 : Upper (D 2) (R 2) [50,68,9,192,256,128] 13 :=
  permutation_upper _ _ _ [50,68,9,192,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u225

def r699 : Route 9 := (fun mask => (mask,id))

def c699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u699 : Upper (D 2) (R 2) [50,68,9,192,256] 13 := by
  apply FastRouting.sound _ _ [50,68,9,192,256] 13 (by decide) (choices 1) [16,128,256] r699 c699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m699_16
  · exact m699_128
  · exact u226

def b700 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 13 392 48 496 464 464 464), lower := (rows 51 70 13 392 48 32 64 128 256), losses := [] }

theorem u700 : Upper (D 2) (R 2) [50,68,9,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b700
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 13 392 80 432 496 432 432), lower := (rows 51 70 13 392 80 32 64 128 256), losses := [] }

theorem u701 : Upper (D 2) (R 2) [50,68,9,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b701
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m702_16 : Upper (D 2) (R 2) [50,68,9,384,128,16] 13 :=
  permutation_upper _ _ _ [50,68,9,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u227

theorem m702_64 : Upper (D 2) (R 2) [50,68,9,384,128,64] 13 :=
  permutation_upper _ _ _ [50,68,9,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u228

def r702 : Route 9 := (fun mask => (mask,id))

def c702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u702 : Upper (D 2) (R 2) [50,68,9,384,128] 13 := by
  apply FastRouting.sound _ _ [50,68,9,384,128] 13 (by decide) (choices 1) [16,64,256] r702 c702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m702_16
  · exact m702_64
  · exact u229

def b703 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 28 168 17 480 448 448 448), lower := (rows 51 70 28 168 17 32 64 128 256), losses := [] }

theorem u703 : Upper (D 2) (R 2) [50,68,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b703
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 28 168 80 417 449 385 385), lower := (rows 51 70 28 168 80 32 64 128 256), losses := [] }

theorem u704 : Upper (D 2) (R 2) [50,68,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b704
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 70 28 168 144 353 321 449 321), lower := (rows 51 70 28 168 144 32 64 128 256), losses := [] }

theorem u705 : Upper (D 2) (R 2) [50,68,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b705
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r706 : Route 9 := (fun mask => (mask,id))

def c706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u706 : Upper (D 2) (R 2) [50,68,24,160,256] 13 := by
  apply FastRouting.sound _ _ [50,68,24,160,256] 13 (by decide) (choices 1) [1,64,128,256] r706 c706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u230
  · exact u231
  · exact u232
  · exact u233

def b707 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 28 392 17 480 480 480 480), lower := (rows 51 70 28 392 17 32 64 128 256), losses := [] }

theorem u707 : Upper (D 2) (R 2) [50,68,24,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b707
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 28 392 48 481 449 449 449), lower := (rows 51 70 28 392 48 32 64 128 256), losses := [] }

theorem u708 : Upper (D 2) (R 2) [50,68,24,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b708
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 28 392 80 417 481 417 417), lower := (rows 51 70 28 392 80 32 64 128 256), losses := [] }

theorem u709 : Upper (D 2) (R 2) [50,68,24,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b709
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 70 28 392 144 353 353 481 353), lower := (rows 51 70 28 392 144 32 64 128 256), losses := [] }

theorem u710 : Upper (D 2) (R 2) [50,68,24,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b710
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 133 88 24 416 480 416 416), lower := (rows 51 70 133 88 24 32 64 128 256), losses := [] }

theorem u711 : Upper (D 2) (R 2) [50,68,129,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b711
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 88 48 424 456 392 392), lower := (rows 51 70 133 88 48 32 64 128 256), losses := [] }

theorem u712 : Upper (D 2) (R 2) [50,68,129,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b712
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,5),(3,7)], upper := (rows 51 70 133 88 144 296 360 424 296), lower := (rows 51 70 133 88 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 148 0 64 128 256), good := (rows 27 94 149 88 144 0 64 144 256) }] }

theorem u713 : Upper (D 2) (R 2) [50,68,129,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b713
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r714 : Route 9 := (fun mask => (mask,id))

def c714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u714 : Upper (D 2) (R 2) [50,68,129,80,256] 13 := by
  apply FastRouting.sound _ _ [50,68,129,80,256] 13 (by decide) (choices 1) [8,128,256] r714 c714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u234
  · exact u235
  · exact u236

def b715 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 133 152 24 352 352 480 352), lower := (rows 51 70 133 152 24 32 64 128 256), losses := [] }

theorem u715 : Upper (D 2) (R 2) [50,68,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b715
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 152 48 360 328 456 328), lower := (rows 51 70 133 152 48 32 64 128 256), losses := [] }

theorem u716 : Upper (D 2) (R 2) [50,68,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b716
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 133 152 80 296 360 424 296), lower := (rows 51 70 133 152 80 32 64 128 256), losses := [] }

theorem u717 : Upper (D 2) (R 2) [50,68,129,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b717
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r718 : Route 9 := (fun mask => (mask,id))

def c718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u718 : Upper (D 2) (R 2) [50,68,129,144,256] 13 := by
  apply FastRouting.sound _ _ [50,68,129,144,256] 13 (by decide) (choices 1) [8,64,256] r718 c718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u237
  · exact u238
  · exact u239

def b719 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 200 24 304 368 432 304), lower := (rows 51 70 133 200 24 32 64 128 256), losses := [] }

theorem u719 : Upper (D 2) (R 2) [50,68,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b719
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P02
