import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0004

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b720 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 200 48 312 344 408 280), lower := (rows 51 70 133 200 48 32 64 128 256), losses := [] }

theorem u720 : Upper (D 2) (R 2) [50,68,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b720
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m721_8 : Upper (D 2) (R 2) [50,68,129,192,256,8] 13 :=
  permutation_upper _ _ _ [50,68,129,192,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u240

theorem m721_16 : Upper (D 2) (R 2) [50,68,129,192,256,16] 13 :=
  permutation_upper _ _ _ [50,68,129,192,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u241

def r721 : Route 9 := (fun mask => (mask,id))

def c721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u721 : Upper (D 2) (R 2) [50,68,129,192,256] 13 := by
  apply FastRouting.sound _ _ [50,68,129,192,256] 13 (by decide) (choices 1) [8,16,256] r721 c721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m721_8
  · exact m721_16
  · exact u242

def b722 : PairBound 9 := { available := 480, camps := [{ cop := 8, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 133 280 24 480 480 480 480), lower := (rows 51 70 133 280 24 32 64 128 256), losses := [] }

theorem u722 : Upper (D 2) (R 2) [50,68,129,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b722
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 280 48 488 456 456 456), lower := (rows 51 70 133 280 48 32 64 128 256), losses := [] }

theorem u723 : Upper (D 2) (R 2) [50,68,129,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b723
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 133 280 80 424 488 424 424), lower := (rows 51 70 133 280 80 32 64 128 256), losses := [] }

theorem u724 : Upper (D 2) (R 2) [50,68,129,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b724
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 360, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 51 70 133 280 144 360 360 488 360), lower := (rows 51 70 133 280 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 25 16 61 93 0 285), good := (rows 379 358 367 376 376 32 64 0 256) }] }

theorem u725 : Upper (D 2) (R 2) [50,68,129,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b725
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 70 133 280 272 232 232 232 488), lower := (rows 51 70 133 280 272 32 64 128 256), losses := [] }

theorem u726 : Upper (D 2) (R 2) [50,68,129,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b726
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 328 24 432 496 432 432), lower := (rows 51 70 133 328 24 32 64 128 256), losses := [] }

theorem u727 : Upper (D 2) (R 2) [50,68,129,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b727
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 328 48 440 472 408 408), lower := (rows 51 70 133 328 48 32 64 128 256), losses := [] }

theorem u728 : Upper (D 2) (R 2) [50,68,129,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b728
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 51 70 133 328 144 312 376 440 312), lower := (rows 51 70 133 328 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 29 16 49 81 0 273), good := (rows 379 78 367 328 376 32 64 0 256) }] }

theorem u729 : Upper (D 2) (R 2) [50,68,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b729
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m730_8 : Upper (D 2) (R 2) [50,68,129,320,256,8] 13 :=
  permutation_upper _ _ _ [50,68,129,320,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u243

theorem m730_16 : Upper (D 2) (R 2) [50,68,129,320,256,16] 13 :=
  permutation_upper _ _ _ [50,68,129,320,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u244

theorem m730_128 : Upper (D 2) (R 2) [50,68,129,320,256,128] 13 :=
  permutation_upper _ _ _ [50,68,129,320,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u245

def r730 : Route 9 := (fun mask => (mask,id))

def c730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u730 : Upper (D 2) (R 2) [50,68,129,320,256] 13 := by
  apply FastRouting.sound _ _ [50,68,129,320,256] 13 (by decide) (choices 1) [8,16,128] r730 c730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m730_8
  · exact m730_16
  · exact m730_128

def b731 : PairBound 9 := { available := 368, camps := [], pairs := [(1,7)], upper := (rows 51 70 133 392 24 368 368 496 368), lower := (rows 51 70 133 392 24 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 24 57 89 0 281), good := (rows 371 70 359 376 376 32 64 0 256) }] }

theorem u731 : Upper (D 2) (R 2) [50,68,129,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b731
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 392 48 376 344 472 344), lower := (rows 51 70 133 392 48 32 64 128 256), losses := [] }

theorem u732 : Upper (D 2) (R 2) [50,68,129,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b732
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 133 392 80 312 376 440 312), lower := (rows 51 70 133 392 80 32 64 128 256), losses := [] }

theorem u733 : Upper (D 2) (R 2) [50,68,129,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b733
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m734_8 : Upper (D 2) (R 2) [50,68,129,384,256,8] 13 :=
  permutation_upper _ _ _ [50,68,129,384,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u246

theorem m734_16 : Upper (D 2) (R 2) [50,68,129,384,256,16] 13 :=
  permutation_upper _ _ _ [50,68,129,384,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u247

theorem m734_64 : Upper (D 2) (R 2) [50,68,129,384,256,64] 13 :=
  permutation_upper _ _ _ [50,68,129,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u248

def r734 : Route 9 := (fun mask => (mask,id))

def c734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u734 : Upper (D 2) (R 2) [50,68,129,384,256] 13 := by
  apply FastRouting.sound _ _ [50,68,129,384,256] 13 (by decide) (choices 1) [8,16,64] r734 c734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m734_8
  · exact m734_16
  · exact m734_64

def b735 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 422, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 140 88 17 416 480 416 416), lower := (rows 51 70 140 88 17 32 64 128 256), losses := [] }

theorem u735 : Upper (D 2) (R 2) [50,68,136,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b735
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 140 88 48 417 449 385 385), lower := (rows 51 70 140 88 48 32 64 128 256), losses := [] }

theorem u736 : Upper (D 2) (R 2) [50,68,136,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b736
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7)], upper := (rows 51 70 140 88 144 289 353 417 289), lower := (rows 51 70 140 88 144 32 64 128 256), losses := [] }

theorem u737 : Upper (D 2) (R 2) [50,68,136,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b737
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r738 : Route 9 := (fun mask => (mask,id))

def c738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u738 : Upper (D 2) (R 2) [50,68,136,80,256] 13 := by
  apply FastRouting.sound _ _ [50,68,136,80,256] 13 (by decide) (choices 1) [1,128,256] r738 c738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u249
  · exact u250
  · exact u251

def b739 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 140 265 48 496 464 464 464), lower := (rows 51 70 140 265 48 32 64 128 256), losses := [] }

theorem u739 : Upper (D 2) (R 2) [50,68,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b739
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 140 265 80 432 496 432 432), lower := (rows 51 70 140 265 80 32 64 128 256), losses := [] }

theorem u740 : Upper (D 2) (R 2) [50,68,136,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b740
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m741_16 : Upper (D 2) (R 2) [50,68,136,257,128,16] 13 :=
  permutation_upper _ _ _ [50,68,136,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u252

theorem m741_64 : Upper (D 2) (R 2) [50,68,136,257,128,64] 13 :=
  permutation_upper _ _ _ [50,68,136,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u253

def r741 : Route 9 := (fun mask => (mask,id))

def c741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u741 : Upper (D 2) (R 2) [50,68,136,257,128] 13 := by
  apply FastRouting.sound _ _ [50,68,136,257,128] 13 (by decide) (choices 1) [16,64,256] r741 c741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m741_16
  · exact m741_64
  · exact u254

def b742 : PairBound 9 := { available := 240, camps := [], pairs := [(1,8),(2,8)], upper := (rows 51 70 140 265 272 240 240 240 496), lower := (rows 51 70 140 265 272 32 64 128 256), losses := [{ target := 8, region := (rows 1 10 12 8 16 49 81 145 0), good := (rows 243 70 142 239 240 32 64 128 0) }] }

theorem u742 : Upper (D 2) (R 2) [50,68,136,257,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b742
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 230, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 140 280 17 480 480 480 480), lower := (rows 51 70 140 280 17 32 64 128 256), losses := [] }

theorem u743 : Upper (D 2) (R 2) [50,68,136,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b743
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 140 280 48 481 449 449 449), lower := (rows 51 70 140 280 48 32 64 128 256), losses := [] }

theorem u744 : Upper (D 2) (R 2) [50,68,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b744
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 140 280 80 417 481 417 417), lower := (rows 51 70 140 280 80 32 64 128 256), losses := [] }

theorem u745 : Upper (D 2) (R 2) [50,68,136,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b745
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r746 : Route 9 := (fun mask => (mask,id))

def c746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u746 : Upper (D 2) (R 2) [50,68,136,272,128] 13 := by
  apply FastRouting.sound _ _ [50,68,136,272,128] 13 (by decide) (choices 1) [1,64,256] r746 c746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u255
  · exact u256
  · exact u257

def b747 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 70 140 280 272 225 225 225 481), lower := (rows 51 70 140 280 272 32 64 128 256), losses := [] }

theorem u747 : Upper (D 2) (R 2) [50,68,136,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b747
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 328 17 432 496 432 432), lower := (rows 51 70 140 328 17 32 64 128 256), losses := [] }

theorem u748 : Upper (D 2) (R 2) [50,68,136,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b748
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 140 328 48 433 465 401 401), lower := (rows 51 70 140 328 48 32 64 128 256), losses := [] }

theorem u749 : Upper (D 2) (R 2) [50,68,136,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b749
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7)], upper := (rows 51 70 140 328 144 305 369 433 305), lower := (rows 51 70 140 328 144 32 64 128 256), losses := [] }

theorem u750 : Upper (D 2) (R 2) [50,68,136,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b750
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m751_1 : Upper (D 2) (R 2) [50,68,136,320,256,1] 13 :=
  permutation_upper _ _ _ [50,68,136,320,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u258

theorem m751_16 : Upper (D 2) (R 2) [50,68,136,320,256,16] 13 :=
  permutation_upper _ _ _ [50,68,136,320,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u259

theorem m751_128 : Upper (D 2) (R 2) [50,68,136,320,256,128] 13 :=
  permutation_upper _ _ _ [50,68,136,320,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u260

def r751 : Route 9 := (fun mask => (mask,id))

def c751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u751 : Upper (D 2) (R 2) [50,68,136,320,256] 13 := by
  apply FastRouting.sound _ _ [50,68,136,320,256] 13 (by decide) (choices 1) [1,16,128] r751 c751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m751_1
  · exact m751_16
  · exact m751_128

def b752 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 148 104 17 424 456 392 392), lower := (rows 51 70 148 104 17 32 64 128 256), losses := [] }

theorem u752 : Upper (D 2) (R 2) [50,68,144,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b752
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 104 24 417 449 385 385), lower := (rows 51 70 148 104 24 32 64 128 256), losses := [] }

theorem u753 : Upper (D 2) (R 2) [50,68,144,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b753
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 70 148 104 144 297 329 393 265), lower := (rows 51 70 148 104 144 32 64 128 256), losses := [] }

theorem u754 : Upper (D 2) (R 2) [50,68,144,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b754
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r755 : Route 9 := (fun mask => (mask,id))

def c755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u755 : Upper (D 2) (R 2) [50,68,144,96,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,96,256] 13 (by decide) (choices 1) [1,8,128,256] r755 c755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u261
  · exact u262
  · exact u263
  · exact u264

def b756 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 70 148 137 24 352 352 480 352), lower := (rows 51 70 148 137 24 32 64 128 256), losses := [] }

theorem u756 : Upper (D 2) (R 2) [50,68,144,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b756
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 148 137 48 360 328 456 328), lower := (rows 51 70 148 137 48 32 64 128 256), losses := [] }

theorem u757 : Upper (D 2) (R 2) [50,68,144,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b757
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 137 80 296 360 424 296), lower := (rows 51 70 148 137 80 32 64 128 256), losses := [] }

theorem u758 : Upper (D 2) (R 2) [50,68,144,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b758
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r759 : Route 9 := (fun mask => (mask,id))

def c759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u759 : Upper (D 2) (R 2) [50,68,144,129,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,129,256] 13 (by decide) (choices 1) [8,64,256] r759 c759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u265
  · exact u266
  · exact u267

def b760 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 148 168 17 360 328 456 328), lower := (rows 51 70 148 168 17 32 64 128 256), losses := [] }

theorem u760 : Upper (D 2) (R 2) [50,68,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b760
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 70 148 168 24 353 321 449 321), lower := (rows 51 70 148 168 24 32 64 128 256), losses := [] }

theorem u761 : Upper (D 2) (R 2) [50,68,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b761
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 168 80 297 329 393 265), lower := (rows 51 70 148 168 80 32 64 128 256), losses := [] }

theorem u762 : Upper (D 2) (R 2) [50,68,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b762
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r763 : Route 9 := (fun mask => (mask,id))

def c763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u763 : Upper (D 2) (R 2) [50,68,144,160,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,160,256] 13 (by decide) (choices 1) [1,8,64,256] r763 c763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u268
  · exact u269
  · exact u270
  · exact u271

def b764 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 148 200 17 296 360 424 296), lower := (rows 51 70 148 200 17 32 64 128 256), losses := [] }

theorem u764 : Upper (D 2) (R 2) [50,68,144,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b764
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 200 24 289 353 417 289), lower := (rows 51 70 148 200 24 32 64 128 256), losses := [] }

theorem u765 : Upper (D 2) (R 2) [50,68,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b765
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 148 200 48 297 329 393 265), lower := (rows 51 70 148 200 48 32 64 128 256), losses := [] }

theorem u766 : Upper (D 2) (R 2) [50,68,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b766
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r767 : Route 9 := (fun mask => (mask,id))

def c767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u767 : Upper (D 2) (R 2) [50,68,144,192,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,192,256] 13 (by decide) (choices 1) [1,8,256] r767 c767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u272
  · exact u273
  · exact u274

def b768 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 265 24 480 480 480 480), lower := (rows 51 70 148 265 24 32 64 128 256), losses := [] }

theorem u768 : Upper (D 2) (R 2) [50,68,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b768
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 148 265 48 488 456 456 456), lower := (rows 51 70 148 265 48 32 64 128 256), losses := [] }

theorem u769 : Upper (D 2) (R 2) [50,68,144,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b769
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 265 80 424 488 424 424), lower := (rows 51 70 148 265 80 32 64 128 256), losses := [] }

theorem u770 : Upper (D 2) (R 2) [50,68,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b770
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 70 148 265 144 360 360 488 360), lower := (rows 51 70 148 265 144 32 64 128 256), losses := [] }

theorem u771 : Upper (D 2) (R 2) [50,68,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b771
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r772 : Route 9 := (fun mask => (mask,id))

def c772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u772 : Upper (D 2) (R 2) [50,68,144,257,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,257,256] 13 (by decide) (choices 1) [8,64,128] r772 c772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u275
  · exact u276
  · exact u277

def b773 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 148 296 17 488 456 456 456), lower := (rows 51 70 148 296 17 32 64 128 256), losses := [] }

theorem u773 : Upper (D 2) (R 2) [50,68,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b773
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 296 24 481 449 449 449), lower := (rows 51 70 148 296 24 32 64 128 256), losses := [] }

theorem u774 : Upper (D 2) (R 2) [50,68,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b774
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 296 80 425 457 393 393), lower := (rows 51 70 148 296 80 32 64 128 256), losses := [] }

theorem u775 : Upper (D 2) (R 2) [50,68,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b775
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 70 148 296 144 361 329 457 329), lower := (rows 51 70 148 296 144 32 64 128 256), losses := [] }

theorem u776 : Upper (D 2) (R 2) [50,68,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b776
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r777 : Route 9 := (fun mask => (mask,id))

def c777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u777 : Upper (D 2) (R 2) [50,68,144,288,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,288,256] 13 (by decide) (choices 1) [1,8,64,128] r777 c777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u278
  · exact u279
  · exact u280
  · exact u281

def b778 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 148 328 17 424 488 424 424), lower := (rows 51 70 148 328 17 32 64 128 256), losses := [] }

theorem u778 : Upper (D 2) (R 2) [50,68,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b778
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 328 24 417 481 417 417), lower := (rows 51 70 148 328 24 32 64 128 256), losses := [] }

theorem u779 : Upper (D 2) (R 2) [50,68,144,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b779
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P02
