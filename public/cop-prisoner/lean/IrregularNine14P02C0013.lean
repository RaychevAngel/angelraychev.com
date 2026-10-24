import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0004
import IrregularNine14P02C0005

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 148 328 48 425 457 393 393), lower := (rows 51 70 148 328 48 32 64 128 256), losses := [] }

theorem u780 : Upper (D 2) (R 2) [50,68,144,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b780
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 70 148 328 144 297 361 425 297), lower := (rows 51 70 148 328 144 32 64 128 256), losses := [] }

theorem u781 : Upper (D 2) (R 2) [50,68,144,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b781
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r782 : Route 9 := (fun mask => (mask,id))

def c782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u782 : Upper (D 2) (R 2) [50,68,144,320,256] 13 := by
  apply FastRouting.sound _ _ [50,68,144,320,256] 13 (by decide) (choices 1) [1,8,128] r782 c782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u282
  · exact u283
  · exact u284

def b783 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 148 392 17 360 360 488 360), lower := (rows 51 70 148 392 17 32 64 128 256), losses := [] }

theorem u783 : Upper (D 2) (R 2) [50,68,144,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b783
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 70 148 392 24 353 353 481 353), lower := (rows 51 70 148 392 24 32 64 128 256), losses := [] }

theorem u784 : Upper (D 2) (R 2) [50,68,144,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b784
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 148 392 48 361 329 457 329), lower := (rows 51 70 148 392 48 32 64 128 256), losses := [] }

theorem u785 : Upper (D 2) (R 2) [50,68,144,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b785
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 392 80 297 361 425 297), lower := (rows 51 70 148 392 80 32 64 128 256), losses := [] }

theorem u786 : Upper (D 2) (R 2) [50,68,144,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b786
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 70 148 392 272 105 105 233 361), lower := (rows 51 70 148 392 272 32 64 128 256), losses := [] }

theorem u787 : Upper (D 2) (R 2) [50,68,144,384,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b787
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 73 24 432 496 432 432), lower := (rows 51 70 388 73 24 32 64 128 256), losses := [] }

theorem u788 : Upper (D 2) (R 2) [50,68,384,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b788
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 73 48 440 472 408 408), lower := (rows 51 70 388 73 48 32 64 128 256), losses := [] }

theorem u789 : Upper (D 2) (R 2) [50,68,384,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b789
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,7)], upper := (rows 51 70 388 73 144 312 376 440 312), lower := (rows 51 70 388 73 144 32 64 128 256), losses := [] }

theorem u790 : Upper (D 2) (R 2) [50,68,384,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b790
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 422, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 388 88 17 424 488 424 424), lower := (rows 51 70 388 88 17 32 64 128 256), losses := [] }

theorem u791 : Upper (D 2) (R 2) [50,68,384,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b791
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 388 88 24 417 481 417 417), lower := (rows 51 70 388 88 24 32 64 128 256), losses := [] }

theorem u792 : Upper (D 2) (R 2) [50,68,384,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b792
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 88 48 425 457 393 393), lower := (rows 51 70 388 88 48 32 64 128 256), losses := [] }

theorem u793 : Upper (D 2) (R 2) [50,68,384,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b793
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,5),(3,7)], upper := (rows 51 70 388 88 144 297 361 425 297), lower := (rows 51 70 388 88 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 148 0 64 128 256), good := (rows 27 94 404 88 144 0 64 144 256) }] }

theorem u794 : Upper (D 2) (R 2) [50,68,384,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b794
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r795 : Route 9 := (fun mask => (mask,id))

def c795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u795 : Upper (D 2) (R 2) [50,68,384,129,8] 13 := by
  apply FastRouting.sound _ _ [50,68,384,129,8] 13 (by decide) (choices 1) [16,64,256] r795 c795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u285
  · exact u286
  · exact u287

def b796 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 137 48 376 344 472 344), lower := (rows 51 70 388 137 48 32 64 128 256), losses := [] }

theorem u796 : Upper (D 2) (R 2) [50,68,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b796
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 388 137 80 312 376 440 312), lower := (rows 51 70 388 137 80 32 64 128 256), losses := [] }

theorem u797 : Upper (D 2) (R 2) [50,68,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b797
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m798_8 : Upper (D 2) (R 2) [50,68,384,129,256,8] 13 :=
  permutation_upper _ _ _ [50,68,384,129,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u287

theorem m798_16 : Upper (D 2) (R 2) [50,68,384,129,256,16] 13 :=
  permutation_upper _ _ _ [50,68,384,129,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u288

theorem m798_64 : Upper (D 2) (R 2) [50,68,384,129,256,64] 13 :=
  permutation_upper _ _ _ [50,68,384,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u289

def r798 : Route 9 := (fun mask => (mask,id))

def c798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u798 : Upper (D 2) (R 2) [50,68,384,129,256] 13 := by
  apply FastRouting.sound _ _ [50,68,384,129,256] 13 (by decide) (choices 1) [8,16,64] r798 c798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m798_8
  · exact m798_16
  · exact m798_64

def b799 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 358, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 388 152 17 360 360 488 360), lower := (rows 51 70 388 152 17 32 64 128 256), losses := [] }

theorem u799 : Upper (D 2) (R 2) [50,68,384,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b799
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 388 152 24 353 353 481 353), lower := (rows 51 70 388 152 24 32 64 128 256), losses := [] }

theorem u800 : Upper (D 2) (R 2) [50,68,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b800
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 152 48 361 329 457 329), lower := (rows 51 70 388 152 48 32 64 128 256), losses := [] }

theorem u801 : Upper (D 2) (R 2) [50,68,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b801
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 388 152 80 297 361 425 297), lower := (rows 51 70 388 152 80 32 64 128 256), losses := [] }

theorem u802 : Upper (D 2) (R 2) [50,68,384,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b802
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 51 70 388 152 272 105 105 233 361), lower := (rows 51 70 388 152 272 32 64 128 256), losses := [] }

theorem u803 : Upper (D 2) (R 2) [50,68,384,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b803
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r804 : Route 9 := (fun mask => (mask,id))

def c804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u804 : Upper (D 2) (R 2) [50,68,384,192,1] 13 := by
  apply FastRouting.sound _ _ [50,68,384,192,1] 13 (by decide) (choices 1) [8,16,256] r804 c804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u290
  · exact u291
  · exact u292

def b805 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 200 24 305 369 433 305), lower := (rows 51 70 388 200 24 32 64 128 256), losses := [] }

theorem u805 : Upper (D 2) (R 2) [50,68,384,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b805
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 200 48 313 345 409 281), lower := (rows 51 70 388 200 48 32 64 128 256), losses := [] }

theorem u806 : Upper (D 2) (R 2) [50,68,384,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b806
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m807_1 : Upper (D 2) (R 2) [50,68,384,192,256,1] 13 :=
  permutation_upper _ _ _ [50,68,384,192,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u292

theorem m807_8 : Upper (D 2) (R 2) [50,68,384,192,256,8] 13 :=
  permutation_upper _ _ _ [50,68,384,192,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u293

theorem m807_16 : Upper (D 2) (R 2) [50,68,384,192,256,16] 13 :=
  permutation_upper _ _ _ [50,68,384,192,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u294

def r807 : Route 9 := (fun mask => (mask,id))

def c807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u807 : Upper (D 2) (R 2) [50,68,384,192,256] 13 := by
  apply FastRouting.sound _ _ [50,68,384,192,256] 13 (by decide) (choices 1) [1,8,16] r807 c807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m807_1
  · exact m807_8
  · exact m807_16

def b808 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 76 48 432 464 400 400), lower := (rows 51 194 13 76 48 32 64 128 256), losses := [] }

theorem u808 : Upper (D 2) (R 2) [50,192,9,68,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b808
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 13 76 144 304 368 432 304), lower := (rows 51 194 13 76 144 32 64 128 256), losses := [] }

theorem u809 : Upper (D 2) (R 2) [50,192,9,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b809
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m810_16 : Upper (D 2) (R 2) [50,192,9,68,256,16] 13 :=
  permutation_upper _ _ _ [50,192,9,68,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u295

theorem m810_128 : Upper (D 2) (R 2) [50,192,9,68,256,128] 13 :=
  permutation_upper _ _ _ [50,192,9,68,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u296

def r810 : Route 9 := (fun mask => (mask,id))

def c810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u810 : Upper (D 2) (R 2) [50,192,9,68,256] 13 := by
  apply FastRouting.sound _ _ [50,192,9,68,256] 13 (by decide) (choices 1) [16,128,256] r810 c810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m810_16
  · exact m810_128
  · exact u297

def b811 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 88 20 416 480 416 416), lower := (rows 51 194 13 88 20 32 64 128 256), losses := [] }

theorem u811 : Upper (D 2) (R 2) [50,192,9,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b811
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 88 48 420 452 388 388), lower := (rows 51 194 13 88 48 32 64 128 256), losses := [] }

theorem u812 : Upper (D 2) (R 2) [50,192,9,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b812
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 13 88 144 292 356 420 292), lower := (rows 51 194 13 88 144 32 64 128 256), losses := [] }

theorem u813 : Upper (D 2) (R 2) [50,192,9,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b813
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r814 : Route 9 := (fun mask => (mask,id))

def c814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u814 : Upper (D 2) (R 2) [50,192,9,80,256] 13 := by
  apply FastRouting.sound _ _ [50,192,9,80,256] 13 (by decide) (choices 1) [4,128,256] r814 c814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u298
  · exact u299
  · exact u300

def b815 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 268 48 496 464 464 464), lower := (rows 51 194 13 268 48 32 64 128 256), losses := [] }

theorem u815 : Upper (D 2) (R 2) [50,192,9,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b815
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 13 268 80 432 496 432 432), lower := (rows 51 194 13 268 80 32 64 128 256), losses := [] }

theorem u816 : Upper (D 2) (R 2) [50,192,9,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b816
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 194 13 268 272 240 240 240 496), lower := (rows 51 194 13 268 272 32 64 128 256), losses := [] }

theorem u817 : Upper (D 2) (R 2) [50,192,9,260,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b817
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 280 20 480 480 480 480), lower := (rows 51 194 13 280 20 32 64 128 256), losses := [] }

theorem u818 : Upper (D 2) (R 2) [50,192,9,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b818
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 280 48 484 452 452 452), lower := (rows 51 194 13 280 48 32 64 128 256), losses := [] }

theorem u819 : Upper (D 2) (R 2) [50,192,9,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b819
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 13 280 80 420 484 420 420), lower := (rows 51 194 13 280 80 32 64 128 256), losses := [] }

theorem u820 : Upper (D 2) (R 2) [50,192,9,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b820
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 194 13 280 272 228 228 228 484), lower := (rows 51 194 13 280 272 32 64 128 256), losses := [] }

theorem u821 : Upper (D 2) (R 2) [50,192,9,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b821
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r822 : Route 9 := (fun mask => (mask,id))

def c822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u822 : Upper (D 2) (R 2) [50,192,9,320,4] 13 := by
  apply FastRouting.sound _ _ [50,192,9,320,4] 13 (by decide) (choices 1) [16,128,256] r822 c822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u301
  · exact u302
  · exact u303

def b823 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 328 48 436 468 404 404), lower := (rows 51 194 13 328 48 32 64 128 256), losses := [] }

theorem u823 : Upper (D 2) (R 2) [50,192,9,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b823
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 13 328 144 308 372 436 308), lower := (rows 51 194 13 328 144 32 64 128 256), losses := [] }

theorem u824 : Upper (D 2) (R 2) [50,192,9,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b824
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m825_4 : Upper (D 2) (R 2) [50,192,9,320,256,4] 13 :=
  permutation_upper _ _ _ [50,192,9,320,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u303

theorem m825_16 : Upper (D 2) (R 2) [50,192,9,320,256,16] 13 :=
  permutation_upper _ _ _ [50,192,9,320,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u304

theorem m825_128 : Upper (D 2) (R 2) [50,192,9,320,256,128] 13 :=
  permutation_upper _ _ _ [50,192,9,320,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u305

def r825 : Route 9 := (fun mask => (mask,id))

def c825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u825 : Upper (D 2) (R 2) [50,192,9,320,256] 13 := by
  apply FastRouting.sound _ _ [50,192,9,320,256] 13 (by decide) (choices 1) [4,16,128] r825 c825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m825_4
  · exact m825_16
  · exact m825_128

def b826 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 104 17 420 452 388 388), lower := (rows 51 194 28 104 17 32 64 128 256), losses := [] }

theorem u826 : Upper (D 2) (R 2) [50,192,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b826
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 28 104 20 417 449 385 385), lower := (rows 51 194 28 104 20 32 64 128 256), losses := [] }

theorem u827 : Upper (D 2) (R 2) [50,192,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b827
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 28 104 144 293 325 389 261), lower := (rows 51 194 28 104 144 32 64 128 256), losses := [] }

theorem u828 : Upper (D 2) (R 2) [50,192,24,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b828
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r829 : Route 9 := (fun mask => (mask,id))

def c829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u829 : Upper (D 2) (R 2) [50,192,24,96,256] 13 := by
  apply FastRouting.sound _ _ [50,192,24,96,256] 13 (by decide) (choices 1) [1,4,128,256] r829 c829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u306
  · exact u307
  · exact u308
  · exact u309

def b830 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 28 265 20 480 480 480 480), lower := (rows 51 194 28 265 20 32 64 128 256), losses := [] }

theorem u830 : Upper (D 2) (R 2) [50,192,24,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b830
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 28 265 48 484 452 452 452), lower := (rows 51 194 28 265 48 32 64 128 256), losses := [] }

theorem u831 : Upper (D 2) (R 2) [50,192,24,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b831
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 28 265 80 420 484 420 420), lower := (rows 51 194 28 265 80 32 64 128 256), losses := [] }

theorem u832 : Upper (D 2) (R 2) [50,192,24,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b832
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 28 265 272 228 228 228 484), lower := (rows 51 194 28 265 272 32 64 128 256), losses := [] }

theorem u833 : Upper (D 2) (R 2) [50,192,24,257,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b833
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 268 17 480 480 480 480), lower := (rows 51 194 28 268 17 32 64 128 256), losses := [] }

theorem u834 : Upper (D 2) (R 2) [50,192,24,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b834
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 28 268 48 481 449 449 449), lower := (rows 51 194 28 268 48 32 64 128 256), losses := [] }

theorem u835 : Upper (D 2) (R 2) [50,192,24,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b835
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 28 268 80 417 481 417 417), lower := (rows 51 194 28 268 80 32 64 128 256), losses := [] }

theorem u836 : Upper (D 2) (R 2) [50,192,24,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b836
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 28 268 272 225 225 225 481), lower := (rows 51 194 28 268 272 32 64 128 256), losses := [] }

theorem u837 : Upper (D 2) (R 2) [50,192,24,260,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b837
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 296 17 484 452 452 452), lower := (rows 51 194 28 296 17 32 64 128 256), losses := [] }

theorem u838 : Upper (D 2) (R 2) [50,192,24,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b838
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 28 296 20 481 449 449 449), lower := (rows 51 194 28 296 20 32 64 128 256), losses := [] }

theorem u839 : Upper (D 2) (R 2) [50,192,24,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b839
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P02
