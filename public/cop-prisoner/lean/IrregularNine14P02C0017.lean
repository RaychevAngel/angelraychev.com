import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0006
import IrregularNine14P02C0007

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 14 134 280 272 225 225 225 481), lower := (rows 113 14 134 280 272 32 64 128 256), losses := [] }

theorem u1020 : Upper (D 2) (R 2) [112,12,130,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1020
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 148 168 17 354 322 450 322), lower := (rows 113 14 148 168 17 32 64 128 256), losses := [] }

theorem u1021 : Upper (D 2) (R 2) [112,12,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1021
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 168 18 353 321 449 321), lower := (rows 113 14 148 168 18 32 64 128 256), losses := [] }

theorem u1022 : Upper (D 2) (R 2) [112,12,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1022
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 148 168 80 291 323 387 259), lower := (rows 113 14 148 168 80 32 64 128 256), losses := [] }

theorem u1023 : Upper (D 2) (R 2) [112,12,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1023
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1024_1 : Upper (D 2) (R 2) [112,12,144,160,256,1] 13 :=
  permutation_upper _ _ _ [112,12,144,160,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u413

theorem m1024_2 : Upper (D 2) (R 2) [112,12,144,160,256,2] 13 :=
  permutation_upper _ _ _ [112,12,144,160,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u414

theorem m1024_64 : Upper (D 2) (R 2) [112,12,144,160,256,64] 13 :=
  permutation_upper _ _ _ [112,12,144,160,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u415

def r1024 : Route 9 := (fun mask => (mask,id))

def c1024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1024 : Upper (D 2) (R 2) [112,12,144,160,256] 13 := by
  apply FastRouting.sound _ _ [112,12,144,160,256] 13 (by decide) (choices 1) [1,2,64,256] r1024 c1024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m1024_1
  · exact m1024_2
  · exact m1024_64
  · exact u416

def b1025 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 148 296 17 482 450 450 450), lower := (rows 113 14 148 296 17 32 64 128 256), losses := [] }

theorem u1025 : Upper (D 2) (R 2) [112,12,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1025
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 148 296 18 481 449 449 449), lower := (rows 113 14 148 296 18 32 64 128 256), losses := [] }

theorem u1026 : Upper (D 2) (R 2) [112,12,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1026
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 148 296 80 419 451 387 387), lower := (rows 113 14 148 296 80 32 64 128 256), losses := [] }

theorem u1027 : Upper (D 2) (R 2) [112,12,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1027
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 14 148 296 144 355 323 451 323), lower := (rows 113 14 148 296 144 32 64 128 256), losses := [] }

theorem u1028 : Upper (D 2) (R 2) [112,12,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1028
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1029_1 : Upper (D 2) (R 2) [112,12,144,288,256,1] 13 :=
  permutation_upper _ _ _ [112,12,144,288,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u417

theorem m1029_2 : Upper (D 2) (R 2) [112,12,144,288,256,2] 13 :=
  permutation_upper _ _ _ [112,12,144,288,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u418

theorem m1029_64 : Upper (D 2) (R 2) [112,12,144,288,256,64] 13 :=
  permutation_upper _ _ _ [112,12,144,288,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u419

def r1029 : Route 9 := (fun mask => (mask,id))

def c1029 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1029 : Upper (D 2) (R 2) [112,12,144,288,256] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288,256] 13 (by decide) (choices 1) [1,2,64,128] r1029 c1029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m1029_1
  · exact m1029_2
  · exact m1029_64
  · exact u420

def b1030 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 148 392 17 354 354 482 354), lower := (rows 113 14 148 392 17 32 64 128 256), losses := [] }

theorem u1030 : Upper (D 2) (R 2) [112,12,144,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1030
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 392 18 353 353 481 353), lower := (rows 113 14 148 392 18 32 64 128 256), losses := [] }

theorem u1031 : Upper (D 2) (R 2) [112,12,144,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1031
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 148 392 48 355 323 451 323), lower := (rows 113 14 148 392 48 32 64 128 256), losses := [] }

theorem u1032 : Upper (D 2) (R 2) [112,12,144,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1032
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 22, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 14 148 392 272 99 99 227 355), lower := (rows 113 14 148 392 272 32 64 128 256), losses := [] }

theorem u1033 : Upper (D 2) (R 2) [112,12,144,384,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1033
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 137 18 480 448 448 448), lower := (rows 113 22 44 137 18 32 64 128 256), losses := [] }

theorem u1034 : Upper (D 2) (R 2) [112,20,40,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1034
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 44 137 80 418 450 386 386), lower := (rows 113 22 44 137 80 32 64 128 256), losses := [] }

theorem u1035 : Upper (D 2) (R 2) [112,20,40,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1035
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 353, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5)], upper := (rows 113 22 44 137 144 354 322 450 322), lower := (rows 113 22 44 137 144 32 64 128 256), losses := [] }

theorem u1036 : Upper (D 2) (R 2) [112,20,40,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1036
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1037 : Route 9 := (fun mask => (mask,id))

def c1037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1037 : Upper (D 2) (R 2) [112,20,40,129,256] 13 := by
  apply FastRouting.sound _ _ [112,20,40,129,256] 13 (by decide) (choices 1) [2,64,128,256] r1037 c1037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u421
  · exact u422
  · exact u423
  · exact u424

def b1038 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 138 17 480 448 448 448), lower := (rows 113 22 44 138 17 32 64 128 256), losses := [] }

theorem u1038 : Upper (D 2) (R 2) [112,20,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1038
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 44 138 80 417 449 385 385), lower := (rows 113 22 44 138 80 32 64 128 256), losses := [] }

theorem u1039 : Upper (D 2) (R 2) [112,20,40,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1039
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,5)], upper := (rows 113 22 44 138 144 353 321 449 321), lower := (rows 113 22 44 138 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 153 0 65 129 257), good := (rows 465 22 30 154 144 0 64 144 256) }] }

theorem u1040 : Upper (D 2) (R 2) [112,20,40,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1040
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1041 : Route 9 := (fun mask => (mask,id))

def c1041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1041 : Upper (D 2) (R 2) [112,20,40,130,256] 13 := by
  apply FastRouting.sound _ _ [112,20,40,130,256] 13 (by decide) (choices 1) [1,64,128,256] r1041 c1041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u425
  · exact u426
  · exact u427
  · exact u428

def b1042 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 200 17 418 450 386 386), lower := (rows 113 22 44 200 17 32 64 128 256), losses := [] }

theorem u1042 : Upper (D 2) (R 2) [112,20,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1042
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 200 18 417 449 385 385), lower := (rows 113 22 44 200 18 32 64 128 256), losses := [] }

theorem u1043 : Upper (D 2) (R 2) [112,20,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1043
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,5)], upper := (rows 113 22 44 200 144 291 323 387 259), lower := (rows 113 22 44 200 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 152 0 64 128 256), good := (rows 81 22 30 216 144 0 64 144 256) }] }

theorem u1044 : Upper (D 2) (R 2) [112,20,40,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1044
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1045 : Route 9 := (fun mask => (mask,id))

def c1045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1045 : Upper (D 2) (R 2) [112,20,40,192,256] 13 := by
  apply FastRouting.sound _ _ [112,20,40,192,256] 13 (by decide) (choices 1) [1,2,128,256] r1045 c1045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u429
  · exact u430
  · exact u431
  · exact u432

def b1046 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 392 17 482 450 450 450), lower := (rows 113 22 44 392 17 32 64 128 256), losses := [] }

theorem u1046 : Upper (D 2) (R 2) [112,20,40,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1046
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 392 18 481 449 449 449), lower := (rows 113 22 44 392 18 32 64 128 256), losses := [] }

theorem u1047 : Upper (D 2) (R 2) [112,20,40,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1047
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 44 392 80 419 451 387 387), lower := (rows 113 22 44 392 80 32 64 128 256), losses := [] }

theorem u1048 : Upper (D 2) (R 2) [112,20,40,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1048
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,5)], upper := (rows 113 22 44 392 144 355 323 451 323), lower := (rows 113 22 44 392 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 152 0 64 128 256), good := (rows 81 22 30 408 144 0 64 144 256) }] }

theorem u1049 : Upper (D 2) (R 2) [112,20,40,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1049
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 168 18 360 328 456 328), lower := (rows 113 22 133 168 18 32 64 128 256), losses := [] }

theorem u1050 : Upper (D 2) (R 2) [112,20,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1050
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 168 24 354 322 450 322), lower := (rows 113 22 133 168 24 32 64 128 256), losses := [] }

theorem u1051 : Upper (D 2) (R 2) [112,20,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1051
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 168 80 298 330 394 266), lower := (rows 113 22 133 168 80 32 64 128 256), losses := [] }

theorem u1052 : Upper (D 2) (R 2) [112,20,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1052
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1053 : Route 9 := (fun mask => (mask,id))

def c1053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1053 : Upper (D 2) (R 2) [112,20,129,160,256] 13 := by
  apply FastRouting.sound _ _ [112,20,129,160,256] 13 (by decide) (choices 1) [2,8,64,256] r1053 c1053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u433
  · exact u434
  · exact u435
  · exact u436

def b1054 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 388, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 133 266 24 480 480 480 480), lower := (rows 113 22 133 266 24 32 64 128 256), losses := [] }

theorem u1054 : Upper (D 2) (R 2) [112,20,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1054
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 133 266 48 488 456 456 456), lower := (rows 113 22 133 266 48 32 64 128 256), losses := [] }

theorem u1055 : Upper (D 2) (R 2) [112,20,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1055
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 133 266 144 360 360 488 360), lower := (rows 113 22 133 266 144 32 64 128 256), losses := [] }

theorem u1056 : Upper (D 2) (R 2) [112,20,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1056
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1057 : Route 9 := (fun mask => (mask,id))

def c1057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1057 : Upper (D 2) (R 2) [112,20,129,258,256] 13 := by
  apply FastRouting.sound _ _ [112,20,129,258,256] 13 (by decide) (choices 1) [8,64,128] r1057 c1057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u437
  · exact u438
  · exact u439

def b1058 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 296 18 488 456 456 456), lower := (rows 113 22 133 296 18 32 64 128 256), losses := [] }

theorem u1058 : Upper (D 2) (R 2) [112,20,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1058
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 296 24 482 450 450 450), lower := (rows 113 22 133 296 24 32 64 128 256), losses := [] }

theorem u1059 : Upper (D 2) (R 2) [112,20,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1059
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 296 80 426 458 394 394), lower := (rows 113 22 133 296 80 32 64 128 256), losses := [] }

theorem u1060 : Upper (D 2) (R 2) [112,20,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1060
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 133 296 144 362 330 458 330), lower := (rows 113 22 133 296 144 32 64 128 256), losses := [] }

theorem u1061 : Upper (D 2) (R 2) [112,20,129,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1061
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1062 : Route 9 := (fun mask => (mask,id))

def c1062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1062 : Upper (D 2) (R 2) [112,20,129,288,256] 13 := by
  apply FastRouting.sound _ _ [112,20,129,288,256] 13 (by decide) (choices 1) [2,8,64,128] r1062 c1062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u440
  · exact u441
  · exact u442
  · exact u443

def b1063 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 392 18 360 360 488 360), lower := (rows 113 22 133 392 18 32 64 128 256), losses := [] }

theorem u1063 : Upper (D 2) (R 2) [112,20,129,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1063
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 133 392 24 354 354 482 354), lower := (rows 113 22 133 392 24 32 64 128 256), losses := [] }

theorem u1064 : Upper (D 2) (R 2) [112,20,129,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1064
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 133 392 48 362 330 458 330), lower := (rows 113 22 133 392 48 32 64 128 256), losses := [] }

theorem u1065 : Upper (D 2) (R 2) [112,20,129,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1065
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1066 : Route 9 := (fun mask => (mask,id))

def c1066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1066 : Upper (D 2) (R 2) [112,20,129,384,256] 13 := by
  apply FastRouting.sound _ _ [112,20,129,384,256] 13 (by decide) (choices 1) [2,8,64] r1066 c1066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u444
  · exact u445
  · exact u446

def b1067 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 265 24 480 480 480 480), lower := (rows 113 22 134 265 24 32 64 128 256), losses := [] }

theorem u1067 : Upper (D 2) (R 2) [112,20,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1067
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 134 265 48 488 456 456 456), lower := (rows 113 22 134 265 48 32 64 128 256), losses := [] }

theorem u1068 : Upper (D 2) (R 2) [112,20,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1068
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 6, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 134 265 144 360 360 488 360), lower := (rows 113 22 134 265 144 32 64 128 256), losses := [] }

theorem u1069 : Upper (D 2) (R 2) [112,20,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1069
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1070 : Route 9 := (fun mask => (mask,id))

def c1070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1070 : Upper (D 2) (R 2) [112,20,130,257,256] 13 := by
  apply FastRouting.sound _ _ [112,20,130,257,256] 13 (by decide) (choices 1) [8,64,128] r1070 c1070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u447
  · exact u448
  · exact u449

def b1071 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 134 296 17 488 456 456 456), lower := (rows 113 22 134 296 17 32 64 128 256), losses := [] }

theorem u1071 : Upper (D 2) (R 2) [112,20,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1071
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 296 24 481 449 449 449), lower := (rows 113 22 134 296 24 32 64 128 256), losses := [] }

theorem u1072 : Upper (D 2) (R 2) [112,20,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1072
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 134 296 80 425 457 393 393), lower := (rows 113 22 134 296 80 32 64 128 256), losses := [] }

theorem u1073 : Upper (D 2) (R 2) [112,20,130,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1073
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 6, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 134 296 144 361 329 457 329), lower := (rows 113 22 134 296 144 32 64 128 256), losses := [] }

theorem u1074 : Upper (D 2) (R 2) [112,20,130,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1074
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1075 : Route 9 := (fun mask => (mask,id))

def c1075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1075 : Upper (D 2) (R 2) [112,20,130,288,256] 13 := by
  apply FastRouting.sound _ _ [112,20,130,288,256] 13 (by decide) (choices 1) [1,8,64,128] r1075 c1075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u450
  · exact u451
  · exact u452
  · exact u453

def b1076 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 265 18 480 480 480 480), lower := (rows 113 22 140 265 18 32 64 128 256), losses := [] }

theorem u1076 : Upper (D 2) (R 2) [112,20,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1076
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 140 265 48 482 450 450 450), lower := (rows 113 22 140 265 48 32 64 128 256), losses := [] }

theorem u1077 : Upper (D 2) (R 2) [112,20,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1077
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 140 265 144 354 354 482 354), lower := (rows 113 22 140 265 144 32 64 128 256), losses := [] }

theorem u1078 : Upper (D 2) (R 2) [112,20,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1078
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 225, targets := 256 }], pairs := [(0,8),(1,5)], upper := (rows 113 22 140 265 272 226 226 226 482), lower := (rows 113 22 140 265 272 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 280 0 64 128 256), good := (rows 81 22 158 281 272 0 64 128 272) }] }

theorem u1079 : Upper (D 2) (R 2) [112,20,136,257,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1079
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P02
