import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0058
import IrregularNine14P09C0059
import IrregularNine14P09C0060

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6960 : Route 9 := (fun mask => (mask,id))

def c6960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6960 : Upper (D 9) (R 9) [6,96,160,80,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384] 13 (by decide) (choices 1) [1,8,256] r6960 c6960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3494
  · exact u3495
  · exact u3496

def r6961 : Route 9 := (fun mask => (mask,id))

def c6961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6961 : Upper (D 9) (R 9) [6,96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257] 13 (by decide) (choices 1) [1,8,16,256] r6961 c6961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3497
  · exact u3498
  · exact u3499
  · exact u3500

def r6962 : Route 9 := (fun mask => (mask,id))

def c6962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6962 : Upper (D 9) (R 9) [6,96,160,192,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264] 13 (by decide) (choices 1) [1,16,256] r6962 c6962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3501
  · exact u3502
  · exact u3503

def b6963 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 16, targets := 192 },{ cop := 4, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 7 98 164 265 273 248 216 216 472), lower := (rows 7 98 164 265 273 32 64 128 256), losses := [] }

theorem u6963 : Upper (D 9) (R 9) [6,96,160,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6963 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6964 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 193 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6),(4,7)], upper := (rows 7 98 164 265 280 241 209 209 465), lower := (rows 7 98 164 265 280 32 64 128 256), losses := [] }

theorem u6964 : Upper (D 9) (R 9) [6,96,160,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6964 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6965 : Route 9 := (fun mask => (mask,id))

def c6965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6965 : Upper (D 9) (R 9) [6,96,160,257,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257,320] 13 (by decide) (choices 1) [1,8,16,128] r6965 c6965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3504
  · exact u3505
  · exact u3506
  · exact u3507

def b6966 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 7 98 164 280 280 225 193 193 449), lower := (rows 7 98 164 280 280 32 64 128 256), losses := [] }

theorem u6966 : Upper (D 9) (R 9) [6,96,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6966 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6967 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 164 280 336 169 201 137 393), lower := (rows 7 98 164 280 336 32 64 128 256), losses := [] }

theorem u6967 : Upper (D 9) (R 9) [6,96,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6967 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6968_16 : Upper (D 9) (R 9) [6,96,160,320,384,16] 13 :=
  permutation_upper _ _ _ [6,96,160,320,384,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3509

def r6968 : Route 9 := (fun mask => (mask,id))

def c6968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6968 : Upper (D 9) (R 9) [6,96,160,320,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320,384] 13 (by decide) (choices 1) [1,8,16] r6968 c6968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3508
  · exact u3509
  · exact m6968_16

def b6969 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 480 }], pairs := [(3,5),(3,6),(3,7),(3,8),(4,5)], upper := (rows 7 98 388 25 25 480 480 480 480), lower := (rows 7 98 388 25 25 32 64 128 256), losses := [] }

theorem u6969 : Upper (D 9) (R 9) [6,96,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6969 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6970 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 8, targets := 448 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(3,7),(3,8)], upper := (rows 7 98 388 25 49 488 456 456 456), lower := (rows 7 98 388 25 49 32 64 128 256), losses := [] }

theorem u6970 : Upper (D 9) (R 9) [6,96,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6970 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6971 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6971 : Upper (D 9) (R 9) [6,96,384,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,40] 13 (by decide) (choices 1) [1,64,128] r6971 c6971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3510
  · exact u3511
  · exact u3512

def b6972 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 385 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7),(4,8)], upper := (rows 7 98 388 25 112 425 457 393 393), lower := (rows 7 98 388 25 112 32 64 128 256), losses := [] }

theorem u6972 : Upper (D 9) (R 9) [6,96,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6972 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6973 : Route 9 := (fun mask => (mask,id))

def c6973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6973 : Upper (D 9) (R 9) [6,96,384,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,160] 13 (by decide) (choices 1) [1,8,64,256] r6973 c6973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3513
  · exact u3514
  · exact u3515
  · exact u3516

def r6974 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6974 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u6974 : Upper (D 9) (R 9) [6,96,384,33,65] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,65] 13 (by decide) (choices 1) [8,16,128] r6974 c6974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3517
  · exact u3518
  · exact u3519

def r6975 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6975 : Upper (D 9) (R 9) [6,96,384,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,72] 13 (by decide) (choices 1) [1,16,128] r6975 c6975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3520
  · exact u3521
  · exact u3522

def r6976 : Route 9 := (fun mask => (mask,id))

def c6976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u6976 : Upper (D 9) (R 9) [6,96,384,33,129] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,129] 13 (by decide) (choices 1) [8,16,64,256] r6976 c6976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3523
  · exact u3524
  · exact u3525
  · exact u3526

def r6977 : Route 9 := (fun mask => (mask,id))

def c6977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6977 : Upper (D 9) (R 9) [6,96,384,33,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,136] 13 (by decide) (choices 1) [1,16,64,256] r6977 c6977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3527
  · exact u3528
  · exact u3529
  · exact u3530

def r6978 : Route 9 := (fun mask => (mask,id))

def c6978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6978 : Upper (D 9) (R 9) [6,96,384,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,192] 13 (by decide) (choices 1) [1,8,16,256] r6978 c6978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3531
  · exact u3532
  · exact u3533
  · exact u3534

def b6979 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 7 98 388 41 400 121 89 217 345), lower := (rows 7 98 388 41 400 32 64 128 256), losses := [] }

theorem u6979 : Upper (D 9) (R 9) [6,96,384,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6979 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6980 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 385 }], pairs := [(3,0),(3,7),(3,8),(4,0),(4,7)], upper := (rows 7 98 388 56 88 417 449 385 385), lower := (rows 7 98 388 56 88 32 64 128 256), losses := [] }

theorem u6980 : Upper (D 9) (R 9) [6,96,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6980 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6981 : Route 9 := (fun mask => (mask,id))

def c6981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6981 : Upper (D 9) (R 9) [6,96,384,48,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,136] 13 (by decide) (choices 1) [1,64,256] r6981 c6981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3535
  · exact u3536
  · exact u3537

def r6982 : Route 9 := (fun mask => (mask,id))

def c6982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6982 : Upper (D 9) (R 9) [6,96,384,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192] 13 (by decide) (choices 1) [1,8,256] r6982 c6982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3538
  · exact u3539
  · exact u3540

def b6983 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 7 98 388 56 400 105 73 201 329), lower := (rows 7 98 388 56 400 32 64 128 256), losses := [] }

theorem u6983 : Upper (D 9) (R 9) [6,96,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6983 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6984 : Route 9 := (fun mask => (mask,id))

def c6984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6984 : Upper (D 9) (R 9) [6,96,384,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160,320] 13 (by decide) (choices 1) [1,8,16] r6984 c6984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3541
  · exact u3542
  · exact u3543

def b6985 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 28 41 208 480 448 448 448), lower := (rows 35 7 28 41 208 32 64 128 256), losses := [] }

theorem u6985 : Upper (D 9) (R 9) [34,5,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6985 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6986 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 28 73 112 416 448 384 384), lower := (rows 35 7 28 73 112 32 64 128 256), losses := [] }

theorem u6986 : Upper (D 9) (R 9) [34,5,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6986 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6987 : Route 9 := (fun mask => (mask,id))

def c6987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6987 : Upper (D 9) (R 9) [34,5,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,160] 13 (by decide) (choices 1) [64,128,256] r6987 c6987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3544
  · exact u3545
  · exact u3546

def r6988 : Route 9 := (fun mask => (mask,id))

def c6988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6988 : Upper (D 9) (R 9) [34,5,24,65,192] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,192] 13 (by decide) (choices 1) [128,256] r6988 c6988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3547
  · exact u3548

def r6989 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6989 : Upper (D 9) (R 9) [34,5,24,65,384] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,384] 13 (by decide) (choices 1) [64,128] r6989 c6989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3549
  · exact u3550

def r6990 : Route 9 := (fun mask => (mask,id))

def c6990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6990 : Upper (D 9) (R 9) [34,5,24,96,192] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,192] 13 (by decide) (choices 1) [1,128,256] r6990 c6990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3551
  · exact u3552
  · exact u3553

def r6991 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6991 : Upper (D 9) (R 9) [34,5,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,384] 13 (by decide) (choices 1) [1,64,128] r6991 c6991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3554
  · exact u3555
  · exact u3556

def b6992 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 20, targets := 289 }], pairs := [(2,0),(2,5),(2,8),(4,0),(4,5)], upper := (rows 35 7 28 200 208 289 353 417 289), lower := (rows 35 7 28 200 208 32 64 128 256), losses := [] }

theorem u6992 : Upper (D 9) (R 9) [34,5,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6992 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6993_256 : Upper (D 9) (R 9) [34,5,24,192,320,256] 13 :=
  permutation_upper _ _ _ [34,5,24,192,320,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3558

def r6993 : Route 9 := (fun mask => (mask,id))

def c6993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6993 : Upper (D 9) (R 9) [34,5,24,192,320] 13 := by
  apply FastRouting.sound _ _ [34,5,24,192,320] 13 (by decide) (choices 1) [1,128,256] r6993 c6993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3557
  · exact u3558
  · exact m6993_256

def b6994 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 76 25 112 416 448 384 384), lower := (rows 35 7 76 25 112 32 64 128 256), losses := [] }

theorem u6994 : Upper (D 9) (R 9) [34,5,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6994 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6995 : Route 9 := (fun mask => (mask,id))

def c6995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6995 : Upper (D 9) (R 9) [34,5,72,17,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,160] 13 (by decide) (choices 1) [64,128,256] r6995 c6995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3559
  · exact u3560
  · exact u3561

def r6996 : Route 9 := (fun mask => (mask,id))

def c6996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6996 : Upper (D 9) (R 9) [34,5,72,17,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,192] 13 (by decide) (choices 1) [128,256] r6996 c6996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3562
  · exact u3563

def r6997 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6997 : Upper (D 9) (R 9) [34,5,72,17,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,384] 13 (by decide) (choices 1) [64,128] r6997 c6997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3564
  · exact u3565

def b6998 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 428, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,5)], upper := (rows 35 7 76 56 81 416 448 384 384), lower := (rows 35 7 76 56 81 32 64 128 256), losses := [] }

theorem u6998 : Upper (D 9) (R 9) [34,5,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6999 : Route 9 := (fun mask => (mask,id))

def c6999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6999 : Upper (D 9) (R 9) [34,5,72,48,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48,129] 13 (by decide) (choices 1) [64,128,256] r6999 c6999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3566
  · exact u3567
  · exact u3568

def r7000 : Route 9 := (fun mask => (mask,id))

def c7000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7000 : Upper (D 9) (R 9) [34,5,72,48,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48,192] 13 (by decide) (choices 1) [1,128,256] r7000 c7000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3569
  · exact u3570
  · exact u3571

def r7001 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7001 : Upper (D 9) (R 9) [34,5,72,48,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48,384] 13 (by decide) (choices 1) [1,64,128] r7001 c7001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3572
  · exact u3573
  · exact u3574

def r7002 : Route 9 := (fun mask => (mask,id))

def c7002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7002 : Upper (D 9) (R 9) [34,5,72,129,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,96] 13 (by decide) (choices 1) [16,128,256] r7002 c7002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3575
  · exact u3576
  · exact u3577

def r7003 : Route 9 := (fun mask => (mask,id))

def c7003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7003 : Upper (D 9) (R 9) [34,5,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,160] 13 (by decide) (choices 1) [16,64,256] r7003 c7003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3578
  · exact u3579
  · exact u3580

def r7004 : Route 9 := (fun mask => (mask,id))

def c7004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7004 : Upper (D 9) (R 9) [34,5,72,129,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,192] 13 (by decide) (choices 1) [16,256] r7004 c7004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3581
  · exact u3582

def r7005 : Route 9 := (fun mask => (mask,id))

def c7005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7005 : Upper (D 9) (R 9) [34,5,72,129,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,288] 13 (by decide) (choices 1) [16,64,128,256] r7005 c7005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3583
  · exact u3584
  · exact u3585
  · exact u3586

def r7006 : Route 9 := (fun mask => (mask,id))

def c7006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7006 : Upper (D 9) (R 9) [34,5,72,129,320] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,320] 13 (by decide) (choices 1) [16,128,256] r7006 c7006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3587
  · exact u3588
  · exact u3589

def r7007 : Route 9 := (fun mask => (mask,id))

def c7007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7007 : Upper (D 9) (R 9) [34,5,72,129,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,384] 13 (by decide) (choices 1) [16,64,256] r7007 c7007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3590
  · exact u3591
  · exact u3592

def b7008 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 7 76 152 49 480 448 448 448), lower := (rows 35 7 76 152 49 32 64 128 256), losses := [] }

theorem u7008 : Upper (D 9) (R 9) [34,5,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7008 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7009 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,0),(3,6)], upper := (rows 35 7 76 152 81 416 480 416 416), lower := (rows 35 7 76 152 81 32 64 128 256), losses := [] }

theorem u7009 : Upper (D 9) (R 9) [34,5,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7009 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7010 : Route 9 := (fun mask => (mask,id))

def c7010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7010 : Upper (D 9) (R 9) [34,5,72,144,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,96] 13 (by decide) (choices 1) [1,128,256] r7010 c7010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3593
  · exact u3594
  · exact u3595

def b7011 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 35 7 76 152 145 352 352 480 352), lower := (rows 35 7 76 152 145 32 64 128 256), losses := [] }

theorem u7011 : Upper (D 9) (R 9) [34,5,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7011 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7012 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 7 76 152 176 353 321 449 321), lower := (rows 35 7 76 152 176 32 64 128 256), losses := [] }

theorem u7012 : Upper (D 9) (R 9) [34,5,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7012 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7013 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 289 }], pairs := [(2,0),(2,5),(2,8),(3,0),(3,5)], upper := (rows 35 7 76 152 208 289 353 417 289), lower := (rows 35 7 76 152 208 32 64 128 256), losses := [] }

theorem u7013 : Upper (D 9) (R 9) [34,5,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7014 : Route 9 := (fun mask => (mask,id))

def c7014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7014 : Upper (D 9) (R 9) [34,5,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,257] 13 (by decide) (choices 1) [64,128,256] r7014 c7014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3596
  · exact u3597
  · exact u3598

def r7015 : Route 9 := (fun mask => (mask,id))

def c7015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7015 : Upper (D 9) (R 9) [34,5,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,288] 13 (by decide) (choices 1) [1,64,128,256] r7015 c7015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3599
  · exact u3600
  · exact u3601
  · exact u3602

def r7016 : Route 9 := (fun mask => (mask,id))

def c7016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7016 : Upper (D 9) (R 9) [34,5,72,144,320] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,320] 13 (by decide) (choices 1) [1,128,256] r7016 c7016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3603
  · exact u3604
  · exact u3605

def b7017 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 7 76 152 400 353 353 481 353), lower := (rows 35 7 76 152 400 32 64 128 256), losses := [] }

theorem u7017 : Upper (D 9) (R 9) [34,5,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7018 : Route 9 := (fun mask => (mask,id))

def c7018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7018 : Upper (D 9) (R 9) [34,5,72,160,65] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,65] 13 (by decide) (choices 1) [16,128,256] r7018 c7018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3606
  · exact u3607
  · exact u3608

def r7019 : Route 9 := (fun mask => (mask,id))

def c7019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7019 : Upper (D 9) (R 9) [34,5,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,129] 13 (by decide) (choices 1) [16,64,256] r7019 c7019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3609
  · exact u3610
  · exact u3611

#print axioms u7019
end Delivery.IrregularNine14.P09
