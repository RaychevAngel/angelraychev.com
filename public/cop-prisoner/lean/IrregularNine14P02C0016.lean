import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0006

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 140 266 48 496 464 464 464), lower := (rows 113 7 140 266 48 32 64 128 256), losses := [] }

theorem u960 : Upper (D 2) (R 2) [112,5,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b960
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 113 7 140 266 144 368 368 496 368), lower := (rows 113 7 140 266 144 32 64 128 256), losses := [{ target := 7, region := (rows 17 2 4 10 16 49 81 0 273), good := (rows 369 367 12 266 369 32 64 0 256) }] }

theorem u961 : Upper (D 2) (R 2) [112,5,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b961
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m962_16 : Upper (D 2) (R 2) [112,5,136,258,256,16] 13 :=
  permutation_upper _ _ _ [112,5,136,258,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u377

theorem m962_64 : Upper (D 2) (R 2) [112,5,136,258,256,64] 13 :=
  permutation_upper _ _ _ [112,5,136,258,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u378

theorem m962_128 : Upper (D 2) (R 2) [112,5,136,258,256,128] 13 :=
  permutation_upper _ _ _ [112,5,136,258,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u379

def r962 : Route 9 := (fun mask => (mask,id))

def c962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u962 : Upper (D 2) (R 2) [112,5,136,258,256] 13 := by
  apply FastRouting.sound _ _ [112,5,136,258,256] 13 (by decide) (choices 1) [16,64,128] r962 c962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m962_16
  · exact m962_64
  · exact m962_128

def b963 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 140 280 18 480 480 480 480), lower := (rows 113 7 140 280 18 32 64 128 256), losses := [] }

theorem u963 : Upper (D 2) (R 2) [112,5,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b963
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 140 280 48 482 450 450 450), lower := (rows 113 7 140 280 48 32 64 128 256), losses := [] }

theorem u964 : Upper (D 2) (R 2) [112,5,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b964
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r965 : Route 9 := (fun mask => (mask,id))

def c965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u965 : Upper (D 2) (R 2) [112,5,136,272,128] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,128] 13 (by decide) (choices 1) [2,64,256] r965 c965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u380
  · exact u381
  · exact u382

def b966 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 7 140 280 272 226 226 226 482), lower := (rows 113 7 140 280 272 32 64 128 256), losses := [] }

theorem u966 : Upper (D 2) (R 2) [112,5,136,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b966
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 168 18 360 328 456 328), lower := (rows 113 7 148 168 18 32 64 128 256), losses := [] }

theorem u967 : Upper (D 2) (R 2) [112,5,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b967
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 7 148 168 24 354 322 450 322), lower := (rows 113 7 148 168 24 32 64 128 256), losses := [] }

theorem u968 : Upper (D 2) (R 2) [112,5,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b968
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 148 168 80 298 330 394 266), lower := (rows 113 7 148 168 80 32 64 128 256), losses := [] }

theorem u969 : Upper (D 2) (R 2) [112,5,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b969
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r970 : Route 9 := (fun mask => (mask,id))

def c970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u970 : Upper (D 2) (R 2) [112,5,144,160,256] 13 := by
  apply FastRouting.sound _ _ [112,5,144,160,256] 13 (by decide) (choices 1) [2,8,64,256] r970 c970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u383
  · exact u384
  · exact u385
  · exact u386

def b971 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 266 24 480 480 480 480), lower := (rows 113 7 148 266 24 32 64 128 256), losses := [] }

theorem u971 : Upper (D 2) (R 2) [112,5,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b971
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 148 266 48 488 456 456 456), lower := (rows 113 7 148 266 48 32 64 128 256), losses := [] }

theorem u972 : Upper (D 2) (R 2) [112,5,144,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b972
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 7 148 266 144 360 360 488 360), lower := (rows 113 7 148 266 144 32 64 128 256), losses := [] }

theorem u973 : Upper (D 2) (R 2) [112,5,144,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b973
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r974 : Route 9 := (fun mask => (mask,id))

def c974 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u974 : Upper (D 2) (R 2) [112,5,144,258,256] 13 := by
  apply FastRouting.sound _ _ [112,5,144,258,256] 13 (by decide) (choices 1) [8,64,128] r974 c974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u387
  · exact u388
  · exact u389

def b975 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 296 18 488 456 456 456), lower := (rows 113 7 148 296 18 32 64 128 256), losses := [] }

theorem u975 : Upper (D 2) (R 2) [112,5,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b975
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 148 296 24 482 450 450 450), lower := (rows 113 7 148 296 24 32 64 128 256), losses := [] }

theorem u976 : Upper (D 2) (R 2) [112,5,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b976
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 148 296 80 426 458 394 394), lower := (rows 113 7 148 296 80 32 64 128 256), losses := [] }

theorem u977 : Upper (D 2) (R 2) [112,5,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b977
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 7 148 296 144 362 330 458 330), lower := (rows 113 7 148 296 144 32 64 128 256), losses := [] }

theorem u978 : Upper (D 2) (R 2) [112,5,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b978
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r979 : Route 9 := (fun mask => (mask,id))

def c979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u979 : Upper (D 2) (R 2) [112,5,144,288,256] 13 := by
  apply FastRouting.sound _ _ [112,5,144,288,256] 13 (by decide) (choices 1) [2,8,64,128] r979 c979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u390
  · exact u391
  · exact u392
  · exact u393

def b980 : PairBound 9 := { available := 360, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 392 18 360 360 488 360), lower := (rows 113 7 148 392 18 32 64 128 256), losses := [] }

theorem u980 : Upper (D 2) (R 2) [112,5,144,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b980
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 7 148 392 24 354 354 482 354), lower := (rows 113 7 148 392 24 32 64 128 256), losses := [] }

theorem u981 : Upper (D 2) (R 2) [112,5,144,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b981
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 148 392 48 362 330 458 330), lower := (rows 113 7 148 392 48 32 64 128 256), losses := [] }

theorem u982 : Upper (D 2) (R 2) [112,5,144,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b982
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 7 148 392 272 106 106 234 362), lower := (rows 113 7 148 392 272 32 64 128 256), losses := [] }

theorem u983 : Upper (D 2) (R 2) [112,5,144,384,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b983
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 388 26 24 480 480 480 480), lower := (rows 113 7 388 26 24 32 64 128 256), losses := [] }

theorem u984 : Upper (D 2) (R 2) [112,5,384,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b984
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 388 26 48 488 456 456 456), lower := (rows 113 7 388 26 48 32 64 128 256), losses := [] }

theorem u985 : Upper (D 2) (R 2) [112,5,384,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b985
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 484, targets := 16 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(2,4)], upper := (rows 113 7 388 26 144 360 360 488 360), lower := (rows 113 7 388 26 144 32 64 128 256), losses := [] }

theorem u986 : Upper (D 2) (R 2) [112,5,384,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b986
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 388 138 24 368 368 496 368), lower := (rows 113 7 388 138 24 32 64 128 256), losses := [] }

theorem u987 : Upper (D 2) (R 2) [112,5,384,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b987
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 388 138 48 376 344 472 344), lower := (rows 113 7 388 138 48 32 64 128 256), losses := [] }

theorem u988 : Upper (D 2) (R 2) [112,5,384,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b988
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m989_8 : Upper (D 2) (R 2) [112,5,384,130,256,8] 13 :=
  permutation_upper _ _ _ [112,5,384,130,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u394

theorem m989_16 : Upper (D 2) (R 2) [112,5,384,130,256,16] 13 :=
  permutation_upper _ _ _ [112,5,384,130,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u395

theorem m989_64 : Upper (D 2) (R 2) [112,5,384,130,256,64] 13 :=
  permutation_upper _ _ _ [112,5,384,130,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u396

def r989 : Route 9 := (fun mask => (mask,id))

def c989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u989 : Upper (D 2) (R 2) [112,5,384,130,256] 13 := by
  apply FastRouting.sound _ _ [112,5,384,130,256] 13 (by decide) (choices 1) [8,16,64] r989 c989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m989_8
  · exact m989_16
  · exact m989_64

def b990 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 356, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 388 152 18 360 360 488 360), lower := (rows 113 7 388 152 18 32 64 128 256), losses := [] }

theorem u990 : Upper (D 2) (R 2) [112,5,384,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b990
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 388 152 24 354 354 482 354), lower := (rows 113 7 388 152 24 32 64 128 256), losses := [] }

theorem u991 : Upper (D 2) (R 2) [112,5,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b991
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 388 152 48 362 330 458 330), lower := (rows 113 7 388 152 48 32 64 128 256), losses := [] }

theorem u992 : Upper (D 2) (R 2) [112,5,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b992
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 113 7 388 152 272 106 106 234 362), lower := (rows 113 7 388 152 272 32 64 128 256), losses := [] }

theorem u993 : Upper (D 2) (R 2) [112,5,384,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b993
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 22 137 48 480 448 448 448), lower := (rows 113 14 22 137 48 32 64 128 256), losses := [] }

theorem u994 : Upper (D 2) (R 2) [112,12,18,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b994
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 22, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 14 22 137 144 352 352 480 352), lower := (rows 113 14 22 137 144 32 64 128 256), losses := [] }

theorem u995 : Upper (D 2) (R 2) [112,12,18,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b995
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r996 : Route 9 := (fun mask => (mask,id))

def c996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u996 : Upper (D 2) (R 2) [112,12,18,129,256] 13 := by
  apply FastRouting.sound _ _ [112,12,18,129,256] 13 (by decide) (choices 1) [64,128,256] r996 c996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u397
  · exact u398
  · exact u399

def b997 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 22 168 17 480 448 448 448), lower := (rows 113 14 22 168 17 32 64 128 256), losses := [] }

theorem u997 : Upper (D 2) (R 2) [112,12,18,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b997
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 22 168 80 417 449 385 385), lower := (rows 113 14 22 168 80 32 64 128 256), losses := [] }

theorem u998 : Upper (D 2) (R 2) [112,12,18,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b998
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 14 22 168 144 353 321 449 321), lower := (rows 113 14 22 168 144 32 64 128 256), losses := [] }

theorem u999 : Upper (D 2) (R 2) [112,12,18,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b999
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1000 : Route 9 := (fun mask => (mask,id))

def c1000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1000 : Upper (D 2) (R 2) [112,12,18,160,256] 13 := by
  apply FastRouting.sound _ _ [112,12,18,160,256] 13 (by decide) (choices 1) [1,64,128,256] r1000 c1000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u400
  · exact u401
  · exact u402
  · exact u403

def b1001 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 22 392 17 480 480 480 480), lower := (rows 113 14 22 392 17 32 64 128 256), losses := [] }

theorem u1001 : Upper (D 2) (R 2) [112,12,18,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1001
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 22 392 48 481 449 449 449), lower := (rows 113 14 22 392 48 32 64 128 256), losses := [] }

theorem u1002 : Upper (D 2) (R 2) [112,12,18,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1002
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 22, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 14 22 392 144 353 353 481 353), lower := (rows 113 14 22 392 144 32 64 128 256), losses := [] }

theorem u1003 : Upper (D 2) (R 2) [112,12,18,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1003
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 152 18 352 352 480 352), lower := (rows 113 14 133 152 18 32 64 128 256), losses := [] }

theorem u1004 : Upper (D 2) (R 2) [112,12,129,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1004
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 133 152 48 354 322 450 322), lower := (rows 113 14 133 152 48 32 64 128 256), losses := [] }

theorem u1005 : Upper (D 2) (R 2) [112,12,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1005
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1006 : Route 9 := (fun mask => (mask,id))

def c1006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1006 : Upper (D 2) (R 2) [112,12,129,144,256] 13 := by
  apply FastRouting.sound _ _ [112,12,129,144,256] 13 (by decide) (choices 1) [2,64,256] r1006 c1006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u404
  · exact u405
  · exact u406

def b1007 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 133 266 48 496 464 464 464), lower := (rows 113 14 133 266 48 32 64 128 256), losses := [] }

theorem u1007 : Upper (D 2) (R 2) [112,12,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1007
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 14 133 266 144 368 368 496 368), lower := (rows 113 14 133 266 144 32 64 128 256), losses := [{ target := 7, region := (rows 17 6 4 12 16 49 81 0 273), good := (rows 369 14 367 266 369 32 64 0 256) }] }

theorem u1008 : Upper (D 2) (R 2) [112,12,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1008
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 229, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 113 14 133 266 272 240 240 240 496), lower := (rows 113 14 133 266 272 32 64 128 256), losses := [] }

theorem u1009 : Upper (D 2) (R 2) [112,12,129,258,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1009
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 388, targets := 16 }], pairs := [(2,4)], upper := (rows 113 14 133 280 18 480 480 480 480), lower := (rows 113 14 133 280 18 32 64 128 256), losses := [] }

theorem u1010 : Upper (D 2) (R 2) [112,12,129,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1010
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 133 280 48 482 450 450 450), lower := (rows 113 14 133 280 48 32 64 128 256), losses := [] }

theorem u1011 : Upper (D 2) (R 2) [112,12,129,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1011
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1012 : Route 9 := (fun mask => (mask,id))

def c1012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1012 : Upper (D 2) (R 2) [112,12,129,272,128] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,128] 13 (by decide) (choices 1) [2,64,256] r1012 c1012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u407
  · exact u408
  · exact u409

def b1013 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 14 133 280 272 226 226 226 482), lower := (rows 113 14 133 280 272 32 64 128 256), losses := [] }

theorem u1013 : Upper (D 2) (R 2) [112,12,129,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1013
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 133 392 18 368 368 496 368), lower := (rows 113 14 133 392 18 32 64 128 256), losses := [] }

theorem u1014 : Upper (D 2) (R 2) [112,12,129,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1014
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 133 392 48 370 338 466 338), lower := (rows 113 14 133 392 48 32 64 128 256), losses := [] }

theorem u1015 : Upper (D 2) (R 2) [112,12,129,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1015
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1016_2 : Upper (D 2) (R 2) [112,12,129,384,256,2] 13 :=
  permutation_upper _ _ _ [112,12,129,384,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u410

theorem m1016_16 : Upper (D 2) (R 2) [112,12,129,384,256,16] 13 :=
  permutation_upper _ _ _ [112,12,129,384,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u411

theorem m1016_64 : Upper (D 2) (R 2) [112,12,129,384,256,64] 13 :=
  permutation_upper _ _ _ [112,12,129,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u412

def r1016 : Route 9 := (fun mask => (mask,id))

def c1016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1016 : Upper (D 2) (R 2) [112,12,129,384,256] 13 := by
  apply FastRouting.sound _ _ [112,12,129,384,256] 13 (by decide) (choices 1) [2,16,64] r1016 c1016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1016_2
  · exact m1016_16
  · exact m1016_64

def b1017 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 230, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 134 280 17 480 480 480 480), lower := (rows 113 14 134 280 17 32 64 128 256), losses := [] }

theorem u1017 : Upper (D 2) (R 2) [112,12,130,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1017
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 134 280 48 481 449 449 449), lower := (rows 113 14 134 280 48 32 64 128 256), losses := [] }

theorem u1018 : Upper (D 2) (R 2) [112,12,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1018
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 113 14 134 280 144 353 353 481 353), lower := (rows 113 14 134 280 144 32 64 128 256), losses := [] }

theorem u1019 : Upper (D 2) (R 2) [112,12,130,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1019
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P02
