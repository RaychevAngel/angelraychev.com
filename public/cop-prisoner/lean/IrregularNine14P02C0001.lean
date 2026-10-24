import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0000

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 14 152 272 160 320 224 352), lower := (rows 113 7 14 152 272 160 320 128 256), losses := [] }

theorem u60 : Upper (D 2) (R 2) [112,5,10,144,256,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b60
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 264, targets := 128 }], pairs := [(3,7)], upper := (rows 113 7 140 280 144 34 320 224 352), lower := (rows 113 7 140 280 144 34 320 128 256), losses := [] }

theorem u61 : Upper (D 2) (R 2) [112,5,136,272,128,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b61
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 140 280 144 96 320 162 290), lower := (rows 113 7 140 280 144 96 320 128 256), losses := [] }

theorem u62 : Upper (D 2) (R 2) [112,5,136,272,128,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b62
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 7 148 266 272 40 192 224 352), lower := (rows 113 7 148 266 272 40 192 128 256), losses := [] }

theorem u63 : Upper (D 2) (R 2) [112,5,144,258,256,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b63
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 148 266 272 96 192 168 296), lower := (rows 113 7 148 266 272 96 192 128 256), losses := [] }

theorem u64 : Upper (D 2) (R 2) [112,5,144,258,256,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b64
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8)], upper := (rows 113 7 148 296 272 160 66 200 328), lower := (rows 113 7 148 296 272 160 66 128 256), losses := [] }

theorem u65 : Upper (D 2) (R 2) [112,5,144,288,256,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b65
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 148 296 272 160 72 194 322), lower := (rows 113 7 148 296 272 160 72 128 256), losses := [] }

theorem u66 : Upper (D 2) (R 2) [112,5,144,288,256,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b66
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 132, targets := 16 }], pairs := [(2,4)], upper := (rows 113 14 133 280 144 34 320 224 352), lower := (rows 113 14 133 280 144 34 320 128 256), losses := [] }

theorem u67 : Upper (D 2) (R 2) [112,12,129,272,128,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b67
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 133 280 144 96 320 162 290), lower := (rows 113 14 133 280 144 96 320 128 256), losses := [] }

theorem u68 : Upper (D 2) (R 2) [112,12,129,272,128,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b68
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8)], upper := (rows 113 14 148 296 272 160 65 194 322), lower := (rows 113 14 148 296 272 160 65 128 256), losses := [] }

theorem u69 : Upper (D 2) (R 2) [112,12,144,288,256,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b69
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 264, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 148 296 272 160 66 193 321), lower := (rows 113 14 148 296 272 160 66 128 256), losses := [] }

theorem u70 : Upper (D 2) (R 2) [112,12,144,288,256,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b70
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 133 266 272 40 192 224 352), lower := (rows 113 22 133 266 272 40 192 128 256), losses := [] }

theorem u71 : Upper (D 2) (R 2) [112,20,129,258,256,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b71
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 266 272 96 192 168 296), lower := (rows 113 22 133 266 272 96 192 128 256), losses := [] }

theorem u72 : Upper (D 2) (R 2) [112,20,129,258,256,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b72
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 133 296 272 160 66 200 328), lower := (rows 113 22 133 296 272 160 66 128 256), losses := [] }

theorem u73 : Upper (D 2) (R 2) [112,20,129,288,256,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b73
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 296 272 160 72 194 322), lower := (rows 113 22 133 296 272 160 72 128 256), losses := [] }

theorem u74 : Upper (D 2) (R 2) [112,20,129,288,256,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b74
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 131 148 268 272 34 72 224 352), lower := (rows 113 131 148 268 272 34 72 128 256), losses := [] }

theorem u75 : Upper (D 2) (R 2) [112,129,144,260,256,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b75
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 268 272 34 96 200 328), lower := (rows 113 131 148 268 272 34 96 128 256), losses := [] }

theorem u76 : Upper (D 2) (R 2) [112,129,144,260,256,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b76
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 488, targets := 16 },{ cop := 5, region := 404, targets := 64 }], pairs := [(2,6),(3,4)], upper := (rows 15 19 52 200 272 96 480 416 416), lower := (rows 15 19 52 200 272 96 64 128 256), losses := [] }

theorem u77 : Upper (D 2) (R 2) [14,17,48,192,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b77
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 203, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 15 19 52 200 272 288 224 224 480), lower := (rows 15 19 52 200 272 288 64 128 256), losses := [] }

theorem u78 : Upper (D 2) (R 2) [14,17,48,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b78
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 460, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 15 19 100 168 272 48 448 448 448), lower := (rows 15 19 100 168 272 48 64 128 256), losses := [] }

theorem u79 : Upper (D 2) (R 2) [14,17,96,160,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b79
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 15 19 100 168 272 96 464 400 400), lower := (rows 15 19 100 168 272 96 64 128 256), losses := [] }

theorem u80 : Upper (D 2) (R 2) [14,17,96,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b80
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r81 : Route 9 := (fun mask => (mask,id))

def c81 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u81 : Upper (D 2) (R 2) [14,17,96,160,256,256] 13 := by
  apply FastRouting.sound _ _ [14,17,96,160,256,256] 13 (by decide) (choices 1) [16,128] r81 c81
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b82 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 392 144 33 352 480 352), lower := (rows 15 50 84 392 144 33 64 128 256), losses := [] }

theorem u82 : Upper (D 2) (R 2) [14,48,80,384,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b82
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 34, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 15 50 84 392 144 96 353 417 289), lower := (rows 15 50 84 392 144 96 64 128 256), losses := [] }

theorem u83 : Upper (D 2) (R 2) [14,48,80,384,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b83
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 488, targets := 16 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6),(3,4)], upper := (rows 15 50 84 392 144 288 97 225 353), lower := (rows 15 50 84 392 144 288 64 128 256), losses := [] }

theorem u84 : Upper (D 2) (R 2) [14,48,80,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b84
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 11 100 56 144 96 448 384 384), lower := (rows 23 11 100 56 144 96 64 128 256), losses := [] }

theorem u85 : Upper (D 2) (R 2) [22,9,96,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b85
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 11 100 56 144 160 320 448 320), lower := (rows 23 11 100 56 144 160 64 128 256), losses := [] }

theorem u86 : Upper (D 2) (R 2) [22,9,96,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b86
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r87 : Route 9 := (fun mask => (mask,id))

def c87 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u87 : Upper (D 2) (R 2) [22,9,96,48,128,256] 13 := by
  apply FastRouting.sound _ _ [22,9,96,48,128,256] 13 (by decide) (choices 1) [128,256] r87 c87
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b88 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 11 100 152 272 96 480 416 416), lower := (rows 23 11 100 152 272 96 64 128 256), losses := [] }

theorem u88 : Upper (D 2) (R 2) [22,9,96,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b88
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 484, targets := 16 },{ cop := 5, region := 324, targets := 128 }], pairs := [(2,4),(2,7)], upper := (rows 23 11 100 152 272 160 352 480 352), lower := (rows 23 11 100 152 272 160 64 128 256), losses := [] }

theorem u89 : Upper (D 2) (R 2) [22,9,96,144,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b89
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 484, targets := 16 },{ cop := 5, region := 196, targets := 256 }], pairs := [(2,4),(2,8)], upper := (rows 23 11 100 152 272 288 224 224 480), lower := (rows 23 11 100 152 272 288 64 128 256), losses := [] }

theorem u90 : Upper (D 2) (R 2) [22,9,96,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b90
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 40, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 23 11 100 168 144 48 320 448 320), lower := (rows 23 11 100 168 144 48 64 128 256), losses := [] }

theorem u91 : Upper (D 2) (R 2) [22,9,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b91
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 11 100 168 144 96 336 400 272), lower := (rows 23 11 100 168 144 96 64 128 256), losses := [] }

theorem u92 : Upper (D 2) (R 2) [22,9,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b92
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r93 : Route 9 := (fun mask => (mask,id))

def c93 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u93 : Upper (D 2) (R 2) [22,9,96,160,128,256] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160,128,256] 13 (by decide) (choices 1) [16,256] r93 c93
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b94 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 460, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 11 100 168 272 48 448 448 448), lower := (rows 23 11 100 168 272 48 64 128 256), losses := [] }

theorem u94 : Upper (D 2) (R 2) [22,9,96,160,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b94
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 11 100 168 272 96 464 400 400), lower := (rows 23 11 100 168 272 96 64 128 256), losses := [] }

theorem u95 : Upper (D 2) (R 2) [22,9,96,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b95
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 11 100 168 272 160 336 464 336), lower := (rows 23 11 100 168 272 160 64 128 256), losses := [] }

theorem u96 : Upper (D 2) (R 2) [22,9,96,160,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b96
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r97 : Route 9 := (fun mask => (mask,id))

def c97 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u97 : Upper (D 2) (R 2) [22,9,96,160,256,256] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160,256,256] 13 (by decide) (choices 1) [16,128] r97 c97
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b98 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 460, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 11 100 392 144 48 352 480 352), lower := (rows 23 11 100 392 144 48 64 128 256), losses := [] }

theorem u98 : Upper (D 2) (R 2) [22,9,96,384,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b98
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 11 100 392 144 96 368 432 304), lower := (rows 23 11 100 392 144 96 64 128 256), losses := [] }

theorem u99 : Upper (D 2) (R 2) [22,9,96,384,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b99
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 356, targets := 128 },{ cop := 5, region := 212, targets := 256 }], pairs := [(2,7),(2,8)], upper := (rows 23 11 100 392 144 288 112 240 368), lower := (rows 23 11 100 392 144 288 64 128 256), losses := [] }

theorem u100 : Upper (D 2) (R 2) [22,9,96,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b100
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 44 200 272 48 448 448 448), lower := (rows 23 35 44 200 272 48 64 128 256), losses := [] }

theorem u101 : Upper (D 2) (R 2) [22,33,40,192,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b101
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 36, targets := 144 }], pairs := [(2,4),(2,7)], upper := (rows 23 35 44 200 272 96 464 400 400), lower := (rows 23 35 44 200 272 96 64 128 256), losses := [] }

theorem u102 : Upper (D 2) (R 2) [22,33,40,192,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b102
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 200, targets := 256 }], pairs := [(3,5),(3,8)], upper := (rows 23 35 44 200 272 288 208 208 464), lower := (rows 23 35 44 200 272 288 64 128 256), losses := [] }

theorem u103 : Upper (D 2) (R 2) [22,33,40,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b103
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 76 168 272 48 448 448 448), lower := (rows 23 35 76 168 272 48 64 128 256), losses := [] }

theorem u104 : Upper (D 2) (R 2) [22,33,72,160,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b104
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(3,6)], upper := (rows 23 35 76 168 272 96 464 400 400), lower := (rows 23 35 76 168 272 96 64 128 256), losses := [] }

theorem u105 : Upper (D 2) (R 2) [22,33,72,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b105
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 35 76 168 272 160 336 464 336), lower := (rows 23 35 76 168 272 160 64 128 256), losses := [] }

theorem u106 : Upper (D 2) (R 2) [22,33,72,160,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b106
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 340, targets := 32 }], pairs := [(1,4),(2,5)], upper := (rows 23 35 76 168 272 288 208 208 464), lower := (rows 23 35 76 168 272 288 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 304 64 128 256), good := (rows 39 35 76 168 288 288 64 128 288) }] }

theorem u107 : Upper (D 2) (R 2) [22,33,72,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b107
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 34, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 23 35 76 392 144 48 352 480 352), lower := (rows 23 35 76 392 144 48 64 128 256), losses := [] }

theorem u108 : Upper (D 2) (R 2) [22,33,72,384,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b108
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 354, targets := 128 },{ cop := 1, region := 408, targets := 64 }], pairs := [(1,7),(3,6)], upper := (rows 23 35 76 392 144 96 368 432 304), lower := (rows 23 35 76 392 144 96 64 128 256), losses := [] }

theorem u109 : Upper (D 2) (R 2) [22,33,72,384,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b109
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(0,6),(1,7)], upper := (rows 23 35 76 392 144 288 112 240 368), lower := (rows 23 35 76 392 144 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 152 296 0 128 256), good := (rows 23 35 63 440 144 288 0 144 288) }] }

theorem u110 : Upper (D 2) (R 2) [22,33,72,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b110
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8)], upper := (rows 23 35 100 200 144 40 336 400 272), lower := (rows 23 35 100 200 144 40 64 128 256), losses := [] }

theorem u111 : Upper (D 2) (R 2) [22,33,96,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b111
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 100 200 144 48 328 392 264), lower := (rows 23 35 100 200 144 48 64 128 256), losses := [] }

theorem u112 : Upper (D 2) (R 2) [22,33,96,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b112
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r113 : Route 9 := (fun mask => (mask,id))

def c113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u113 : Upper (D 2) (R 2) [22,33,96,192,128,256] 13 := by
  apply FastRouting.sound _ _ [22,33,96,192,128,256] 13 (by decide) (choices 1) [8,16,256] r113 c113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8
  · exact u9
  · exact u10

def b114 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 100 200 272 40 464 400 400), lower := (rows 23 35 100 200 272 40 64 128 256), losses := [] }

theorem u114 : Upper (D 2) (R 2) [22,33,96,192,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b114
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 100 200 272 48 456 392 392), lower := (rows 23 35 100 200 272 48 64 128 256), losses := [] }

theorem u115 : Upper (D 2) (R 2) [22,33,96,192,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b115
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 36, targets := 272 }], pairs := [(2,4),(2,8)], upper := (rows 23 35 100 200 272 160 344 408 280), lower := (rows 23 35 100 200 272 160 64 128 256), losses := [] }

theorem u116 : Upper (D 2) (R 2) [22,33,96,192,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b116
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 200, targets := 256 }], pairs := [(3,5),(3,8)], upper := (rows 23 35 100 200 272 288 216 152 408), lower := (rows 23 35 100 200 272 288 64 128 256), losses := [] }

theorem u117 : Upper (D 2) (R 2) [22,33,96,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b117
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 100 392 144 40 336 464 336), lower := (rows 23 35 100 392 144 40 64 128 256), losses := [] }

theorem u118 : Upper (D 2) (R 2) [22,33,96,384,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b118
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 100 392 144 48 328 456 328), lower := (rows 23 35 100 392 144 48 64 128 256), losses := [] }

theorem u119 : Upper (D 2) (R 2) [22,33,96,384,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b119
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P02
