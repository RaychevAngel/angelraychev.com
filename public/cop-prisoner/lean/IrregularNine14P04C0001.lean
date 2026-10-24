import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0000

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 11 52 200 276 40 83 147 275), lower := (rows 7 11 52 200 276 40 64 128 256), losses := [] }

theorem u60 : Upper (D 4) (R 4) [6,9,48,192,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b60
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 52, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 276 48 75 139 267), lower := (rows 7 11 52 200 276 48 64 128 256), losses := [] }

theorem u61 : Upper (D 4) (R 4) [6,9,48,192,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b61
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 200 280 33 86 150 278), lower := (rows 7 11 52 200 280 33 64 128 256), losses := [] }

theorem u62 : Upper (D 4) (R 4) [6,9,48,192,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b62
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 200 280 34 85 149 277), lower := (rows 7 11 52 200 280 34 64 128 256), losses := [] }

theorem u63 : Upper (D 4) (R 4) [6,9,48,192,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b63
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 474, targets := 4 }], pairs := [(1,2)], upper := (rows 7 11 52 200 280 36 83 147 275), lower := (rows 7 11 52 200 280 36 64 128 256), losses := [] }

theorem u64 : Upper (D 4) (R 4) [6,9,48,192,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b64
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 203, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 52 200 280 48 71 135 263), lower := (rows 7 11 52 200 280 48 64 128 256), losses := [] }

theorem u65 : Upper (D 4) (R 4) [6,9,48,192,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b65
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 73 146 36 344 408 280), lower := (rows 7 26 37 73 146 36 64 128 256), losses := [] }

theorem u66 : Upper (D 4) (R 4) [6,24,33,65,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b66
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 37, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 37 73 146 40 340 404 276), lower := (rows 7 26 37 73 146 40 64 128 256), losses := [] }

theorem u67 : Upper (D 4) (R 4) [6,24,33,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b67
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 328, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 37 73 146 48 332 396 268), lower := (rows 7 26 37 73 146 48 64 128 256), losses := [] }

theorem u68 : Upper (D 4) (R 4) [6,24,33,65,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b68
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 28, camps := [], pairs := [], upper := (rows 7 26 37 73 146 288 92 156 284), lower := (rows 7 26 37 73 146 288 64 128 256), losses := [] }

theorem u69 : Upper (D 4) (R 4) [6,24,33,65,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b69
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 73 400 34 92 156 284), lower := (rows 7 26 37 73 400 34 64 128 256), losses := [] }

theorem u70 : Upper (D 4) (R 4) [6,24,33,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b70
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 73 400 36 90 154 282), lower := (rows 7 26 37 73 400 36 64 128 256), losses := [] }

theorem u71 : Upper (D 4) (R 4) [6,24,33,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b71
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 37, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 37 73 400 40 86 150 278), lower := (rows 7 26 37 73 400 40 64 128 256), losses := [] }

theorem u72 : Upper (D 4) (R 4) [6,24,33,65,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b72
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 73 400 48 78 142 270), lower := (rows 7 26 37 73 400 48 64 128 256), losses := [] }

theorem u73 : Upper (D 4) (R 4) [6,24,33,65,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b73
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 74 148 33 344 408 280), lower := (rows 7 26 37 74 148 33 64 128 256), losses := [] }

theorem u74 : Upper (D 4) (R 4) [6,24,33,66,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b74
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 37 74 148 40 337 401 273), lower := (rows 7 26 37 74 148 40 64 128 256), losses := [] }

theorem u75 : Upper (D 4) (R 4) [6,24,33,66,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b75
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 328, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 37 74 148 48 329 393 265), lower := (rows 7 26 37 74 148 48 64 128 256), losses := [] }

theorem u76 : Upper (D 4) (R 4) [6,24,33,66,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b76
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 7 26 37 74 148 288 89 153 281), lower := (rows 7 26 37 74 148 288 64 128 256), losses := [] }

theorem u77 : Upper (D 4) (R 4) [6,24,33,66,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b77
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 74 400 33 92 156 284), lower := (rows 7 26 37 74 400 33 64 128 256), losses := [] }

theorem u78 : Upper (D 4) (R 4) [6,24,33,66,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b78
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 74 400 36 89 153 281), lower := (rows 7 26 37 74 400 36 64 128 256), losses := [] }

theorem u79 : Upper (D 4) (R 4) [6,24,33,66,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b79
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 37 74 400 40 85 149 277), lower := (rows 7 26 37 74 400 40 64 128 256), losses := [] }

theorem u80 : Upper (D 4) (R 4) [6,24,33,66,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b80
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 74 400 48 77 141 269), lower := (rows 7 26 37 74 400 48 64 128 256), losses := [] }

theorem u81 : Upper (D 4) (R 4) [6,24,33,66,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b81
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 76 400 33 90 154 282), lower := (rows 7 26 37 76 400 33 64 128 256), losses := [] }

theorem u82 : Upper (D 4) (R 4) [6,24,33,68,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b82
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 76 400 34 89 153 281), lower := (rows 7 26 37 76 400 34 64 128 256), losses := [] }

theorem u83 : Upper (D 4) (R 4) [6,24,33,68,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b83
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 26 37 76 400 40 83 147 275), lower := (rows 7 26 37 76 400 40 64 128 256), losses := [] }

theorem u84 : Upper (D 4) (R 4) [6,24,33,68,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b84
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 76 400 48 75 139 267), lower := (rows 7 26 37 76 400 48 64 128 256), losses := [] }

theorem u85 : Upper (D 4) (R 4) [6,24,33,68,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b85
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 28, camps := [], pairs := [(2,1)], upper := (rows 7 26 100 137 274 33 92 156 284), lower := (rows 7 26 100 137 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 9 16 41 66 130 258), good := (rows 493 508 100 173 468 45 64 128 256) }] }

theorem u86 : Upper (D 4) (R 4) [6,24,96,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b86
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 25, camps := [{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 274 36 89 153 281), lower := (rows 7 26 100 137 274 36 64 128 256), losses := [] }

theorem u87 : Upper (D 4) (R 4) [6,24,96,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b87
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 100 137 274 40 85 149 277), lower := (rows 7 26 100 137 274 40 64 128 256), losses := [] }

theorem u88 : Upper (D 4) (R 4) [6,24,96,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b88
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 100 137 274 48 77 141 269), lower := (rows 7 26 100 137 274 48 64 128 256), losses := [] }

theorem u89 : Upper (D 4) (R 4) [6,24,96,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b89
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 26, camps := [], pairs := [(1,0)], upper := (rows 7 26 100 137 276 33 90 154 282), lower := (rows 7 26 100 137 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 32 74 138 266), good := (rows 470 474 100 474 276 48 64 128 256) }] }

theorem u90 : Upper (D 4) (R 4) [6,24,96,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b90
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 100 137 276 34 89 153 281), lower := (rows 7 26 100 137 276 34 64 128 256), losses := [] }

theorem u91 : Upper (D 4) (R 4) [6,24,96,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b91
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 100 137 276 40 83 147 275), lower := (rows 7 26 100 137 276 40 64 128 256), losses := [] }

theorem u92 : Upper (D 4) (R 4) [6,24,96,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b92
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 100 137 276 48 75 139 267), lower := (rows 7 26 100 137 276 48 64 128 256), losses := [] }

theorem u93 : Upper (D 4) (R 4) [6,24,96,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b93
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r94 : Route 9 := (fun mask => (mask,id))

def c94 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u94 : Upper (D 4) (R 4) [6,24,96,130,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,260,1] 13 (by decide) (choices 1) [1,8,16] r94 c94
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2
  · exact u3
  · exact u4

def b95 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 100 138 276 40 81 145 273), lower := (rows 7 26 100 138 276 40 64 128 256), losses := [] }

theorem u95 : Upper (D 4) (R 4) [6,24,96,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b95
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 100 138 276 48 73 137 265), lower := (rows 7 26 100 138 276 48 64 128 256), losses := [] }

theorem u96 : Upper (D 4) (R 4) [6,24,96,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b96
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 26 148 33 344 408 280), lower := (rows 7 35 76 26 148 33 64 128 256), losses := [] }

theorem u97 : Upper (D 4) (R 4) [6,33,72,18,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b97
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 35 76 26 148 40 337 401 273), lower := (rows 7 35 76 26 148 40 64 128 256), losses := [] }

theorem u98 : Upper (D 4) (R 4) [6,33,72,18,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b98
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 325, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 26 148 48 329 393 265), lower := (rows 7 35 76 26 148 48 64 128 256), losses := [] }

theorem u99 : Upper (D 4) (R 4) [6,33,72,18,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b99
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 7 35 76 26 148 288 89 153 281), lower := (rows 7 35 76 26 148 288 64 128 256), losses := [] }

theorem u100 : Upper (D 4) (R 4) [6,33,72,18,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b100
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 26 152 33 340 404 276), lower := (rows 7 35 76 26 152 33 64 128 256), losses := [] }

theorem u101 : Upper (D 4) (R 4) [6,33,72,18,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b101
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 26 152 36 337 401 273), lower := (rows 7 35 76 26 152 36 64 128 256), losses := [] }

theorem u102 : Upper (D 4) (R 4) [6,33,72,18,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b102
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 325, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 26 152 48 325 389 261), lower := (rows 7 35 76 26 152 48 64 128 256), losses := [] }

theorem u103 : Upper (D 4) (R 4) [6,33,72,18,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b103
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 7 35 76 26 152 288 85 149 277), lower := (rows 7 35 76 26 152 288 64 128 256), losses := [] }

theorem u104 : Upper (D 4) (R 4) [6,33,72,18,136,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b104
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 26 400 33 92 156 284), lower := (rows 7 35 76 26 400 33 64 128 256), losses := [] }

theorem u105 : Upper (D 4) (R 4) [6,33,72,18,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b105
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 26 400 36 89 153 281), lower := (rows 7 35 76 26 400 36 64 128 256), losses := [] }

theorem u106 : Upper (D 4) (R 4) [6,33,72,18,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b106
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 35 76 26 400 40 85 149 277), lower := (rows 7 35 76 26 400 40 64 128 256), losses := [] }

theorem u107 : Upper (D 4) (R 4) [6,33,72,18,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b107
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 69, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 26 400 48 77 141 269), lower := (rows 7 35 76 26 400 48 64 128 256), losses := [] }

theorem u108 : Upper (D 4) (R 4) [6,33,72,18,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b108
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 28 146 33 344 408 280), lower := (rows 7 35 76 28 146 33 64 128 256), losses := [] }

theorem u109 : Upper (D 4) (R 4) [6,33,72,20,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b109
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 35 76 28 146 40 337 401 273), lower := (rows 7 35 76 28 146 40 64 128 256), losses := [] }

theorem u110 : Upper (D 4) (R 4) [6,33,72,20,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b110
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 28 146 48 329 393 265), lower := (rows 7 35 76 28 146 48 64 128 256), losses := [] }

theorem u111 : Upper (D 4) (R 4) [6,33,72,20,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b111
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 7 35 76 28 146 288 89 153 281), lower := (rows 7 35 76 28 146 288 64 128 256), losses := [] }

theorem u112 : Upper (D 4) (R 4) [6,33,72,20,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b112
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 28 400 33 90 154 282), lower := (rows 7 35 76 28 400 33 64 128 256), losses := [] }

theorem u113 : Upper (D 4) (R 4) [6,33,72,20,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b113
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 28 400 34 89 153 281), lower := (rows 7 35 76 28 400 34 64 128 256), losses := [] }

theorem u114 : Upper (D 4) (R 4) [6,33,72,20,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b114
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 35 76 28 400 40 83 147 275), lower := (rows 7 35 76 28 400 40 64 128 256), losses := [] }

theorem u115 : Upper (D 4) (R 4) [6,33,72,20,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b115
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 28 400 48 75 139 267), lower := (rows 7 35 76 28 400 48 64 128 256), losses := [] }

theorem u116 : Upper (D 4) (R 4) [6,33,72,20,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b116
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 274 36 88 152 280), lower := (rows 7 35 76 137 274 36 64 128 256), losses := [] }

theorem u117 : Upper (D 4) (R 4) [6,33,72,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b117
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 137 274 40 84 148 276), lower := (rows 7 35 76 137 274 40 64 128 256), losses := [] }

theorem u118 : Upper (D 4) (R 4) [6,33,72,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b118
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r119 : Route 9 := (fun mask => (mask,id))

def c119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u119 : Upper (D 4) (R 4) [6,33,72,129,258,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,258,16] 13 (by decide) (choices 1) [4,8,16] r119 c119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5
  · exact u6
  · exact u7

#print axioms u119
end Delivery.IrregularNine14.P04
