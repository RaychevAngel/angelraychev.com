import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 296 144 48 66 192 448), lower := (rows 23 11 100 296 144 48 66 128 256), losses := [] }

theorem u0 : Upper (D 1) (R 1) [22,9,96,288,128,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b0
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 296 144 48 192 194 322), lower := (rows 23 11 100 296 144 48 192 128 256), losses := [] }

theorem u1 : Upper (D 1) (R 1) [22,9,96,288,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 296 144 160 66 208 336), lower := (rows 23 11 100 296 144 160 66 128 256), losses := [] }

theorem u2 : Upper (D 1) (R 1) [22,9,96,288,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 296 144 160 80 194 322), lower := (rows 23 11 100 296 144 160 80 128 256), losses := [] }

theorem u3 : Upper (D 1) (R 1) [22,9,96,288,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 23 11 292 104 144 48 66 192 448), lower := (rows 23 11 292 104 144 48 66 128 256), losses := [] }

theorem u4 : Upper (D 1) (R 1) [22,9,288,96,128,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 2 }], pairs := [(3,1)], upper := (rows 23 11 292 104 144 48 192 194 322), lower := (rows 23 11 292 104 144 48 192 128 256), losses := [] }

theorem u5 : Upper (D 1) (R 1) [22,9,288,96,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 292 104 144 160 66 208 336), lower := (rows 23 11 292 104 144 160 66 128 256), losses := [] }

theorem u6 : Upper (D 1) (R 1) [22,9,288,96,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 2 }], pairs := [(3,1)], upper := (rows 23 11 292 104 144 160 80 194 322), lower := (rows 23 11 292 104 144 160 80 128 256), losses := [] }

theorem u7 : Upper (D 1) (R 1) [22,9,288,96,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 266 144 48 192 224 352), lower := (rows 23 98 13 266 144 48 192 128 256), losses := [] }

theorem u8 : Upper (D 1) (R 1) [22,96,9,258,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 13 266 144 96 192 176 304), lower := (rows 23 98 13 266 144 96 192 128 256), losses := [] }

theorem u9 : Upper (D 1) (R 1) [22,96,9,258,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 296 144 160 66 208 336), lower := (rows 23 98 13 296 144 160 66 128 256), losses := [] }

theorem u10 : Upper (D 1) (R 1) [22,96,9,288,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b10
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 296 144 160 80 194 322), lower := (rows 23 98 13 296 144 160 80 128 256), losses := [] }

theorem u11 : Upper (D 1) (R 1) [22,96,9,288,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b11
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 13 74 144 160 80 224 352), lower := (rows 23 290 13 74 144 160 80 128 256), losses := [] }

theorem u12 : Upper (D 1) (R 1) [22,288,9,66,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b12
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 72, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 13 74 144 160 96 208 336), lower := (rows 23 290 13 74 144 160 96 128 256), losses := [] }

theorem u13 : Upper (D 1) (R 1) [22,288,9,66,128,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b13
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 72, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 13 104 144 160 66 208 336), lower := (rows 23 290 13 104 144 160 66 128 256), losses := [] }

theorem u14 : Upper (D 1) (R 1) [22,288,9,96,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b14
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 13 104 144 160 80 194 322), lower := (rows 23 290 13 104 144 160 80 128 256), losses := [] }

theorem u15 : Upper (D 1) (R 1) [22,288,9,96,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b15
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 266 144 48 192 224 352), lower := (rows 29 98 7 266 144 48 192 128 256), losses := [] }

theorem u16 : Upper (D 1) (R 1) [28,96,3,258,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b16
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 7 266 144 96 192 176 304), lower := (rows 29 98 7 266 144 96 192 128 256), losses := [] }

theorem u17 : Upper (D 1) (R 1) [28,96,3,258,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b17
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 7 296 80 160 66 144 400), lower := (rows 29 98 7 296 80 160 66 128 256), losses := [] }

theorem u18 : Upper (D 1) (R 1) [28,96,3,288,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b18
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 7 296 80 160 80 130 386), lower := (rows 29 98 7 296 80 160 80 128 256), losses := [] }

theorem u19 : Upper (D 1) (R 1) [28,96,3,288,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b19
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 7 296 80 160 192 146 274), lower := (rows 29 98 7 296 80 160 192 128 256), losses := [] }

theorem u20 : Upper (D 1) (R 1) [28,96,3,288,64,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b20
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 296 144 160 66 208 336), lower := (rows 29 98 7 296 144 160 66 128 256), losses := [] }

theorem u21 : Upper (D 1) (R 1) [28,96,3,288,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b21
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 296 144 160 80 194 322), lower := (rows 29 98 7 296 144 160 80 128 256), losses := [] }

theorem u22 : Upper (D 1) (R 1) [28,96,3,288,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b22
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 18, camps := [], pairs := [], upper := (rows 29 98 134 296 80 160 65 146 274), lower := (rows 29 98 134 296 80 160 65 128 256), losses := [] }

theorem u23 : Upper (D 1) (R 1) [28,96,130,288,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b23
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 424, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 134 296 80 160 66 145 273), lower := (rows 29 98 134 296 80 160 66 128 256), losses := [] }

theorem u24 : Upper (D 1) (R 1) [28,96,130,288,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b24
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 296 80 160 80 131 259), lower := (rows 29 98 134 296 80 160 80 128 256), losses := [] }

theorem u25 : Upper (D 1) (R 1) [28,96,130,288,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b25
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 29 259 38 74 144 48 192 224 352), lower := (rows 29 259 38 74 144 48 192 128 256), losses := [] }

theorem u26 : Upper (D 1) (R 1) [28,257,34,66,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b26
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 29 259 38 74 144 96 192 176 304), lower := (rows 29 259 38 74 144 96 192 128 256), losses := [] }

theorem u27 : Upper (D 1) (R 1) [28,257,34,66,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b27
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 74 144 160 80 224 352), lower := (rows 29 290 7 74 144 160 80 128 256), losses := [] }

theorem u28 : Upper (D 1) (R 1) [28,288,3,66,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b28
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 72, targets := 16 }], pairs := [(3,4)], upper := (rows 29 290 7 74 144 160 96 208 336), lower := (rows 29 290 7 74 144 160 96 128 256), losses := [] }

theorem u29 : Upper (D 1) (R 1) [28,288,3,66,128,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b29
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 72, targets := 16 }], pairs := [(3,4)], upper := (rows 29 290 7 104 144 160 66 208 336), lower := (rows 29 290 7 104 144 160 66 128 256), losses := [] }

theorem u30 : Upper (D 1) (R 1) [28,288,3,96,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b30
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 104 144 160 80 194 322), lower := (rows 29 290 7 104 144 160 80 128 256), losses := [] }

theorem u31 : Upper (D 1) (R 1) [28,288,3,96,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b31
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 412, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 88 144 96 66 160 416), lower := (rows 51 7 268 88 144 96 66 128 256), losses := [] }

theorem u32 : Upper (D 1) (R 1) [50,5,264,80,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b32
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 268 88 144 96 96 130 386), lower := (rows 51 7 268 88 144 96 96 128 256), losses := [] }

theorem u33 : Upper (D 1) (R 1) [50,5,264,80,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b33
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 268 88 144 96 192 162 290), lower := (rows 51 7 268 88 144 96 192 128 256), losses := [] }

theorem u34 : Upper (D 1) (R 1) [50,5,264,80,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b34
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 200 80 160 66 176 304), lower := (rows 51 7 268 200 80 160 66 128 256), losses := [] }

theorem u35 : Upper (D 1) (R 1) [50,5,264,192,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b35
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 268 200 80 160 80 162 290), lower := (rows 51 7 268 200 80 160 80 128 256), losses := [] }

theorem u36 : Upper (D 1) (R 1) [50,5,264,192,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b36
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 268 200 80 160 96 146 274), lower := (rows 51 7 268 200 80 160 96 128 256), losses := [] }

theorem u37 : Upper (D 1) (R 1) [50,5,264,192,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b37
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 152 80 160 66 164 292), lower := (rows 51 259 76 152 80 160 66 128 256), losses := [] }

theorem u38 : Upper (D 1) (R 1) [50,257,72,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b38
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 51 259 76 152 80 160 68 162 290), lower := (rows 51 259 76 152 80 160 68 128 256), losses := [] }

theorem u39 : Upper (D 1) (R 1) [50,257,72,144,64,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b39
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 92, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 152 80 160 96 134 262), lower := (rows 51 259 76 152 80 160 96 128 256), losses := [] }

theorem u40 : Upper (D 1) (R 1) [50,257,72,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b40
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 156, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 168 144 96 66 140 268), lower := (rows 51 259 84 168 144 96 66 128 256), losses := [] }

theorem u41 : Upper (D 1) (R 1) [50,257,80,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b41
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 51 259 84 168 144 96 68 138 266), lower := (rows 51 259 84 168 144 96 68 128 256), losses := [] }

theorem u42 : Upper (D 1) (R 1) [50,257,80,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b42
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 51 259 84 168 144 96 72 134 262), lower := (rows 51 259 84 168 144 96 72 128 256), losses := [] }

theorem u43 : Upper (D 1) (R 1) [50,257,80,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b43
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 262 200 80 160 66 176 304), lower := (rows 53 11 262 200 80 160 66 128 256), losses := [] }

theorem u44 : Upper (D 1) (R 1) [52,9,258,192,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b44
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 420, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 262 200 80 160 80 162 290), lower := (rows 53 11 262 200 80 160 80 128 256), losses := [] }

theorem u45 : Upper (D 1) (R 1) [52,9,258,192,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b45
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 262 200 80 160 96 146 274), lower := (rows 53 11 262 200 80 160 96 128 256), losses := [] }

theorem u46 : Upper (D 1) (R 1) [52,9,258,192,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b46
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 48, camps := [], pairs := [(0,6)], upper := (rows 53 11 324 200 18 160 66 176 304), lower := (rows 53 11 324 200 18 160 66 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 82 255 0 223 351), good := (rows 437 443 437 440 434 160 434 160 256) }] }

theorem u47 : Upper (D 1) (R 1) [52,9,320,192,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b47
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 34, camps := [], pairs := [(2,4)], upper := (rows 53 11 324 200 18 160 80 162 290), lower := (rows 53 11 324 200 18 160 80 128 256), losses := [{ target := 4, region := (rows 1 2 68 72 0 251 64 146 274), good := (rows 421 427 364 236 418 160 492 160 256) }] }

theorem u48 : Upper (D 1) (R 1) [52,9,320,192,2,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b48
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 324 200 18 160 96 146 274), lower := (rows 53 11 324 200 18 160 96 128 256), losses := [] }

theorem u49 : Upper (D 1) (R 1) [52,9,320,192,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b49
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 53 26 324 104 144 34 65 130 386), lower := (rows 53 26 324 104 144 34 65 128 256), losses := [] }

theorem u50 : Upper (D 1) (R 1) [52,24,320,96,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b50
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 324 104 144 34 66 129 385), lower := (rows 53 26 324 104 144 34 66 128 256), losses := [] }

theorem u51 : Upper (D 1) (R 1) [52,24,320,96,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b51
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 3, camps := [], pairs := [(3,1)], upper := (rows 53 26 324 104 144 34 192 131 259), lower := (rows 53 26 324 104 144 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 208 32 208 128 256), good := (rows 125 88 340 120 208 32 208 208 256) }] }

theorem u52 : Upper (D 1) (R 1) [52,24,320,96,128,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b52
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 53 67 262 138 80 160 72 176 304), lower := (rows 53 67 262 138 80 160 72 128 256), losses := [] }

theorem u53 : Upper (D 1) (R 1) [52,65,258,130,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b53
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 428, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 262 138 80 160 80 168 296), lower := (rows 53 67 262 138 80 160 80 128 256), losses := [] }

theorem u54 : Upper (D 1) (R 1) [52,65,258,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b54
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 53 67 262 138 80 160 96 152 280), lower := (rows 53 67 262 138 80 160 96 128 256), losses := [] }

theorem u55 : Upper (D 1) (R 1) [52,65,258,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b55
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 152 80 160 66 168 296), lower := (rows 53 67 262 152 80 160 66 128 256), losses := [] }

theorem u56 : Upper (D 1) (R 1) [52,65,258,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b56
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 67 262 152 80 160 72 162 290), lower := (rows 53 67 262 152 80 160 72 128 256), losses := [] }

theorem u57 : Upper (D 1) (R 1) [52,65,258,144,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b57
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 53 67 262 152 80 160 96 138 266), lower := (rows 53 67 262 152 80 160 96 128 256), losses := [] }

theorem u58 : Upper (D 1) (R 1) [52,65,258,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b58
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 53 67 388 138 18 96 72 176 304), lower := (rows 53 67 388 138 18 96 72 128 256), losses := [] }

theorem u59 : Upper (D 1) (R 1) [52,65,384,130,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b59
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P01
