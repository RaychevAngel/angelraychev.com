import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 428, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 15 19 100 168 272 288 80 192 448), lower := (rows 15 19 100 168 272 288 80 128 256), losses := [] }

theorem u0 : Upper (D 2) (R 2) [14,17,96,160,256,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b0
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 68, targets := 272 }], pairs := [(2,4),(2,8)], upper := (rows 15 19 100 168 272 288 192 208 336), lower := (rows 15 19 100 168 272 288 192 128 256), losses := [] }

theorem u1 : Upper (D 2) (R 2) [14,17,96,160,256,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 484, targets := 16 },{ cop := 6, region := 292, targets := 128 }], pairs := [(2,4),(2,7)], upper := (rows 23 11 100 56 144 288 192 448 320), lower := (rows 23 11 100 56 144 288 192 128 256), losses := [] }

theorem u2 : Upper (D 2) (R 2) [22,9,96,48,128,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b2
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 11 100 56 144 288 320 192 448), lower := (rows 23 11 100 56 144 288 320 128 256), losses := [] }

theorem u3 : Upper (D 2) (R 2) [22,9,96,48,128,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b3
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 11 100 168 144 288 80 448 320), lower := (rows 23 11 100 168 144 288 80 128 256), losses := [] }

theorem u4 : Upper (D 2) (R 2) [22,9,96,160,128,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b4
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 11 100 168 144 288 320 208 336), lower := (rows 23 11 100 168 144 288 320 128 256), losses := [] }

theorem u5 : Upper (D 2) (R 2) [22,9,96,160,128,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b5
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 428, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 11 100 168 272 288 80 192 448), lower := (rows 23 11 100 168 272 288 80 128 256), losses := [] }

theorem u6 : Upper (D 2) (R 2) [22,9,96,160,256,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b6
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 68, targets := 272 }], pairs := [(2,4),(2,8)], upper := (rows 23 11 100 168 272 288 192 208 336), lower := (rows 23 11 100 168 272 288 192 128 256), losses := [] }

theorem u7 : Upper (D 2) (R 2) [22,9,96,160,256,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b7
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 23 35 100 200 144 288 72 400 272), lower := (rows 23 35 100 200 144 288 72 128 256), losses := [] }

theorem u8 : Upper (D 2) (R 2) [22,33,96,192,128,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b8
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 264, camps := [{ cop := 6, region := 428, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 35 100 200 144 288 80 392 264), lower := (rows 23 35 100 200 144 288 80 128 256), losses := [] }

theorem u9 : Upper (D 2) (R 2) [22,33,96,192,128,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b9
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 35 100 200 144 288 320 152 280), lower := (rows 23 35 100 200 144 288 320 128 256), losses := [] }

theorem u10 : Upper (D 2) (R 2) [22,33,96,192,128,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b10
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 147, targets := 256 }], pairs := [(0,8)], upper := (rows 23 35 100 392 144 288 72 208 336), lower := (rows 23 35 100 392 144 288 72 128 256), losses := [] }

theorem u11 : Upper (D 2) (R 2) [22,33,96,384,128,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b11
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 428, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 35 100 392 144 288 80 200 328), lower := (rows 23 35 100 392 144 288 80 128 256), losses := [] }

theorem u12 : Upper (D 2) (R 2) [22,33,96,384,128,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b12
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 428, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 196 328 272 40 80 160 416), lower := (rows 23 35 196 328 272 40 80 128 256), losses := [] }

theorem u13 : Upper (D 2) (R 2) [22,33,192,320,256,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b13
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 404, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 328 272 40 96 144 400), lower := (rows 23 35 196 328 272 40 96 128 256), losses := [] }

theorem u14 : Upper (D 2) (R 2) [22,33,192,320,256,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b14
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7)], upper := (rows 23 35 196 328 272 40 192 176 304), lower := (rows 23 35 196 328 272 40 192 128 256), losses := [] }

theorem u15 : Upper (D 2) (R 2) [22,33,192,320,256,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b15
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 72, targets := 160 }], pairs := [(3,5),(3,7)], upper := (rows 23 42 196 73 272 288 80 160 416), lower := (rows 23 42 196 73 272 288 80 128 256), losses := [] }

theorem u16 : Upper (D 2) (R 2) [22,40,192,65,256,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b16
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 404, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,5)], upper := (rows 23 42 196 73 272 288 96 144 400), lower := (rows 23 42 196 73 272 288 96 128 256), losses := [] }

theorem u17 : Upper (D 2) (R 2) [22,40,192,65,256,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b17
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 42 196 73 272 288 192 176 304), lower := (rows 23 42 196 73 272 288 192 128 256), losses := [] }

theorem u18 : Upper (D 2) (R 2) [22,40,192,65,256,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b18
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 196 88 272 160 65 416 288), lower := (rows 23 42 196 88 272 160 65 128 256), losses := [] }

theorem u19 : Upper (D 2) (R 2) [22,40,192,80,256,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b19
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 68, targets := 272 }], pairs := [(2,4),(2,8)], upper := (rows 23 42 196 88 272 160 96 385 257), lower := (rows 23 42 196 88 272 160 96 128 256), losses := [] }

theorem u20 : Upper (D 2) (R 2) [22,40,192,80,256,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b20
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 23 42 196 88 272 160 320 161 289), lower := (rows 23 42 196 88 272 160 320 128 256), losses := [] }

theorem u21 : Upper (D 2) (R 2) [22,40,192,80,256,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b21
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 288, camps := [{ cop := 6, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 328 17 160 80 416 288), lower := (rows 23 42 196 328 17 160 80 128 256), losses := [] }

theorem u22 : Upper (D 2) (R 2) [22,40,192,320,1,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b22
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 272, camps := [{ cop := 5, region := 68, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 196 328 17 160 96 400 272), lower := (rows 23 42 196 328 17 160 96 128 256), losses := [] }

theorem u23 : Upper (D 2) (R 2) [22,40,192,320,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b23
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8)], upper := (rows 23 42 196 328 17 160 320 176 304), lower := (rows 23 42 196 328 17 160 320 128 256), losses := [] }

theorem u24 : Upper (D 2) (R 2) [22,40,192,320,1,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b24
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 228, targets := 256 }], pairs := [(2,8)], upper := (rows 23 42 196 328 272 160 65 176 304), lower := (rows 23 42 196 328 272 160 65 128 256), losses := [] }

theorem u25 : Upper (D 2) (R 2) [22,40,192,320,256,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b25
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 72, targets := 160 }], pairs := [(3,5),(3,7)], upper := (rows 23 42 196 328 272 160 80 161 289), lower := (rows 23 42 196 328 272 160 80 128 256), losses := [] }

theorem u26 : Upper (D 2) (R 2) [22,40,192,320,256,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b26
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 68, targets := 272 }], pairs := [(2,4),(2,8)], upper := (rows 23 42 196 328 272 160 96 145 273), lower := (rows 23 42 196 328 272 160 96 128 256), losses := [] }

theorem u27 : Upper (D 2) (R 2) [22,40,192,320,256,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b27
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 7 76 152 272 160 96 448 320), lower := (rows 51 7 76 152 272 160 96 128 256), losses := [] }

theorem u28 : Upper (D 2) (R 2) [50,5,72,144,256,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b28
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 356, targets := 16 }], pairs := [(2,4),(2,5)], upper := (rows 51 7 76 152 272 160 320 224 352), lower := (rows 51 7 76 152 272 160 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 336 0 336 128 256), good := (rows 83 7 92 220 336 128 336 128 336) }] }

theorem u29 : Upper (D 2) (R 2) [50,5,72,144,256,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b29
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 51 7 84 200 272 160 72 416 288), lower := (rows 51 7 84 200 272 160 72 128 256), losses := [] }

theorem u30 : Upper (D 2) (R 2) [50,5,80,192,256,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b30
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 70, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 51 7 84 200 272 160 96 392 264), lower := (rows 51 7 84 200 272 160 96 128 256), losses := [] }

theorem u31 : Upper (D 2) (R 2) [50,5,80,192,256,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b31
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 171, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 7 84 200 272 160 320 168 296), lower := (rows 51 7 84 200 272 160 320 128 256), losses := [] }

theorem u32 : Upper (D 2) (R 2) [50,5,80,192,256,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b32
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 84 392 144 288 72 224 352), lower := (rows 51 7 84 392 144 288 72 128 256), losses := [] }

theorem u33 : Upper (D 2) (R 2) [50,5,80,384,128,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b33
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 70, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 51 7 84 392 144 288 96 200 328), lower := (rows 51 7 84 392 144 288 96 128 256), losses := [] }

theorem u34 : Upper (D 2) (R 2) [50,5,80,384,128,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b34
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6)], upper := (rows 51 7 196 328 144 288 72 176 304), lower := (rows 51 7 196 328 144 288 72 128 256), losses := [] }

theorem u35 : Upper (D 2) (R 2) [50,5,192,320,128,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b35
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 68, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 51 7 196 328 144 288 80 168 296), lower := (rows 51 7 196 328 144 288 80 128 256), losses := [] }

theorem u36 : Upper (D 2) (R 2) [50,5,192,320,128,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b36
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 72, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 51 7 196 328 144 288 96 152 280), lower := (rows 51 7 196 328 144 288 96 128 256), losses := [] }

theorem u37 : Upper (D 2) (R 2) [50,5,192,320,128,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b37
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 67 76 392 144 288 68 176 304), lower := (rows 51 67 76 392 144 288 68 128 256), losses := [] }

theorem u38 : Upper (D 2) (R 2) [50,65,72,384,128,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b38
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 51 67 76 392 144 288 80 164 292), lower := (rows 51 67 76 392 144 288 80 128 256), losses := [] }

theorem u39 : Upper (D 2) (R 2) [50,65,72,384,128,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b39
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 140 280 144 288 68 224 352), lower := (rows 51 67 140 280 144 288 68 128 256), losses := [] }

theorem u40 : Upper (D 2) (R 2) [50,65,136,272,128,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b40
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 66, targets := 144 }], pairs := [(1,4),(1,7)], upper := (rows 51 67 140 280 144 288 96 196 324), lower := (rows 51 67 140 280 144 288 96 128 256), losses := [] }

theorem u41 : Upper (D 2) (R 2) [50,65,136,272,128,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b41
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 67 140 328 144 288 68 176 304), lower := (rows 51 67 140 328 144 288 68 128 256), losses := [] }

theorem u42 : Upper (D 2) (R 2) [50,65,136,320,128,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b42
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 51 67 140 328 144 288 80 164 292), lower := (rows 51 67 140 328 144 288 80 128 256), losses := [] }

theorem u43 : Upper (D 2) (R 2) [50,65,136,320,128,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b43
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 66, targets := 144 }], pairs := [(1,4),(1,7)], upper := (rows 51 67 140 328 144 288 96 148 276), lower := (rows 51 67 140 328 144 288 96 128 256), losses := [] }

theorem u44 : Upper (D 2) (R 2) [50,65,136,320,128,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b44
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 280 144 288 65 224 352), lower := (rows 51 70 140 280 144 288 65 128 256), losses := [] }

theorem u45 : Upper (D 2) (R 2) [50,68,136,272,128,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b45
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,4),(3,7)], upper := (rows 51 70 140 280 144 288 96 193 321), lower := (rows 51 70 140 280 144 288 96 128 256), losses := [{ target := 4, region := (rows 1 6 4 8 0 297 365 129 257), good := (rows 483 70 238 360 128 352 96 128 352) }] }

theorem u46 : Upper (D 2) (R 2) [50,68,136,272,128,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b46
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 51 194 76 152 272 33 68 416 288), lower := (rows 51 194 76 152 272 33 68 128 256), losses := [] }

theorem u47 : Upper (D 2) (R 2) [50,192,72,144,256,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b47
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 99, targets := 256 }], pairs := [(0,8)], upper := (rows 51 194 76 152 272 33 96 388 260), lower := (rows 51 194 76 152 272 33 96 128 256), losses := [] }

theorem u48 : Upper (D 2) (R 2) [50,192,72,144,256,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b48
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 36, camps := [], pairs := [(1,4)], upper := (rows 51 194 76 152 272 33 320 164 292), lower := (rows 51 194 76 152 272 33 320 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 33 336 128 256), good := (rows 99 194 78 206 320 33 320 128 320) }] }

theorem u49 : Upper (D 2) (R 2) [50,192,72,144,256,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b49
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 51 194 76 392 17 288 68 176 304), lower := (rows 51 194 76 392 17 288 68 128 256), losses := [] }

theorem u50 : Upper (D 2) (R 2) [50,192,72,384,1,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b50
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 430, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 392 17 288 80 164 292), lower := (rows 51 194 76 392 17 288 80 128 256), losses := [] }

theorem u51 : Upper (D 2) (R 2) [50,192,72,384,1,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b51
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 392 17 288 96 148 276), lower := (rows 51 194 76 392 17 288 96 128 256), losses := [] }

theorem u52 : Upper (D 2) (R 2) [50,192,72,384,1,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b52
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 51 194 84 268 272 33 72 160 416), lower := (rows 51 194 84 268 272 33 72 128 256), losses := [] }

theorem u53 : Upper (D 2) (R 2) [50,192,80,260,256,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b53
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 136, camps := [{ cop := 6, region := 414, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 268 272 33 96 136 392), lower := (rows 51 194 84 268 272 33 96 128 256), losses := [] }

theorem u54 : Upper (D 2) (R 2) [50,192,80,260,256,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b54
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7)], upper := (rows 51 194 84 268 272 33 192 168 296), lower := (rows 51 194 84 268 272 33 192 128 256), losses := [] }

theorem u55 : Upper (D 2) (R 2) [50,192,80,260,256,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b55
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 51 194 84 392 272 33 68 168 296), lower := (rows 51 194 84 392 272 33 68 128 256), losses := [] }

theorem u56 : Upper (D 2) (R 2) [50,192,80,384,256,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b56
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 51 194 84 392 272 33 72 164 292), lower := (rows 51 194 84 392 272 33 72 128 256), losses := [] }

theorem u57 : Upper (D 2) (R 2) [50,192,80,384,256,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b57
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 414, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 392 272 33 96 140 268), lower := (rows 51 194 84 392 272 33 96 128 256), losses := [] }

theorem u58 : Upper (D 2) (R 2) [50,192,80,384,256,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b58
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 14 152 272 96 192 416 288), lower := (rows 113 7 14 152 272 96 192 128 256), losses := [] }

theorem u59 : Upper (D 2) (R 2) [112,5,10,144,256,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b59
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P02
