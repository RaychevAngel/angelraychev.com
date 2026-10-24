import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 143, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 168 304 96 66 132 320), lower := (rows 7 11 21 168 304 96 66 132 256), losses := [] }

theorem u0 : Upper (D 6) (R 6) [6,9,17,160,288,64,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b0
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 279, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 168 304 96 66 192 260), lower := (rows 7 11 21 168 304 96 66 192 256), losses := [] }

theorem u1 : Upper (D 6) (R 6) [6,9,17,160,288,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 343, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 21 168 336 36 66 160 320), lower := (rows 7 11 21 168 336 36 66 160 256), losses := [] }

theorem u2 : Upper (D 6) (R 6) [6,9,17,160,320,4,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 21 168 336 36 66 192 288), lower := (rows 7 11 21 168 336 36 66 192 256), losses := [{ target := 1, region := (rows 1 0 4 12 80 37 64 208 303), good := (rows 301 297 445 424 464 300 464 208 256) }] }

theorem u3 : Upper (D 6) (R 6) [6,9,17,160,320,4,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b3
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 143, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 152 304 96 66 132 320), lower := (rows 7 11 37 152 304 96 66 132 256), losses := [] }

theorem u4 : Upper (D 6) (R 6) [6,9,33,144,288,64,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b4
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 37 152 304 96 66 192 260), lower := (rows 7 11 37 152 304 96 66 192 256), losses := [] }

theorem u5 : Upper (D 6) (R 6) [6,9,33,144,288,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b5
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 272, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 37 152 336 96 66 132 288), lower := (rows 7 11 37 152 336 96 66 132 256), losses := [] }

theorem u6 : Upper (D 6) (R 6) [6,9,33,144,320,64,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b6
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 168, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 152 336 96 66 160 260), lower := (rows 7 11 37 152 336 96 66 160 256), losses := [] }

theorem u7 : Upper (D 6) (R 6) [6,9,33,144,320,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b7
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 200 336 33 68 130 288), lower := (rows 7 11 52 200 336 33 68 130 256), losses := [] }

theorem u8 : Upper (D 6) (R 6) [6,9,48,192,320,1,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b8
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 200, targets := 3 },{ cop := 0, region := 336, targets := 1 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 52 200 336 33 68 160 258), lower := (rows 7 11 52 200 336 33 68 160 256), losses := [] }

theorem u9 : Upper (D 6) (R 6) [6,9,48,192,320,1,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 200 336 34 68 129 288), lower := (rows 7 11 52 200 336 34 68 129 256), losses := [] }

theorem u10 : Upper (D 6) (R 6) [6,9,48,192,320,2,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(4,1),(4,5)], upper := (rows 7 11 52 200 336 34 68 160 257), lower := (rows 7 11 52 200 336 34 68 160 256), losses := [] }

theorem u11 : Upper (D 6) (R 6) [6,9,48,192,320,2,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 200 336 34 96 129 260), lower := (rows 7 11 52 200 336 34 96 129 256), losses := [] }

theorem u12 : Upper (D 6) (R 6) [6,9,48,192,320,2,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b12
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 200, targets := 3 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 7 11 52 200 336 34 96 132 257), lower := (rows 7 11 52 200 336 34 96 132 256), losses := [] }

theorem u13 : Upper (D 6) (R 6) [6,9,48,192,320,2,32,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b13
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 155, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 56 148 288 65 130 320), lower := (rows 7 11 100 56 148 288 65 130 256), losses := [] }

theorem u14 : Upper (D 6) (R 6) [6,9,96,48,132,256,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b14
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 152, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 100 56 148 288 65 192 258), lower := (rows 7 11 100 56 148 288 65 192 256), losses := [] }

theorem u15 : Upper (D 6) (R 6) [6,9,96,48,132,256,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b15
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 155, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 56 148 288 66 129 320), lower := (rows 7 11 100 56 148 288 66 129 256), losses := [] }

theorem u16 : Upper (D 6) (R 6) [6,9,96,48,132,256,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b16
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 152, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 100 56 148 288 66 192 257), lower := (rows 7 11 100 56 148 288 66 192 256), losses := [] }

theorem u17 : Upper (D 6) (R 6) [6,9,96,48,132,256,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b17
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 152 304 36 66 129 320), lower := (rows 7 11 100 152 304 36 66 129 256), losses := [] }

theorem u18 : Upper (D 6) (R 6) [6,9,96,144,288,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b18
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 304, targets := 66 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,1),(4,6)], upper := (rows 7 11 100 152 304 36 66 192 257), lower := (rows 7 11 100 152 304 36 66 192 256), losses := [] }

theorem u19 : Upper (D 6) (R 6) [6,9,96,144,288,4,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b19
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 276 48 66 129 320), lower := (rows 7 11 100 168 276 48 66 129 256), losses := [] }

theorem u20 : Upper (D 6) (R 6) [6,9,96,160,260,16,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b20
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 66 }], pairs := [(4,1),(4,6)], upper := (rows 7 11 100 168 276 48 66 192 257), lower := (rows 7 11 100 168 276 48 66 192 256), losses := [] }

theorem u21 : Upper (D 6) (R 6) [6,9,96,160,260,16,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b21
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 175, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 56 336 36 66 160 320), lower := (rows 7 11 133 56 336 36 66 160 256), losses := [] }

theorem u22 : Upper (D 6) (R 6) [6,9,129,48,320,4,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b22
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 199, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 133 56 336 36 66 192 288), lower := (rows 7 11 133 56 336 36 66 192 256), losses := [] }

theorem u23 : Upper (D 6) (R 6) [6,9,129,48,320,4,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b23
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 151, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 133 296 52 96 66 144 320), lower := (rows 7 11 133 296 52 96 66 144 256), losses := [] }

theorem u24 : Upper (D 6) (R 6) [6,9,129,288,36,64,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b24
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 199, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 133 296 52 96 66 192 272), lower := (rows 7 11 133 296 52 96 66 192 256), losses := [] }

theorem u25 : Upper (D 6) (R 6) [6,9,129,288,36,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b25
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 272, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 148 104 304 36 65 130 320), lower := (rows 7 11 148 104 304 36 65 130 256), losses := [] }

theorem u26 : Upper (D 6) (R 6) [6,9,144,96,288,4,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b26
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 304, targets := 1 },{ cop := 0, region := 104, targets := 2 },{ cop := 0, region := 304, targets := 64 }], pairs := [(3,1),(4,0),(4,6)], upper := (rows 7 11 148 104 304 36 65 192 258), lower := (rows 7 11 148 104 304 36 65 192 256), losses := [] }

theorem u27 : Upper (D 6) (R 6) [6,9,144,96,288,4,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b27
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 272, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 148 104 304 36 66 129 320), lower := (rows 7 11 148 104 304 36 66 129 256), losses := [] }

theorem u28 : Upper (D 6) (R 6) [6,9,144,96,288,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 304, targets := 66 },{ cop := 0, region := 104, targets := 1 }], pairs := [(3,0),(4,1),(4,6)], upper := (rows 7 11 148 104 304 36 66 192 257), lower := (rows 7 11 148 104 304 36 66 192 256), losses := [] }

theorem u29 : Upper (D 6) (R 6) [6,9,144,96,288,4,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 264, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 148 296 112 36 65 130 320), lower := (rows 7 11 148 296 112 36 65 130 256), losses := [] }

theorem u30 : Upper (D 6) (R 6) [6,9,144,288,96,4,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 296 112 36 65 192 258), lower := (rows 7 11 148 296 112 36 65 192 256), losses := [] }

theorem u31 : Upper (D 6) (R 6) [6,9,144,288,96,4,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b31
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 264, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 148 296 112 36 66 129 320), lower := (rows 7 11 148 296 112 36 66 129 256), losses := [] }

theorem u32 : Upper (D 6) (R 6) [6,9,144,288,96,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b32
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 296 112 36 66 192 257), lower := (rows 7 11 148 296 112 36 66 192 256), losses := [] }

theorem u33 : Upper (D 6) (R 6) [6,9,144,288,96,4,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b33
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 56 276 96 65 130 320), lower := (rows 7 11 164 56 276 96 65 130 256), losses := [] }

theorem u34 : Upper (D 6) (R 6) [6,9,160,48,260,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b34
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 283, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 276 96 65 192 258), lower := (rows 7 11 164 56 276 96 65 192 256), losses := [] }

theorem u35 : Upper (D 6) (R 6) [6,9,160,48,260,64,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b35
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 56 276 96 66 129 320), lower := (rows 7 11 164 56 276 96 66 129 256), losses := [] }

theorem u36 : Upper (D 6) (R 6) [6,9,160,48,260,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b36
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 283, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 276 96 66 192 257), lower := (rows 7 11 164 56 276 96 66 192 256), losses := [] }

theorem u37 : Upper (D 6) (R 6) [6,9,160,48,260,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b37
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 104 276 48 65 130 320), lower := (rows 7 11 164 104 276 48 65 130 256), losses := [] }

theorem u38 : Upper (D 6) (R 6) [6,9,160,96,260,16,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b38
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 104 276 48 65 192 258), lower := (rows 7 11 164 104 276 48 65 192 256), losses := [] }

theorem u39 : Upper (D 6) (R 6) [6,9,160,96,260,16,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b39
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 104 276 48 66 129 320), lower := (rows 7 11 164 104 276 48 66 129 256), losses := [] }

theorem u40 : Upper (D 6) (R 6) [6,9,160,96,260,16,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 66 }], pairs := [(4,1),(4,6)], upper := (rows 7 11 164 104 276 48 66 192 257), lower := (rows 7 11 164 104 276 48 66 192 256), losses := [] }

theorem u41 : Upper (D 6) (R 6) [6,9,160,96,260,16,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 296, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 280 84 96 65 130 288), lower := (rows 7 11 164 280 84 96 65 130 256), losses := [] }

theorem u42 : Upper (D 6) (R 6) [6,9,160,272,68,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b42
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 347, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 280 84 96 65 160 258), lower := (rows 7 11 164 280 84 96 65 160 256), losses := [] }

theorem u43 : Upper (D 6) (R 6) [6,9,160,272,68,64,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b43
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 296, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 280 84 96 66 129 288), lower := (rows 7 11 164 280 84 96 66 129 256), losses := [] }

theorem u44 : Upper (D 6) (R 6) [6,9,160,272,68,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b44
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 347, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 280 84 96 66 160 257), lower := (rows 7 11 164 280 84 96 66 160 256), losses := [] }

theorem u45 : Upper (D 6) (R 6) [6,9,160,272,68,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b45
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 296 84 96 65 130 272), lower := (rows 7 11 164 296 84 96 65 130 256), losses := [] }

theorem u46 : Upper (D 6) (R 6) [6,9,160,288,68,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b46
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 296 84 96 65 144 258), lower := (rows 7 11 164 296 84 96 65 144 256), losses := [] }

theorem u47 : Upper (D 6) (R 6) [6,9,160,288,68,64,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b47
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 296 84 96 66 129 272), lower := (rows 7 11 164 296 84 96 66 129 256), losses := [] }

theorem u48 : Upper (D 6) (R 6) [6,9,160,288,68,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b48
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 296 84 96 66 144 257), lower := (rows 7 11 164 296 84 96 66 144 256), losses := [] }

theorem u49 : Upper (D 6) (R 6) [6,9,160,288,68,64,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b49
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(4,1),(4,5)], upper := (rows 7 26 133 104 273 34 68 160 320), lower := (rows 7 26 133 104 273 34 68 160 256), losses := [] }

theorem u50 : Upper (D 6) (R 6) [6,24,129,96,257,2,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b50
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 304, targets := 4 }], pairs := [(2,1),(2,5),(4,2)], upper := (rows 7 26 133 104 273 34 68 192 288), lower := (rows 7 26 133 104 273 34 68 192 256), losses := [] }

theorem u51 : Upper (D 6) (R 6) [6,24,129,96,257,2,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b51
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 133 26 336 96 68 136 288), lower := (rows 7 35 133 26 336 96 68 136 256), losses := [] }

theorem u52 : Upper (D 6) (R 6) [6,33,129,18,320,64,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b52
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 26 336 96 68 160 264), lower := (rows 7 35 133 26 336 96 68 160 256), losses := [] }

theorem u53 : Upper (D 6) (R 6) [6,33,129,18,320,64,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b53
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 133 88 274 96 68 136 288), lower := (rows 7 35 133 88 274 96 68 136 256), losses := [] }

theorem u54 : Upper (D 6) (R 6) [6,33,129,80,258,64,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b54
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 88 274 96 68 160 264), lower := (rows 7 35 133 88 274 96 68 160 256), losses := [] }

theorem u55 : Upper (D 6) (R 6) [6,33,129,80,258,64,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b55
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 280, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 133 88 304 96 68 130 264), lower := (rows 7 35 133 88 304 96 68 130 256), losses := [] }

theorem u56 : Upper (D 6) (R 6) [6,33,129,80,288,64,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b56
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 133 88 304 96 68 136 258), lower := (rows 7 35 133 88 304 96 68 136 256), losses := [] }

theorem u57 : Upper (D 6) (R 6) [6,33,129,80,288,64,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b57
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 143, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 28 304 96 65 130 320), lower := (rows 7 35 140 28 304 96 65 130 256), losses := [] }

theorem u58 : Upper (D 6) (R 6) [6,33,136,20,288,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b58
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 7 35 140 28 304 96 65 192 258), lower := (rows 7 35 140 28 304 96 65 192 256), losses := [] }

theorem u59 : Upper (D 6) (R 6) [6,33,136,20,288,64,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b59
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P06
