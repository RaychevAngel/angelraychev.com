import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 200 280 33 66 132 288), lower := (rows 7 11 52 200 280 33 66 132 256), losses := [] }

theorem u0 : Upper (D 5) (R 5) [6,9,48,192,264,1,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b0
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 52 200 280 33 68 160 258), lower := (rows 7 11 52 200 280 33 68 160 256), losses := [] }

theorem u1 : Upper (D 5) (R 5) [6,9,48,192,264,1,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 200 280 34 65 132 288), lower := (rows 7 11 52 200 280 34 65 132 256), losses := [] }

theorem u2 : Upper (D 5) (R 5) [6,9,48,192,264,2,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 200, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 52 200 280 34 68 160 257), lower := (rows 7 11 52 200 280 34 68 160 256), losses := [] }

theorem u3 : Upper (D 5) (R 5) [6,9,48,192,264,2,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 11 84 168 304 36 72 129 258), lower := (rows 7 11 84 168 304 36 72 129 256), losses := [] }

theorem u4 : Upper (D 5) (R 5) [6,9,80,160,288,4,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 372, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 84 168 304 36 72 130 257), lower := (rows 7 11 84 168 304 36 72 130 256), losses := [] }

theorem u5 : Upper (D 5) (R 5) [6,9,80,160,288,4,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 332, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 44 76 152 34 320 129 288), lower := (rows 7 19 44 76 152 34 320 129 256), losses := [] }

theorem u6 : Upper (D 5) (R 5) [6,17,40,68,136,2,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 328, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 44 76 152 34 320 160 257), lower := (rows 7 19 44 76 152 34 320 160 256), losses := [] }

theorem u7 : Upper (D 5) (R 5) [6,17,40,68,136,2,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 44 200 280 34 65 132 288), lower := (rows 7 19 44 200 280 34 65 132 256), losses := [] }

theorem u8 : Upper (D 5) (R 5) [6,17,40,192,264,2,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 200 280 34 68 160 257), lower := (rows 7 19 44 200 280 34 68 160 256), losses := [] }

theorem u9 : Upper (D 5) (R 5) [6,17,40,192,264,2,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 324, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 76 140 56 33 320 130 288), lower := (rows 7 19 76 140 56 33 320 130 256), losses := [] }

theorem u10 : Upper (D 5) (R 5) [6,17,72,132,40,1,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b10
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 327, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 140 56 33 320 160 258), lower := (rows 7 19 76 140 56 33 320 160 256), losses := [] }

theorem u11 : Upper (D 5) (R 5) [6,17,72,132,40,1,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b11
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 76 140 56 34 320 129 288), lower := (rows 7 19 76 140 56 34 320 129 256), losses := [] }

theorem u12 : Upper (D 5) (R 5) [6,17,72,132,40,2,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b12
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 327, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 140 56 34 320 160 257), lower := (rows 7 19 76 140 56 34 320 160 256), losses := [] }

theorem u13 : Upper (D 5) (R 5) [6,17,72,132,40,2,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b13
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 1 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 76 140 280 33 96 130 288), lower := (rows 7 19 76 140 280 33 96 130 256), losses := [] }

theorem u14 : Upper (D 5) (R 5) [6,17,72,132,264,1,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b14
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 140 280 33 96 160 258), lower := (rows 7 19 76 140 280 33 96 160 256), losses := [] }

theorem u15 : Upper (D 5) (R 5) [6,17,72,132,264,1,32,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b15
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 76 140 280 34 96 129 288), lower := (rows 7 19 76 140 280 34 96 129 256), losses := [] }

theorem u16 : Upper (D 5) (R 5) [6,17,72,132,264,2,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b16
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 140 280 34 96 160 257), lower := (rows 7 19 76 140 280 34 96 160 256), losses := [] }

theorem u17 : Upper (D 5) (R 5) [6,17,72,132,264,2,32,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b17
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 1 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 100 140 280 33 72 130 288), lower := (rows 7 19 100 140 280 33 72 130 256), losses := [] }

theorem u18 : Upper (D 5) (R 5) [6,17,96,132,264,1,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b18
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 140 280 33 72 160 258), lower := (rows 7 19 100 140 280 33 72 160 256), losses := [] }

theorem u19 : Upper (D 5) (R 5) [6,17,96,132,264,1,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b19
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 100 140 280 34 72 129 288), lower := (rows 7 19 100 140 280 34 72 129 256), losses := [] }

theorem u20 : Upper (D 5) (R 5) [6,17,96,132,264,2,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b20
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 140 280 34 72 160 257), lower := (rows 7 19 100 140 280 34 72 160 256), losses := [] }

theorem u21 : Upper (D 5) (R 5) [6,17,96,132,264,2,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b21
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 280 33 66 136 288), lower := (rows 7 19 196 44 280 33 66 136 256), losses := [] }

theorem u22 : Upper (D 5) (R 5) [6,17,192,36,264,1,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b22
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 44 280 33 72 160 258), lower := (rows 7 19 196 44 280 33 72 160 256), losses := [] }

theorem u23 : Upper (D 5) (R 5) [6,17,192,36,264,1,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b23
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 280 34 65 136 288), lower := (rows 7 19 196 44 280 34 65 136 256), losses := [] }

theorem u24 : Upper (D 5) (R 5) [6,17,192,36,264,2,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b24
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 44 280 34 72 160 257), lower := (rows 7 19 196 44 280 34 72 160 256), losses := [] }

theorem u25 : Upper (D 5) (R 5) [6,17,192,36,264,2,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b25
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 304 33 66 136 264), lower := (rows 7 19 196 44 304 33 66 136 256), losses := [] }

theorem u26 : Upper (D 5) (R 5) [6,17,192,36,288,1,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b26
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 306, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 44 304 33 72 136 258), lower := (rows 7 19 196 44 304 33 72 136 256), losses := [] }

theorem u27 : Upper (D 5) (R 5) [6,17,192,36,288,1,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b27
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 268 56 33 66 136 288), lower := (rows 7 19 196 268 56 33 66 136 256), losses := [] }

theorem u28 : Upper (D 5) (R 5) [6,17,192,260,40,1,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b28
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 196, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 268 56 33 72 160 258), lower := (rows 7 19 196 268 56 33 72 160 256), losses := [] }

theorem u29 : Upper (D 5) (R 5) [6,17,192,260,40,1,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b29
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 268 56 34 65 136 288), lower := (rows 7 19 196 268 56 34 65 136 256), losses := [] }

theorem u30 : Upper (D 5) (R 5) [6,17,192,260,40,2,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b30
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 196 268 56 34 72 160 257), lower := (rows 7 19 196 268 56 34 72 160 256), losses := [] }

theorem u31 : Upper (D 5) (R 5) [6,17,192,260,40,2,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b31
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 228, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 196 42 276 33 65 160 264), lower := (rows 7 26 196 42 276 33 65 160 256), losses := [] }

theorem u32 : Upper (D 5) (R 5) [6,24,192,34,260,1,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b32
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 42 276 33 72 160 257), lower := (rows 7 26 196 42 276 33 72 160 256), losses := [] }

theorem u33 : Upper (D 5) (R 5) [6,24,192,34,260,1,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b33
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 69 138 280 36 80 129 288), lower := (rows 7 42 69 138 280 36 80 129 256), losses := [] }

theorem u34 : Upper (D 5) (R 5) [6,40,65,130,264,4,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b34
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 138, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 138 280 36 80 160 257), lower := (rows 7 42 69 138 280 36 80 160 256), losses := [] }

theorem u35 : Upper (D 5) (R 5) [6,40,65,130,264,4,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b35
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 84 138 280 36 65 129 288), lower := (rows 7 42 84 138 280 36 65 129 256), losses := [] }

theorem u36 : Upper (D 5) (R 5) [6,40,80,130,264,4,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b36
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 138, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 138 280 36 65 160 257), lower := (rows 7 42 84 138 280 36 65 160 256), losses := [] }

theorem u37 : Upper (D 5) (R 5) [6,40,80,130,264,4,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b37
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 274, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 168 280 36 65 129 258), lower := (rows 7 50 76 168 280 36 65 129 256), losses := [] }

theorem u38 : Upper (D 5) (R 5) [6,48,72,160,264,4,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b38
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 50 76 168 280 36 65 130 257), lower := (rows 7 50 76 168 280 36 65 130 256), losses := [] }

theorem u39 : Upper (D 5) (R 5) [6,48,72,160,264,4,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b39
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 268 26 48 96 129 288), lower := (rows 7 67 140 268 26 48 96 129 256), losses := [] }

theorem u40 : Upper (D 5) (R 5) [6,65,136,260,10,16,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b40
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 140 268 26 48 96 160 257), lower := (rows 7 67 140 268 26 48 96 160 256), losses := [] }

theorem u41 : Upper (D 5) (R 5) [6,65,136,260,10,16,32,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b41
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 199, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 268 56 33 80 130 288), lower := (rows 7 67 140 268 56 33 80 130 256), losses := [] }

theorem u42 : Upper (D 5) (R 5) [6,65,136,260,40,1,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b42
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 268 56 33 80 160 258), lower := (rows 7 67 140 268 56 33 80 160 256), losses := [] }

theorem u43 : Upper (D 5) (R 5) [6,65,136,260,40,1,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b43
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 199, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 268 56 34 80 129 288), lower := (rows 7 67 140 268 56 34 80 129 256), losses := [] }

theorem u44 : Upper (D 5) (R 5) [6,65,136,260,40,2,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b44
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 7 67 140 268 56 34 80 160 257), lower := (rows 7 67 140 268 56 34 80 160 256), losses := [] }

theorem u45 : Upper (D 5) (R 5) [6,65,136,260,40,2,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b45
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 42 304 36 72 129 264), lower := (rows 7 67 148 42 304 36 72 129 256), losses := [] }

theorem u46 : Upper (D 5) (R 5) [6,65,144,34,288,4,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b46
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 148 42 304 36 72 136 257), lower := (rows 7 67 148 42 304 36 72 136 256), losses := [] }

theorem u47 : Upper (D 5) (R 5) [6,65,144,34,288,4,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b47
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 42 276 48 72 129 264), lower := (rows 7 67 164 42 276 48 72 129 256), losses := [] }

theorem u48 : Upper (D 5) (R 5) [6,65,160,34,260,16,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b48
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 164 42 276 48 72 136 257), lower := (rows 7 67 164 42 276 48 72 136 256), losses := [] }

theorem u49 : Upper (D 5) (R 5) [6,65,160,34,260,16,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b49
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 56 276 34 72 129 264), lower := (rows 7 67 164 56 276 34 72 129 256), losses := [] }

theorem u50 : Upper (D 5) (R 5) [6,65,160,48,260,2,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b50
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 67 164 56 276 34 72 136 257), lower := (rows 7 67 164 56 276 34 72 136 256), losses := [] }

theorem u51 : Upper (D 5) (R 5) [6,65,160,48,260,2,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b51
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 164 42 276 48 65 129 264), lower := (rows 7 74 164 42 276 48 65 129 256), losses := [] }

theorem u52 : Upper (D 5) (R 5) [6,72,160,34,260,16,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b52
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 74 164 42 276 48 65 136 257), lower := (rows 7 74 164 42 276 48 65 136 256), losses := [] }

theorem u53 : Upper (D 5) (R 5) [6,72,160,34,260,16,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b53
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 164 56 276 34 65 129 264), lower := (rows 7 74 164 56 276 34 65 129 256), losses := [] }

theorem u54 : Upper (D 5) (R 5) [6,72,160,48,260,2,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b54
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 74 164 56 276 34 65 136 257), lower := (rows 7 74 164 56 276 34 65 136 256), losses := [] }

theorem u55 : Upper (D 5) (R 5) [6,72,160,48,260,2,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b55
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 346, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 82 164 42 276 33 72 129 264), lower := (rows 7 82 164 42 276 33 72 129 256), losses := [] }

theorem u56 : Upper (D 5) (R 5) [6,80,160,34,260,1,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b56
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 164 42 276 33 72 136 257), lower := (rows 7 82 164 42 276 33 72 136 256), losses := [] }

theorem u57 : Upper (D 5) (R 5) [6,80,160,34,260,1,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b57
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 76 168 280 36 65 130 260), lower := (rows 19 35 76 168 280 36 65 130 256), losses := [] }

theorem u58 : Upper (D 5) (R 5) [18,33,72,160,264,4,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b58
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 172, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 76 168 280 36 65 132 258), lower := (rows 19 35 76 168 280 36 65 132 256), losses := [] }

theorem u59 : Upper (D 5) (R 5) [18,33,72,160,264,4,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b59
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P05
