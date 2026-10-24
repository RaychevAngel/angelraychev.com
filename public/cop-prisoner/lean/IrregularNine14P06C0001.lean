import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 143, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 28 304 96 66 129 320), lower := (rows 7 35 140 28 304 96 66 129 256), losses := [] }

theorem u60 : Upper (D 6) (R 6) [6,33,136,20,288,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b60
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 140 28 304 96 66 192 257), lower := (rows 7 35 140 28 304 96 66 192 256), losses := [] }

theorem u61 : Upper (D 6) (R 6) [6,33,136,20,288,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b61
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 272, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 140 28 336 96 65 130 288), lower := (rows 7 35 140 28 336 96 65 130 256), losses := [] }

theorem u62 : Upper (D 6) (R 6) [6,33,136,20,320,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b62
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 28 336 96 65 160 258), lower := (rows 7 35 140 28 336 96 65 160 256), losses := [] }

theorem u63 : Upper (D 6) (R 6) [6,33,136,20,320,64,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b63
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 56 276 96 65 130 320), lower := (rows 7 35 140 56 276 96 65 130 256), losses := [] }

theorem u64 : Upper (D 6) (R 6) [6,33,136,48,260,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b64
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 272, targets := 1 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 272, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 35 140 56 276 96 65 192 258), lower := (rows 7 35 140 56 276 96 65 192 256), losses := [] }

theorem u65 : Upper (D 6) (R 6) [6,33,136,48,260,64,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b65
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 56 276 96 66 129 320), lower := (rows 7 35 140 56 276 96 66 129 256), losses := [] }

theorem u66 : Upper (D 6) (R 6) [6,33,136,48,260,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b66
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 66 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 35 140 56 276 96 66 192 257), lower := (rows 7 35 140 56 276 96 66 192 256), losses := [] }

theorem u67 : Upper (D 6) (R 6) [6,33,136,48,260,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b67
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 1, region := 272, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 7 35 140 88 304 96 68 129 258), lower := (rows 7 35 140 88 304 96 68 129 256), losses := [] }

theorem u68 : Upper (D 6) (R 6) [6,33,136,80,288,64,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b68
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 1, region := 272, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 7 35 140 88 304 96 68 130 257), lower := (rows 7 35 140 88 304 96 68 130 256), losses := [] }

theorem u69 : Upper (D 6) (R 6) [6,33,136,80,288,64,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b69
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 296 82 96 68 129 272), lower := (rows 7 35 140 296 82 96 68 129 256), losses := [] }

theorem u70 : Upper (D 6) (R 6) [6,33,136,288,66,64,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b70
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 35 140 296 82 96 68 144 257), lower := (rows 7 35 140 296 82 96 68 144 256), losses := [] }

theorem u71 : Upper (D 6) (R 6) [6,33,136,288,66,64,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b71
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 52 200 336 33 66 129 260), lower := (rows 7 42 52 200 336 33 66 129 256), losses := [] }

theorem u72 : Upper (D 6) (R 6) [6,40,48,192,320,1,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b72
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 42 52 200 336 33 66 132 257), lower := (rows 7 42 52 200 336 33 66 132 256), losses := [] }

theorem u73 : Upper (D 6) (R 6) [6,40,48,192,320,1,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b73
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 164 88 276 33 66 129 320), lower := (rows 7 42 164 88 276 33 66 129 256), losses := [] }

theorem u74 : Upper (D 6) (R 6) [6,40,160,80,260,1,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b74
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 164 88 276 33 66 192 257), lower := (rows 7 42 164 88 276 33 66 192 256), losses := [] }

theorem u75 : Upper (D 6) (R 6) [6,40,160,80,260,1,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b75
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,2)], upper := (rows 7 42 196 25 336 36 66 129 288), lower := (rows 7 42 196 25 336 36 66 129 256), losses := [] }

theorem u76 : Upper (D 6) (R 6) [6,40,192,17,320,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b76
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 196 25 336 36 66 160 257), lower := (rows 7 42 196 25 336 36 66 160 256), losses := [] }

theorem u77 : Upper (D 6) (R 6) [6,40,192,17,320,4,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b77
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 196 26 336 33 96 129 260), lower := (rows 7 42 196 26 336 33 96 129 256), losses := [] }

theorem u78 : Upper (D 6) (R 6) [6,40,192,18,320,1,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b78
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 378, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 42 196 26 336 33 96 132 257), lower := (rows 7 42 196 26 336 33 96 132 256), losses := [] }

theorem u79 : Upper (D 6) (R 6) [6,40,192,18,320,1,32,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b79
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 314, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 196 26 336 36 65 129 288), lower := (rows 7 42 196 26 336 36 65 129 256), losses := [] }

theorem u80 : Upper (D 6) (R 6) [6,40,192,18,320,4,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b80
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 196 26 336 36 65 160 257), lower := (rows 7 42 196 26 336 36 65 160 256), losses := [] }

theorem u81 : Upper (D 6) (R 6) [6,40,192,18,320,4,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b81
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 88 274 36 65 129 288), lower := (rows 7 42 196 88 274 36 65 129 256), losses := [] }

theorem u82 : Upper (D 6) (R 6) [6,40,192,80,258,4,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b82
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 196 88 274 36 65 160 257), lower := (rows 7 42 196 88 274 36 65 160 256), losses := [] }

theorem u83 : Upper (D 6) (R 6) [6,40,192,80,258,4,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b83
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 304, targets := 66 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(4,1),(4,6)], upper := (rows 7 42 196 88 276 33 66 129 288), lower := (rows 7 42 196 88 276 33 66 129 256), losses := [] }

theorem u84 : Upper (D 6) (R 6) [6,40,192,80,260,1,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b84
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 196 88 276 33 66 160 257), lower := (rows 7 42 196 88 276 33 66 160 256), losses := [] }

theorem u85 : Upper (D 6) (R 6) [6,40,192,80,260,1,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b85
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 272, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 272, targets := 32 }], pairs := [(2,1),(4,0),(4,5)], upper := (rows 7 42 196 88 276 33 96 129 258), lower := (rows 7 42 196 88 276 33 96 129 256), losses := [] }

theorem u86 : Upper (D 6) (R 6) [6,40,192,80,260,1,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b86
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 0, region := 272, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 7 42 196 88 276 33 96 130 257), lower := (rows 7 42 196 88 276 33 96 130 256), losses := [] }

theorem u87 : Upper (D 6) (R 6) [6,40,192,80,260,1,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b87
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 196 328 52 33 66 129 272), lower := (rows 7 42 196 328 52 33 66 129 256), losses := [] }

theorem u88 : Upper (D 6) (R 6) [6,40,192,320,36,1,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b88
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 48, targets := 66 }], pairs := [(4,1),(4,6)], upper := (rows 7 42 196 328 52 33 66 144 257), lower := (rows 7 42 196 328 52 33 66 144 256), losses := [] }

theorem u89 : Upper (D 6) (R 6) [6,40,192,320,36,1,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b89
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 346, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 56 336 36 66 129 264), lower := (rows 7 98 133 56 336 36 66 129 256), losses := [] }

theorem u90 : Upper (D 6) (R 6) [6,96,129,48,320,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b90
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 98 133 56 336 36 66 136 257), lower := (rows 7 98 133 56 336 36 66 136 256), losses := [] }

theorem u91 : Upper (D 6) (R 6) [6,96,129,48,320,4,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b91
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 280, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 140 56 336 33 68 129 258), lower := (rows 7 98 140 56 336 33 68 129 256), losses := [] }

theorem u92 : Upper (D 6) (R 6) [6,96,136,48,320,1,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b92
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 7 98 140 56 336 33 68 130 257), lower := (rows 7 98 140 56 336 33 68 130 256), losses := [] }

theorem u93 : Upper (D 6) (R 6) [6,96,136,48,320,1,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b93
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 42 88 96 68 144 288), lower := (rows 7 131 261 42 88 96 68 144 256), losses := [] }

theorem u94 : Upper (D 6) (R 6) [6,129,257,34,72,64,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b94
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 341, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 131 261 42 88 96 68 160 272), lower := (rows 7 131 261 42 88 96 68 160 256), losses := [] }

theorem u95 : Upper (D 6) (R 6) [6,129,257,34,72,64,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b95
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 327, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 261 56 88 34 68 160 320), lower := (rows 7 131 261 56 88 34 68 160 256), losses := [] }

theorem u96 : Upper (D 6) (R 6) [6,129,257,48,72,2,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b96
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 261 56 88 34 68 192 288), lower := (rows 7 131 261 56 88 34 68 192 256), losses := [] }

theorem u97 : Upper (D 6) (R 6) [6,129,257,48,72,2,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b97
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 162 324 44 88 33 66 129 272), lower := (rows 7 162 324 44 88 33 66 129 256), losses := [] }

theorem u98 : Upper (D 6) (R 6) [6,160,320,36,72,1,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b98
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 210, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 162 324 44 88 33 66 144 257), lower := (rows 7 162 324 44 88 33 66 144 256), losses := [] }

theorem u99 : Upper (D 6) (R 6) [6,160,320,36,72,1,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b99
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 139, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 200 336 36 68 130 288), lower := (rows 11 19 37 200 336 36 68 130 256), losses := [] }

theorem u100 : Upper (D 6) (R 6) [10,17,33,192,320,4,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b100
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 275, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 200 336 36 68 160 258), lower := (rows 11 19 37 200 336 36 68 160 256), losses := [] }

theorem u101 : Upper (D 6) (R 6) [10,17,33,192,320,4,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b101
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 139, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 200 336 36 96 130 260), lower := (rows 11 19 37 200 336 36 96 130 256), losses := [] }

theorem u102 : Upper (D 6) (R 6) [10,17,33,192,320,4,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b102
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 275, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 200 336 36 96 132 258), lower := (rows 11 19 37 200 336 36 96 132 256), losses := [] }

theorem u103 : Upper (D 6) (R 6) [10,17,33,192,320,4,32,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b103
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 140 304 36 65 130 320), lower := (rows 11 19 100 140 304 36 65 130 256), losses := [] }

theorem u104 : Upper (D 6) (R 6) [10,17,96,132,288,4,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b104
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 100 140 304 36 65 192 258), lower := (rows 11 19 100 140 304 36 65 192 256), losses := [] }

theorem u105 : Upper (D 6) (R 6) [10,17,96,132,288,4,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b105
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 140 304 36 66 129 320), lower := (rows 11 19 100 140 304 36 66 129 256), losses := [] }

theorem u106 : Upper (D 6) (R 6) [10,17,96,132,288,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b106
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 100 140 304 36 66 192 257), lower := (rows 11 19 100 140 304 36 66 192 256), losses := [] }

theorem u107 : Upper (D 6) (R 6) [10,17,96,132,288,4,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b107
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 22 38 104 208 33 320 129 260), lower := (rows 11 22 38 104 208 33 320 129 256), losses := [] }

theorem u108 : Upper (D 6) (R 6) [10,20,34,96,192,1,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b108
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 150, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 22 38 104 208 33 320 132 257), lower := (rows 11 22 38 104 208 33 320 132 256), losses := [] }

theorem u109 : Upper (D 6) (R 6) [10,20,34,96,192,1,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b109
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 200 336 33 96 129 260), lower := (rows 11 22 38 200 336 33 96 129 256), losses := [] }

theorem u110 : Upper (D 6) (R 6) [10,20,34,192,320,1,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b110
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(4,1),(4,2)], upper := (rows 11 22 38 200 336 33 96 132 257), lower := (rows 11 22 38 200 336 33 96 132 256), losses := [] }

theorem u111 : Upper (D 6) (R 6) [10,20,34,192,320,1,32,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b111
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 339, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 133 44 273 96 66 160 320), lower := (rows 11 22 133 44 273 96 66 160 256), losses := [] }

theorem u112 : Upper (D 6) (R 6) [10,20,129,36,257,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b112
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 133 44 273 96 66 192 288), lower := (rows 11 22 133 44 273 96 66 192 256), losses := [] }

theorem u113 : Upper (D 6) (R 6) [10,20,129,36,257,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b113
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 22 200 336 36 96 129 260), lower := (rows 11 35 22 200 336 36 96 129 256), losses := [] }

theorem u114 : Upper (D 6) (R 6) [10,33,18,192,320,4,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b114
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 232, targets := 3 },{ cop := 1, region := 336, targets := 2 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 35 22 200 336 36 96 132 257), lower := (rows 11 35 22 200 336 36 96 132 256), losses := [] }

theorem u115 : Upper (D 6) (R 6) [10,33,18,192,320,4,32,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b115
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 140 276 96 65 130 320), lower := (rows 11 35 52 140 276 96 65 130 256), losses := [] }

theorem u116 : Upper (D 6) (R 6) [10,33,48,132,260,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b116
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 140 276 96 65 192 258), lower := (rows 11 35 52 140 276 96 65 192 256), losses := [] }

theorem u117 : Upper (D 6) (R 6) [10,33,48,132,260,64,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b117
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 140 276 96 66 129 320), lower := (rows 11 35 52 140 276 96 66 129 256), losses := [] }

theorem u118 : Upper (D 6) (R 6) [10,33,48,132,260,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b118
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 276, targets := 2 },{ cop := 1, region := 276, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 35 52 140 276 96 66 192 257), lower := (rows 11 35 52 140 276 96 66 192 256), losses := [] }

theorem u119 : Upper (D 6) (R 6) [10,33,48,132,260,64,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b119
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P06
