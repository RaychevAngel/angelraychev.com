import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 9, camps := [], pairs := [(3,0)], upper := (rows 7 35 69 56 336 160 192 137 265), lower := (rows 7 35 69 56 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 6 98 100 120 376 224 224 224 256) }] }

theorem u60 : Upper (D 3) (R 3) [6,33,65,48,320,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b60
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 69 152 304 160 65 200 328), lower := (rows 7 35 69 152 304 160 65 128 256), losses := [] }

theorem u61 : Upper (D 3) (R 3) [6,33,65,144,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b61
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 35 69 152 304 160 72 193 321), lower := (rows 7 35 69 152 304 160 72 128 256), losses := [] }

theorem u62 : Upper (D 3) (R 3) [6,33,65,144,288,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b62
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 76 265 112 160 65 144 400), lower := (rows 7 35 76 265 112 160 65 128 256), losses := [] }

theorem u63 : Upper (D 3) (R 3) [6,33,72,257,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b63
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 76 265 112 160 80 129 385), lower := (rows 7 35 76 265 112 160 80 128 256), losses := [] }

theorem u64 : Upper (D 3) (R 3) [6,33,72,257,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b64
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 265 112 160 192 145 273), lower := (rows 7 35 76 265 112 160 192 128 256), losses := [] }

theorem u65 : Upper (D 3) (R 3) [6,33,72,257,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b65
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 76 265 208 160 65 176 304), lower := (rows 7 35 76 265 208 160 65 128 256), losses := [] }

theorem u66 : Upper (D 3) (R 3) [6,33,72,257,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b66
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 76 265 208 160 80 161 289), lower := (rows 7 35 76 265 208 160 80 128 256), losses := [] }

theorem u67 : Upper (D 3) (R 3) [6,33,72,257,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b67
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 265 208 160 96 145 273), lower := (rows 7 35 76 265 208 160 96 128 256), losses := [] }

theorem u68 : Upper (D 3) (R 3) [6,33,72,257,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b68
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 261 88 176 96 65 136 392), lower := (rows 7 35 261 88 176 96 65 128 256), losses := [] }

theorem u69 : Upper (D 3) (R 3) [6,33,257,80,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b69
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 261 88 176 96 72 129 385), lower := (rows 7 35 261 88 176 96 72 128 256), losses := [] }

theorem u70 : Upper (D 3) (R 3) [6,33,257,80,160,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b70
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 261 88 176 96 192 137 265), lower := (rows 7 35 261 88 176 96 192 128 256), losses := [] }

theorem u71 : Upper (D 3) (R 3) [6,33,257,80,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b71
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 268 73 112 160 65 144 400), lower := (rows 7 35 268 73 112 160 65 128 256), losses := [] }

theorem u72 : Upper (D 3) (R 3) [6,33,264,65,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b72
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 268 73 112 160 80 129 385), lower := (rows 7 35 268 73 112 160 80 128 256), losses := [] }

theorem u73 : Upper (D 3) (R 3) [6,33,264,65,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b73
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 268 73 112 160 192 145 273), lower := (rows 7 35 268 73 112 160 192 128 256), losses := [] }

theorem u74 : Upper (D 3) (R 3) [6,33,264,65,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b74
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 268 73 208 160 65 176 304), lower := (rows 7 35 268 73 208 160 65 128 256), losses := [] }

theorem u75 : Upper (D 3) (R 3) [6,33,264,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b75
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 268 73 208 160 80 161 289), lower := (rows 7 35 268 73 208 160 80 128 256), losses := [] }

theorem u76 : Upper (D 3) (R 3) [6,33,264,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b76
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 268 73 208 160 96 145 273), lower := (rows 7 35 268 73 208 160 96 128 256), losses := [] }

theorem u77 : Upper (D 3) (R 3) [6,33,264,65,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b77
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 324 104 152 160 65 145 273), lower := (rows 7 35 324 104 152 160 65 128 256), losses := [] }

theorem u78 : Upper (D 3) (R 3) [6,33,320,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b78
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 7 35 324 104 152 160 80 129 257), lower := (rows 7 35 324 104 152 160 80 128 256), losses := [] }

theorem u79 : Upper (D 3) (R 3) [6,33,320,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b79
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 84 137 273 96 65 160 416), lower := (rows 7 42 84 137 273 96 65 128 256), losses := [] }

theorem u80 : Upper (D 3) (R 3) [6,40,80,129,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b80
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 84 137 273 96 96 129 385), lower := (rows 7 42 84 137 273 96 96 128 256), losses := [] }

theorem u81 : Upper (D 3) (R 3) [6,40,80,129,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b81
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 137 273 96 192 161 289), lower := (rows 7 42 84 137 273 96 192 128 256), losses := [] }

theorem u82 : Upper (D 3) (R 3) [6,40,80,129,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b82
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 261 73 112 160 65 144 400), lower := (rows 7 42 261 73 112 160 65 128 256), losses := [] }

theorem u83 : Upper (D 3) (R 3) [6,40,257,65,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b83
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 261 73 112 160 80 129 385), lower := (rows 7 42 261 73 112 160 80 128 256), losses := [] }

theorem u84 : Upper (D 3) (R 3) [6,40,257,65,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b84
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 73 112 160 192 145 273), lower := (rows 7 42 261 73 112 160 192 128 256), losses := [] }

theorem u85 : Upper (D 3) (R 3) [6,40,257,65,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b85
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 7 42 261 73 145 160 80 224 352), lower := (rows 7 42 261 73 145 160 80 128 256), losses := [] }

theorem u86 : Upper (D 3) (R 3) [6,40,257,65,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b86
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 261 73 145 160 96 208 336), lower := (rows 7 42 261 73 145 160 96 128 256), losses := [] }

theorem u87 : Upper (D 3) (R 3) [6,40,257,65,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b87
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 261 73 208 160 65 176 304), lower := (rows 7 42 261 73 208 160 65 128 256), losses := [] }

theorem u88 : Upper (D 3) (R 3) [6,40,257,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b88
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 261 73 208 160 80 161 289), lower := (rows 7 42 261 73 208 160 80 128 256), losses := [] }

theorem u89 : Upper (D 3) (R 3) [6,40,257,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b89
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 261 73 208 160 96 145 273), lower := (rows 7 42 261 73 208 160 96 128 256), losses := [] }

theorem u90 : Upper (D 3) (R 3) [6,40,257,65,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b90
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 138, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 200 112 33 65 144 400), lower := (rows 7 42 261 200 112 33 65 128 256), losses := [] }

theorem u91 : Upper (D 3) (R 3) [6,40,257,192,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b91
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 261 200 112 33 80 129 385), lower := (rows 7 42 261 200 112 33 80 128 256), losses := [] }

theorem u92 : Upper (D 3) (R 3) [6,40,257,192,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b92
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 200 112 33 192 145 273), lower := (rows 7 42 261 200 112 33 192 128 256), losses := [] }

theorem u93 : Upper (D 3) (R 3) [6,40,257,192,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b93
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 276 73 145 160 65 224 352), lower := (rows 7 42 276 73 145 160 65 128 256), losses := [] }

theorem u94 : Upper (D 3) (R 3) [6,40,272,65,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b94
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 276 73 145 160 96 193 321), lower := (rows 7 42 276 73 145 160 96 128 256), losses := [] }

theorem u95 : Upper (D 3) (R 3) [6,40,272,65,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b95
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 324 137 176 96 65 145 273), lower := (rows 7 42 324 137 176 96 65 128 256), losses := [] }

theorem u96 : Upper (D 3) (R 3) [6,40,320,129,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b96
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 7 42 324 137 176 96 80 129 257), lower := (rows 7 42 324 137 176 96 80 128 256), losses := [] }

theorem u97 : Upper (D 3) (R 3) [6,40,320,129,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b97
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 56 208 33 65 136 392), lower := (rows 7 98 261 56 208 33 65 128 256), losses := [] }

theorem u98 : Upper (D 3) (R 3) [6,96,257,48,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b98
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 261 56 208 33 72 129 385), lower := (rows 7 98 261 56 208 33 72 128 256), losses := [] }

theorem u99 : Upper (D 3) (R 3) [6,96,257,48,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b99
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 56 208 33 192 137 265), lower := (rows 7 98 261 56 208 33 192 128 256), losses := [] }

theorem u100 : Upper (D 3) (R 3) [6,96,257,48,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 168 208 33 65 152 280), lower := (rows 7 98 261 168 208 33 65 128 256), losses := [] }

theorem u101 : Upper (D 3) (R 3) [6,96,257,160,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b101
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 98 261 168 208 33 72 145 273), lower := (rows 7 98 261 168 208 33 72 128 256), losses := [] }

theorem u102 : Upper (D 3) (R 3) [6,96,257,160,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 261 168 208 33 80 137 265), lower := (rows 7 98 261 168 208 33 80 128 256), losses := [] }

theorem u103 : Upper (D 3) (R 3) [6,96,257,160,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b103
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 388 56 208 33 65 137 265), lower := (rows 7 98 388 56 208 33 65 128 256), losses := [] }

theorem u104 : Upper (D 3) (R 3) [6,96,384,48,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b104
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 7 98 388 56 208 33 72 129 257), lower := (rows 7 98 388 56 208 33 72 128 256), losses := [] }

theorem u105 : Upper (D 3) (R 3) [6,96,384,48,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 73 273 160 96 192 448), lower := (rows 35 7 28 73 273 160 96 128 256), losses := [] }

theorem u106 : Upper (D 3) (R 3) [34,5,24,65,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 96, camps := [], pairs := [(1,5)], upper := (rows 35 7 28 73 273 160 192 224 352), lower := (rows 35 7 28 73 273 160 192 128 256), losses := [{ target := 5, region := (rows 1 18 20 9 16 0 224 128 256), good := (rows 75 15 30 73 287 192 192 192 256) }] }

theorem u107 : Upper (D 3) (R 3) [34,5,24,65,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 265 112 160 65 144 400), lower := (rows 35 7 76 265 112 160 65 128 256), losses := [] }

theorem u108 : Upper (D 3) (R 3) [34,5,72,257,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b108
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 76 265 112 160 80 129 385), lower := (rows 35 7 76 265 112 160 80 128 256), losses := [] }

theorem u109 : Upper (D 3) (R 3) [34,5,72,257,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b109
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 265 112 160 192 145 273), lower := (rows 35 7 76 265 112 160 192 128 256), losses := [] }

theorem u110 : Upper (D 3) (R 3) [34,5,72,257,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b110
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 7 76 265 145 160 80 224 352), lower := (rows 35 7 76 265 145 160 80 128 256), losses := [] }

theorem u111 : Upper (D 3) (R 3) [34,5,72,257,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b111
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 80, camps := [], pairs := [(2,0)], upper := (rows 35 7 76 265 145 160 96 208 336), lower := (rows 35 7 76 265 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 241 144 272), good := (rows 98 70 76 332 496 224 96 224 256) }] }

theorem u112 : Upper (D 3) (R 3) [34,5,72,257,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b112
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 265 208 160 65 176 304), lower := (rows 35 7 76 265 208 160 65 128 256), losses := [] }

theorem u113 : Upper (D 3) (R 3) [34,5,72,257,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b113
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 76 265 208 160 80 161 289), lower := (rows 35 7 76 265 208 160 80 128 256), losses := [] }

theorem u114 : Upper (D 3) (R 3) [34,5,72,257,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b114
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 76 265 208 160 96 145 273), lower := (rows 35 7 76 265 208 160 96 128 256), losses := [] }

theorem u115 : Upper (D 3) (R 3) [34,5,72,257,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b115
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 268 73 112 160 65 144 400), lower := (rows 35 7 268 73 112 160 65 128 256), losses := [] }

theorem u116 : Upper (D 3) (R 3) [34,5,264,65,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b116
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 268 73 112 160 80 129 385), lower := (rows 35 7 268 73 112 160 80 128 256), losses := [] }

theorem u117 : Upper (D 3) (R 3) [34,5,264,65,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 268 73 112 160 192 145 273), lower := (rows 35 7 268 73 112 160 192 128 256), losses := [] }

theorem u118 : Upper (D 3) (R 3) [34,5,264,65,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b118
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 7 268 73 145 160 80 224 352), lower := (rows 35 7 268 73 145 160 80 128 256), losses := [] }

theorem u119 : Upper (D 3) (R 3) [34,5,264,65,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b119
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P03
