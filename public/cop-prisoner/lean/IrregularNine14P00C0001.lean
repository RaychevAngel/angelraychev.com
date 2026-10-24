import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 84 137 144 33 96 140 268), lower := (rows 51 322 84 137 144 33 96 128 256), losses := [] }

theorem u60 : Upper (D 0) (R 0) [50,320,80,129,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b60
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 84 140 17 160 65 168 296), lower := (rows 51 322 84 140 17 160 65 128 256), losses := [] }

theorem u61 : Upper (D 0) (R 0) [50,320,80,132,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b61
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 51 322 84 140 17 160 72 161 289), lower := (rows 51 322 84 140 17 160 72 128 256), losses := [] }

theorem u62 : Upper (D 0) (R 0) [50,320,80,132,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b62
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 84 140 17 160 96 137 265), lower := (rows 51 322 84 140 17 160 96 128 256), losses := [] }

theorem u63 : Upper (D 0) (R 0) [50,320,80,132,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b63
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 84 140 144 33 65 168 296), lower := (rows 51 322 84 140 144 33 65 128 256), losses := [] }

theorem u64 : Upper (D 0) (R 0) [50,320,80,132,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b64
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 51 322 84 140 144 33 72 161 289), lower := (rows 51 322 84 140 144 33 72 128 256), losses := [] }

theorem u65 : Upper (D 0) (R 0) [50,320,80,132,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b65
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 84 140 144 33 96 137 265), lower := (rows 51 322 84 140 144 33 96 128 256), losses := [] }

theorem u66 : Upper (D 0) (R 0) [50,320,80,132,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b66
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 84 168 144 33 65 140 268), lower := (rows 51 322 84 168 144 33 65 128 256), losses := [] }

theorem u67 : Upper (D 0) (R 0) [50,320,80,160,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b67
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 51 322 84 168 144 33 68 137 265), lower := (rows 51 322 84 168 144 33 68 128 256), losses := [] }

theorem u68 : Upper (D 0) (R 0) [50,320,80,160,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b68
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 51 322 84 168 144 33 72 133 261), lower := (rows 51 322 84 168 144 33 72 128 256), losses := [] }

theorem u69 : Upper (D 0) (R 0) [50,320,80,160,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b69
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 7 140 280 17 34 192 224 352), lower := (rows 113 7 140 280 17 34 192 128 256), losses := [] }

theorem u70 : Upper (D 0) (R 0) [112,5,136,272,1,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b70
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 140 280 17 96 192 162 290), lower := (rows 113 7 140 280 17 96 192 128 256), losses := [] }

theorem u71 : Upper (D 0) (R 0) [112,5,136,272,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b71
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 7 140 280 144 33 66 224 352), lower := (rows 113 7 140 280 144 33 66 128 256), losses := [] }

theorem u72 : Upper (D 0) (R 0) [112,5,136,272,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b72
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 280 144 33 96 194 322), lower := (rows 113 7 140 280 144 33 96 128 256), losses := [] }

theorem u73 : Upper (D 0) (R 0) [112,5,136,272,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b73
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 7 268 152 17 34 192 224 352), lower := (rows 113 7 268 152 17 34 192 128 256), losses := [] }

theorem u74 : Upper (D 0) (R 0) [112,5,264,144,1,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b74
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 268 152 17 96 192 162 290), lower := (rows 113 7 268 152 17 96 192 128 256), losses := [] }

theorem u75 : Upper (D 0) (R 0) [112,5,264,144,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b75
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 14 133 280 17 34 192 224 352), lower := (rows 113 14 133 280 17 34 192 128 256), losses := [] }

theorem u76 : Upper (D 0) (R 0) [112,12,129,272,1,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b76
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 133 280 17 96 192 162 290), lower := (rows 113 14 133 280 17 96 192 128 256), losses := [] }

theorem u77 : Upper (D 0) (R 0) [112,12,129,272,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b77
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 14 133 280 144 33 66 224 352), lower := (rows 113 14 133 280 144 33 66 128 256), losses := [] }

theorem u78 : Upper (D 0) (R 0) [112,12,129,272,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b78
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 280 144 33 96 194 322), lower := (rows 113 14 133 280 144 33 96 128 256), losses := [] }

theorem u79 : Upper (D 0) (R 0) [112,12,129,272,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b79
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 14 148 265 17 34 192 224 352), lower := (rows 113 14 148 265 17 34 192 128 256), losses := [] }

theorem u80 : Upper (D 0) (R 0) [112,12,144,257,1,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b80
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 148 265 17 96 192 162 290), lower := (rows 113 14 148 265 17 96 192 128 256), losses := [] }

theorem u81 : Upper (D 0) (R 0) [112,12,144,257,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b81
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 14 148 296 17 160 65 194 322), lower := (rows 113 14 148 296 17 160 65 128 256), losses := [] }

theorem u82 : Upper (D 0) (R 0) [112,12,144,288,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b82
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 14 148 296 17 160 66 193 321), lower := (rows 113 14 148 296 17 160 66 128 256), losses := [] }

theorem u83 : Upper (D 0) (R 0) [112,12,144,288,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b83
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 44 328 17 160 65 130 386), lower := (rows 113 22 44 328 17 160 65 128 256), losses := [] }

theorem u84 : Upper (D 0) (R 0) [112,20,40,320,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b84
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 113 22 44 328 17 160 66 129 385), lower := (rows 113 22 44 328 17 160 66 128 256), losses := [] }

theorem u85 : Upper (D 0) (R 0) [112,20,40,320,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b85
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 328 17 160 192 131 259), lower := (rows 113 22 44 328 17 160 192 128 256), losses := [] }

theorem u86 : Upper (D 0) (R 0) [112,20,40,320,1,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b86
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 44 328 144 33 65 130 386), lower := (rows 113 22 44 328 144 33 65 128 256), losses := [] }

theorem u87 : Upper (D 0) (R 0) [112,20,40,320,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b87
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 113 22 44 328 144 33 66 129 385), lower := (rows 113 22 44 328 144 33 66 128 256), losses := [] }

theorem u88 : Upper (D 0) (R 0) [112,20,40,320,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b88
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 328 144 33 192 131 259), lower := (rows 113 22 44 328 144 33 192 128 256), losses := [] }

theorem u89 : Upper (D 0) (R 0) [112,20,40,320,128,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b89
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 140 296 17 160 65 194 322), lower := (rows 113 22 140 296 17 160 65 128 256), losses := [] }

theorem u90 : Upper (D 0) (R 0) [112,20,136,288,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b90
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 22 140 296 17 160 66 193 321), lower := (rows 113 22 140 296 17 160 66 128 256), losses := [] }

theorem u91 : Upper (D 0) (R 0) [112,20,136,288,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b91
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 113 22 292 137 17 160 66 200 328), lower := (rows 113 22 292 137 17 160 66 128 256), losses := [] }

theorem u92 : Upper (D 0) (R 0) [112,20,288,129,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b92
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 22 292 137 17 160 72 194 322), lower := (rows 113 22 292 137 17 160 72 128 256), losses := [] }

theorem u93 : Upper (D 0) (R 0) [112,20,288,129,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b93
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 113 22 292 137 144 33 66 200 328), lower := (rows 113 22 292 137 144 33 66 128 256), losses := [] }

theorem u94 : Upper (D 0) (R 0) [112,20,288,129,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b94
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 22 292 137 144 33 72 194 322), lower := (rows 113 22 292 137 144 33 72 128 256), losses := [] }

theorem u95 : Upper (D 0) (R 0) [112,20,288,129,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b95
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 292 138 17 160 65 200 328), lower := (rows 113 22 292 138 17 160 65 128 256), losses := [] }

theorem u96 : Upper (D 0) (R 0) [112,20,288,130,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b96
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 22 292 138 17 160 72 193 321), lower := (rows 113 22 292 138 17 160 72 128 256), losses := [] }

theorem u97 : Upper (D 0) (R 0) [112,20,288,130,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b97
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 292 138 144 33 65 200 328), lower := (rows 113 22 292 138 144 33 65 128 256), losses := [] }

theorem u98 : Upper (D 0) (R 0) [112,20,288,130,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b98
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 22 292 138 144 33 72 193 321), lower := (rows 113 22 292 138 144 33 72 128 256), losses := [] }

theorem u99 : Upper (D 0) (R 0) [112,20,288,130,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b99
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 292 200 17 160 65 138 266), lower := (rows 113 22 292 200 17 160 65 128 256), losses := [] }

theorem u100 : Upper (D 0) (R 0) [112,20,288,192,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b100
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 113 22 292 200 17 160 66 137 265), lower := (rows 113 22 292 200 17 160 66 128 256), losses := [] }

theorem u101 : Upper (D 0) (R 0) [112,20,288,192,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b101
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 22 292 200 17 160 72 131 259), lower := (rows 113 22 292 200 17 160 72 128 256), losses := [] }

theorem u102 : Upper (D 0) (R 0) [112,20,288,192,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b102
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 292 200 144 33 65 138 266), lower := (rows 113 22 292 200 144 33 65 128 256), losses := [] }

theorem u103 : Upper (D 0) (R 0) [112,20,288,192,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b103
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 113 22 292 200 144 33 66 137 265), lower := (rows 113 22 292 200 144 33 66 128 256), losses := [] }

theorem u104 : Upper (D 0) (R 0) [112,20,288,192,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b104
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 22 292 200 144 33 72 131 259), lower := (rows 113 22 292 200 144 33 72 128 256), losses := [] }

theorem u105 : Upper (D 0) (R 0) [112,20,288,192,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b105
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 275 35 52 76 80 160 65 136 392), lower := (rows 275 35 52 76 80 160 65 128 256), losses := [] }

theorem u106 : Upper (D 0) (R 0) [274,33,48,68,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b106
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 35 52 76 80 160 72 129 385), lower := (rows 275 35 52 76 80 160 72 128 256), losses := [] }

theorem u107 : Upper (D 0) (R 0) [274,33,48,68,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b107
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 84, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 52 76 80 160 192 137 265), lower := (rows 275 35 52 76 80 160 192 128 256), losses := [] }

theorem u108 : Upper (D 0) (R 0) [274,33,48,68,64,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b108
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 275 35 52 76 144 96 65 136 392), lower := (rows 275 35 52 76 144 96 65 128 256), losses := [] }

theorem u109 : Upper (D 0) (R 0) [274,33,48,68,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b109
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 35 52 76 144 96 72 129 385), lower := (rows 275 35 52 76 144 96 72 128 256), losses := [] }

theorem u110 : Upper (D 0) (R 0) [274,33,48,68,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b110
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 52 76 144 96 192 137 265), lower := (rows 275 35 52 76 144 96 192 128 256), losses := [] }

theorem u111 : Upper (D 0) (R 0) [274,33,48,68,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b111
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 152 80 160 65 164 292), lower := (rows 275 35 76 152 80 160 65 128 256), losses := [] }

theorem u112 : Upper (D 0) (R 0) [274,33,72,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b112
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 275 35 76 152 80 160 68 161 289), lower := (rows 275 35 76 152 80 160 68 128 256), losses := [] }

theorem u113 : Upper (D 0) (R 0) [274,33,72,144,64,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b113
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 92, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 152 80 160 96 133 261), lower := (rows 275 35 76 152 80 160 96 128 256), losses := [] }

theorem u114 : Upper (D 0) (R 0) [274,33,72,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b114
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 168 144 96 65 148 276), lower := (rows 275 35 76 168 144 96 65 128 256), losses := [] }

theorem u115 : Upper (D 0) (R 0) [274,33,72,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b115
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 275 35 76 168 144 96 68 145 273), lower := (rows 275 35 76 168 144 96 68 128 256), losses := [] }

theorem u116 : Upper (D 0) (R 0) [274,33,72,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b116
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 168 144 96 80 133 261), lower := (rows 275 35 76 168 144 96 80 128 256), losses := [] }

theorem u117 : Upper (D 0) (R 0) [274,33,72,160,128,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b117
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 275 35 84 168 144 96 65 140 268), lower := (rows 275 35 84 168 144 96 65 128 256), losses := [] }

theorem u118 : Upper (D 0) (R 0) [274,33,80,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b118
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 275 35 84 168 144 96 68 137 265), lower := (rows 275 35 84 168 144 96 68 128 256), losses := [] }

theorem u119 : Upper (D 0) (R 0) [274,33,80,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b119
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P00
