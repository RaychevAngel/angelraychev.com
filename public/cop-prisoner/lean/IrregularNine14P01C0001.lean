import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 428, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 388 138 18 96 80 168 296), lower := (rows 53 67 388 138 18 96 80 128 256), losses := [] }

theorem u60 : Upper (D 1) (R 1) [52,65,384,130,2,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b60
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 53 67 388 138 18 96 96 152 280), lower := (rows 53 67 388 138 18 96 96 128 256), losses := [] }

theorem u61 : Upper (D 1) (R 1) [52,65,384,130,2,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b61
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 388 152 18 96 66 168 296), lower := (rows 53 67 388 152 18 96 66 128 256), losses := [] }

theorem u62 : Upper (D 1) (R 1) [52,65,384,144,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b62
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 67 388 152 18 96 72 162 290), lower := (rows 53 67 388 152 18 96 72 128 256), losses := [] }

theorem u63 : Upper (D 1) (R 1) [52,65,384,144,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b63
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 53 67 388 152 18 96 96 138 266), lower := (rows 53 67 388 152 18 96 96 128 256), losses := [] }

theorem u64 : Upper (D 1) (R 1) [52,65,384,144,2,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b64
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 388 152 80 34 66 168 296), lower := (rows 53 67 388 152 80 34 66 128 256), losses := [] }

theorem u65 : Upper (D 1) (R 1) [52,65,384,144,64,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b65
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 67 388 152 80 34 72 162 290), lower := (rows 53 67 388 152 80 34 72 128 256), losses := [] }

theorem u66 : Upper (D 1) (R 1) [52,65,384,144,64,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b66
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 53 67 388 152 80 34 96 138 266), lower := (rows 53 67 388 152 80 34 96 128 256), losses := [] }

theorem u67 : Upper (D 1) (R 1) [52,65,384,144,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b67
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 7 392 80 160 66 176 304), lower := (rows 53 74 7 392 80 160 66 128 256), losses := [] }

theorem u68 : Upper (D 1) (R 1) [52,72,3,384,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b68
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 424, targets := 16 }], pairs := [(3,4)], upper := (rows 53 74 7 392 80 160 80 162 290), lower := (rows 53 74 7 392 80 160 80 128 256), losses := [] }

theorem u69 : Upper (D 1) (R 1) [52,72,3,384,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b69
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 394, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 7 392 80 160 96 146 274), lower := (rows 53 74 7 392 80 160 96 128 256), losses := [] }

theorem u70 : Upper (D 1) (R 1) [52,72,3,384,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b70
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 421, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 261 138 80 160 66 176 304), lower := (rows 53 74 261 138 80 160 66 128 256), losses := [] }

theorem u71 : Upper (D 1) (R 1) [52,72,257,130,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b71
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 168, targets := 16 }], pairs := [(3,4)], upper := (rows 53 74 261 138 80 160 80 162 290), lower := (rows 53 74 261 138 80 160 80 128 256), losses := [] }

theorem u72 : Upper (D 1) (R 1) [52,72,257,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b72
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 138, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 261 138 80 160 96 146 274), lower := (rows 53 74 261 138 80 160 96 128 256), losses := [] }

theorem u73 : Upper (D 1) (R 1) [52,72,257,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b73
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 137 80 160 66 176 304), lower := (rows 53 74 262 137 80 160 66 128 256), losses := [] }

theorem u74 : Upper (D 1) (R 1) [52,72,258,129,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b74
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 420, targets := 16 }], pairs := [(2,4)], upper := (rows 53 74 262 137 80 160 80 162 290), lower := (rows 53 74 262 137 80 160 80 128 256), losses := [] }

theorem u75 : Upper (D 1) (R 1) [52,72,258,129,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b75
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 276, targets := 32 }], pairs := [(2,5)], upper := (rows 53 74 262 137 80 160 96 146 274), lower := (rows 53 74 262 137 80 160 96 128 256), losses := [] }

theorem u76 : Upper (D 1) (R 1) [52,72,258,129,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b76
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 74 262 152 80 160 65 162 290), lower := (rows 53 74 262 152 80 160 65 128 256), losses := [] }

theorem u77 : Upper (D 1) (R 1) [52,72,258,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b77
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 152 80 160 66 161 289), lower := (rows 53 74 262 152 80 160 66 128 256), losses := [] }

theorem u78 : Upper (D 1) (R 1) [52,72,258,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b78
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 262 152 80 160 96 131 259), lower := (rows 53 74 262 152 80 160 96 128 256), losses := [] }

theorem u79 : Upper (D 1) (R 1) [52,72,258,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b79
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 74 324 152 18 160 65 162 290), lower := (rows 53 74 324 152 18 160 65 128 256), losses := [] }

theorem u80 : Upper (D 1) (R 1) [52,72,320,144,2,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b80
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 324 152 18 160 66 161 289), lower := (rows 53 74 324 152 18 160 66 128 256), losses := [] }

theorem u81 : Upper (D 1) (R 1) [52,72,320,144,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b81
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 324 152 18 160 96 131 259), lower := (rows 53 74 324 152 18 160 96 128 256), losses := [] }

theorem u82 : Upper (D 1) (R 1) [52,72,320,144,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b82
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 74 388 152 18 96 65 162 290), lower := (rows 53 74 388 152 18 96 65 128 256), losses := [] }

theorem u83 : Upper (D 1) (R 1) [52,72,384,144,2,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b83
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 388, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 388 152 18 96 66 161 289), lower := (rows 53 74 388 152 18 96 66 128 256), losses := [] }

theorem u84 : Upper (D 1) (R 1) [52,72,384,144,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b84
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 388 152 18 96 96 131 259), lower := (rows 53 74 388 152 18 96 96 128 256), losses := [] }

theorem u85 : Upper (D 1) (R 1) [52,72,384,144,2,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b85
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 74 388 152 80 34 65 162 290), lower := (rows 53 74 388 152 80 34 65 128 256), losses := [] }

theorem u86 : Upper (D 1) (R 1) [52,72,384,144,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b86
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 388, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 388 152 80 34 66 161 289), lower := (rows 53 74 388 152 80 34 66 128 256), losses := [] }

theorem u87 : Upper (D 1) (R 1) [52,72,384,144,64,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b87
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 388 152 80 34 96 131 259), lower := (rows 53 74 388 152 80 34 96 128 256), losses := [] }

theorem u88 : Upper (D 1) (R 1) [52,72,384,144,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b88
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 137 144 96 66 168 296), lower := (rows 53 82 262 137 144 96 66 128 256), losses := [] }

theorem u89 : Upper (D 1) (R 1) [52,80,258,129,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b89
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 82 262 137 144 96 72 162 290), lower := (rows 53 82 262 137 144 96 72 128 256), losses := [] }

theorem u90 : Upper (D 1) (R 1) [52,80,258,129,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b90
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 262 137 144 96 96 138 266), lower := (rows 53 82 262 137 144 96 96 128 256), losses := [] }

theorem u91 : Upper (D 1) (R 1) [52,80,258,129,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b91
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 53 82 262 138 144 96 65 168 296), lower := (rows 53 82 262 138 144 96 65 128 256), losses := [] }

theorem u92 : Upper (D 1) (R 1) [52,80,258,130,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b92
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 53 82 262 138 144 96 72 161 289), lower := (rows 53 82 262 138 144 96 72 128 256), losses := [] }

theorem u93 : Upper (D 1) (R 1) [52,80,258,130,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b93
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 262 138 144 96 96 137 265), lower := (rows 53 82 262 138 144 96 96 128 256), losses := [] }

theorem u94 : Upper (D 1) (R 1) [52,80,258,130,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b94
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 53 82 262 168 144 96 65 138 266), lower := (rows 53 82 262 168 144 96 65 128 256), losses := [] }

theorem u95 : Upper (D 1) (R 1) [52,80,258,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b95
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 168 144 96 66 137 265), lower := (rows 53 82 262 168 144 96 66 128 256), losses := [] }

theorem u96 : Upper (D 1) (R 1) [52,80,258,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b96
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 53 82 262 168 144 96 72 131 259), lower := (rows 53 82 262 168 144 96 72 128 256), losses := [] }

theorem u97 : Upper (D 1) (R 1) [52,80,258,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b97
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 324 137 144 34 66 168 296), lower := (rows 53 82 324 137 144 34 66 128 256), losses := [] }

theorem u98 : Upper (D 1) (R 1) [52,80,320,129,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b98
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 82 324 137 144 34 72 162 290), lower := (rows 53 82 324 137 144 34 72 128 256), losses := [] }

theorem u99 : Upper (D 1) (R 1) [52,80,320,129,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b99
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 324 137 144 34 96 138 266), lower := (rows 53 82 324 137 144 34 96 128 256), losses := [] }

theorem u100 : Upper (D 1) (R 1) [52,80,320,129,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 53 82 324 138 144 34 65 168 296), lower := (rows 53 82 324 138 144 34 65 128 256), losses := [] }

theorem u101 : Upper (D 1) (R 1) [52,80,320,130,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 53 82 324 138 144 34 72 161 289), lower := (rows 53 82 324 138 144 34 72 128 256), losses := [] }

theorem u102 : Upper (D 1) (R 1) [52,80,320,130,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b102
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 324 138 144 34 96 137 265), lower := (rows 53 82 324 138 144 34 96 128 256), losses := [] }

theorem u103 : Upper (D 1) (R 1) [52,80,320,130,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 53 82 324 168 144 34 65 138 266), lower := (rows 53 82 324 168 144 34 65 128 256), losses := [] }

theorem u104 : Upper (D 1) (R 1) [52,80,320,160,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 324 168 144 34 66 137 265), lower := (rows 53 82 324 168 144 34 66 128 256), losses := [] }

theorem u105 : Upper (D 1) (R 1) [52,80,320,160,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 53 82 324 168 144 34 72 131 259), lower := (rows 53 82 324 168 144 34 72 128 256), losses := [] }

theorem u106 : Upper (D 1) (R 1) [52,80,320,160,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 13 328 18 160 66 176 304), lower := (rows 53 194 13 328 18 160 66 128 256), losses := [] }

theorem u107 : Upper (D 1) (R 1) [52,192,9,320,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 13 328 18 160 80 162 290), lower := (rows 53 194 13 328 18 160 80 128 256), losses := [] }

theorem u108 : Upper (D 1) (R 1) [52,192,9,320,2,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 146, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 13 328 18 160 96 146 274), lower := (rows 53 194 13 328 18 160 96 128 256), losses := [] }

theorem u109 : Upper (D 1) (R 1) [52,192,9,320,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 268 11 80 160 66 176 304), lower := (rows 53 194 268 11 80 160 66 128 256), losses := [] }

theorem u110 : Upper (D 1) (R 1) [52,192,264,3,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 420, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 268 11 80 160 80 162 290), lower := (rows 53 194 268 11 80 160 80 128 256), losses := [] }

theorem u111 : Upper (D 1) (R 1) [52,192,264,3,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 268 11 80 160 96 146 274), lower := (rows 53 194 268 11 80 160 96 128 256), losses := [] }

theorem u112 : Upper (D 1) (R 1) [52,192,264,3,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 268 73 18 160 66 176 304), lower := (rows 53 194 268 73 18 160 66 128 256), losses := [] }

theorem u113 : Upper (D 1) (R 1) [52,192,264,65,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 268 73 18 160 80 162 290), lower := (rows 53 194 268 73 18 160 80 128 256), losses := [] }

theorem u114 : Upper (D 1) (R 1) [52,192,264,65,2,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 268 73 18 160 96 146 274), lower := (rows 53 194 268 73 18 160 96 128 256), losses := [] }

theorem u115 : Upper (D 1) (R 1) [52,192,264,65,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 53 194 324 11 18 160 72 176 304), lower := (rows 53 194 324 11 18 160 72 128 256), losses := [] }

theorem u116 : Upper (D 1) (R 1) [52,192,320,3,2,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 82, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 324 11 18 160 80 168 296), lower := (rows 53 194 324 11 18 160 80 128 256), losses := [] }

theorem u117 : Upper (D 1) (R 1) [52,192,320,3,2,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 324 11 18 160 96 152 280), lower := (rows 53 194 324 11 18 160 96 128 256), losses := [] }

theorem u118 : Upper (D 1) (R 1) [52,192,320,3,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 7 200 80 160 66 176 304), lower := (rows 53 266 7 200 80 160 66 128 256), losses := [] }

theorem u119 : Upper (D 1) (R 1) [52,264,3,192,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b119
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P01
