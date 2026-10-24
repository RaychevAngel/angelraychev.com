import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 139, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 137 400 288 80 224 352), lower := (rows 7 42 100 137 400 288 80 128 256), losses := [] }

theorem u60 : Upper (D 10) (R 10) [6,40,96,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b60 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 137 400 288 96 208 336), lower := (rows 7 42 100 137 400 288 96 128 256), losses := [] }

theorem u61 : Upper (D 10) (R 10) [6,40,96,129,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b61 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 456, targets := 32 },{ cop := 6, region := 292, targets := 128 }], pairs := [(2,7),(3,5)], upper := (rows 7 42 100 152 49 288 192 448 320), lower := (rows 7 42 100 152 49 288 192 128 256), losses := [] }

theorem u62 : Upper (D 10) (R 10) [6,40,96,144,33,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b62 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 152 49 288 320 192 448), lower := (rows 7 42 100 152 49 288 320 128 256), losses := [] }

theorem u63 : Upper (D 10) (R 10) [6,40,96,144,33,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b63 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 336 33 96 384 384), lower := (rows 7 42 100 152 336 33 96 128 256), losses := [] }

theorem u64 : Upper (D 10) (R 10) [6,40,96,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b64 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 152 336 33 192 416 288), lower := (rows 7 42 100 152 336 33 192 128 256), losses := [] }

theorem u65 : Upper (D 10) (R 10) [6,40,96,144,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b65 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 152 336 33 320 160 416), lower := (rows 7 42 100 152 336 33 320 128 256), losses := [] }

theorem u66 : Upper (D 10) (R 10) [6,40,96,144,320,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b66 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 200 176 288 65 400 272), lower := (rows 7 42 100 200 176 288 65 128 256), losses := [] }

theorem u67 : Upper (D 10) (R 10) [6,40,96,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b67 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 200 176 288 80 385 257), lower := (rows 7 42 100 200 176 288 80 128 256), losses := [] }

theorem u68 : Upper (D 10) (R 10) [6,40,96,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b68 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 200 176 288 320 145 273), lower := (rows 7 42 100 200 176 288 320 128 256), losses := [] }

theorem u69 : Upper (D 10) (R 10) [6,40,96,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b69 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 139, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 200 273 288 80 160 416), lower := (rows 7 42 100 200 273 288 80 128 256), losses := [] }

theorem u70 : Upper (D 10) (R 10) [6,40,96,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b70 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 69, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 200 273 288 96 144 400), lower := (rows 7 42 100 200 273 288 96 128 256), losses := [] }

theorem u71 : Upper (D 10) (R 10) [6,40,96,192,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b71 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 100 200 273 288 192 176 304), lower := (rows 7 42 100 200 273 288 192 128 256), losses := [] }

theorem u72 : Upper (D 10) (R 10) [6,40,96,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b72 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 200 400 288 65 176 304), lower := (rows 7 42 100 200 400 288 65 128 256), losses := [] }

theorem u73 : Upper (D 10) (R 10) [6,40,96,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b73 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 139, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 200 400 288 80 161 289), lower := (rows 7 42 100 200 400 288 80 128 256), losses := [] }

theorem u74 : Upper (D 10) (R 10) [6,40,96,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b74 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 200 400 288 96 145 273), lower := (rows 7 42 100 200 400 288 96 128 256), losses := [] }

theorem u75 : Upper (D 10) (R 10) [6,40,96,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b75 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 7 42 100 392 208 33 80 416 288), lower := (rows 7 42 100 392 208 33 80 128 256), losses := [] }

theorem u76 : Upper (D 10) (R 10) [6,40,96,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b76 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 392 208 33 96 400 272), lower := (rows 7 42 100 392 208 33 96 128 256), losses := [] }

theorem u77 : Upper (D 10) (R 10) [6,40,96,384,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b77 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 392 208 33 320 176 304), lower := (rows 7 42 100 392 208 33 320 128 256), losses := [] }

theorem u78 : Upper (D 10) (R 10) [6,40,96,384,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b78 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 196 88 176 288 65 416 288), lower := (rows 7 42 196 88 176 288 65 128 256), losses := [] }

theorem u79 : Upper (D 10) (R 10) [6,40,192,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b79 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 196 88 176 288 96 385 257), lower := (rows 7 42 196 88 176 288 96 128 256), losses := [] }

theorem u80 : Upper (D 10) (R 10) [6,40,192,80,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b80 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(2,5),(4,6)], upper := (rows 7 42 196 88 176 288 320 161 289), lower := (rows 7 42 196 88 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 352 128 256), good := (rows 7 74 196 92 220 320 320 128 320) }] }

theorem u81 : Upper (D 10) (R 10) [6,40,192,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b81 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 88 304 160 65 416 288), lower := (rows 7 42 196 88 304 160 65 128 256), losses := [] }

theorem u82 : Upper (D 10) (R 10) [6,40,192,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b82 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 74, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 42 196 88 304 160 96 385 257), lower := (rows 7 42 196 88 304 160 96 128 256), losses := [] }

theorem u83 : Upper (D 10) (R 10) [6,40,192,80,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b83 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 196 88 304 160 320 161 289), lower := (rows 7 42 196 88 304 160 320 128 256), losses := [] }

theorem u84 : Upper (D 10) (R 10) [6,40,192,80,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b84 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 266, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 280 112 160 65 416 288), lower := (rows 7 42 196 280 112 160 65 128 256), losses := [] }

theorem u85 : Upper (D 10) (R 10) [6,40,192,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b85 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 80, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 42 196 280 112 160 96 385 257), lower := (rows 7 42 196 280 112 160 96 128 256), losses := [] }

theorem u86 : Upper (D 10) (R 10) [6,40,192,272,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b86 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 48, targets := 256 }], pairs := [(4,7),(4,8)], upper := (rows 7 42 196 280 112 160 320 161 289), lower := (rows 7 42 196 280 112 160 320 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 18 32 328 0 256), good := (rows 23 122 68 344 112 32 320 0 320) }] }

theorem u87 : Upper (D 10) (R 10) [6,40,192,272,96,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b87 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 328 304 160 65 176 304), lower := (rows 7 42 196 328 304 160 65 128 256), losses := [] }

theorem u88 : Upper (D 10) (R 10) [6,40,192,320,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b88 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 196 328 304 160 80 161 289), lower := (rows 7 42 196 328 304 160 80 128 256), losses := [] }

theorem u89 : Upper (D 10) (R 10) [6,40,192,320,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b89 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 74, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 42 196 328 304 160 96 145 273), lower := (rows 7 42 196 328 304 160 96 128 256), losses := [] }

theorem u90 : Upper (D 10) (R 10) [6,40,192,320,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b90 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 107, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 148 168 304 96 65 416 288), lower := (rows 7 74 148 168 304 96 65 128 256), losses := [] }

theorem u91 : Upper (D 10) (R 10) [6,72,144,160,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b91 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 107, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 148 168 304 96 96 385 257), lower := (rows 7 74 148 168 304 96 96 128 256), losses := [] }

theorem u92 : Upper (D 10) (R 10) [6,72,144,160,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b92 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(3,8),(4,7)], upper := (rows 7 74 148 168 304 96 320 161 289), lower := (rows 7 74 148 168 304 96 320 128 256), losses := [{ target := 8, region := (rows 1 2 4 9 16 98 64 129 0), good := (rows 175 106 148 168 48 96 96 128 0) }] }

theorem u93 : Upper (D 10) (R 10) [6,72,144,160,288,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b93 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 148 296 336 160 65 160 288), lower := (rows 7 74 148 296 336 160 65 128 256), losses := [] }

theorem u94 : Upper (D 10) (R 10) [6,72,144,288,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b94 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 296 336 160 96 161 289), lower := (rows 7 74 148 296 336 160 96 128 256), losses := [] }

theorem u95 : Upper (D 10) (R 10) [6,72,144,288,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b95 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 41 112 288 80 384 384), lower := (rows 7 74 164 41 112 288 80 128 256), losses := [] }

theorem u96 : Upper (D 10) (R 10) [6,72,160,33,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b96 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 41 112 288 192 400 272), lower := (rows 7 74 164 41 112 288 192 128 256), losses := [] }

theorem u97 : Upper (D 10) (R 10) [6,72,160,33,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b97 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 41 112 288 320 144 400), lower := (rows 7 74 164 41 112 288 320 128 256), losses := [] }

theorem u98 : Upper (D 10) (R 10) [6,72,160,33,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b98 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 41 208 288 80 416 288), lower := (rows 7 74 164 41 208 288 80 128 256), losses := [] }

theorem u99 : Upper (D 10) (R 10) [6,72,160,33,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b99 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 41 208 288 96 400 272), lower := (rows 7 74 164 41 208 288 96 128 256), losses := [] }

theorem u100 : Upper (D 10) (R 10) [6,72,160,33,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b100 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 292, targets := 64 }], pairs := [(1,5),(2,6)], upper := (rows 7 74 164 41 208 288 320 176 304), lower := (rows 7 74 164 41 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 20 0 352 128 256), good := (rows 23 74 212 75 208 320 320 128 320) }] }

theorem u101 : Upper (D 10) (R 10) [6,72,160,33,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b101 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 41 336 288 80 160 416), lower := (rows 7 74 164 41 336 288 80 128 256), losses := [] }

theorem u102 : Upper (D 10) (R 10) [6,72,160,33,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b102 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 74 164 41 336 288 96 144 400), lower := (rows 7 74 164 41 336 288 96 128 256), losses := [] }

theorem u103 : Upper (D 10) (R 10) [6,72,160,33,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b103 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 41 336 288 192 176 304), lower := (rows 7 74 164 41 336 288 192 128 256), losses := [] }

theorem u104 : Upper (D 10) (R 10) [6,72,160,33,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b104 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 41 400 288 80 224 352), lower := (rows 7 74 164 41 400 288 80 128 256), losses := [] }

theorem u105 : Upper (D 10) (R 10) [6,72,160,33,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b105 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 74 164 41 400 288 96 208 336), lower := (rows 7 74 164 41 400 288 96 128 256), losses := [] }

theorem u106 : Upper (D 10) (R 10) [6,72,160,33,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b106 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 56 400 96 65 416 288), lower := (rows 7 74 164 56 400 96 65 128 256), losses := [] }

theorem u107 : Upper (D 10) (R 10) [6,72,160,48,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b107 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 56 400 96 96 385 257), lower := (rows 7 74 164 56 400 96 96 128 256), losses := [] }

theorem u108 : Upper (D 10) (R 10) [6,72,160,48,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b108 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 74 164 56 400 96 320 161 289), lower := (rows 7 74 164 56 400 96 320 128 256), losses := [] }

theorem u109 : Upper (D 10) (R 10) [6,72,160,48,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b109 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 152 304 96 65 416 288), lower := (rows 7 74 164 152 304 96 65 128 256), losses := [] }

theorem u110 : Upper (D 10) (R 10) [6,72,160,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b110 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 152 304 96 96 385 257), lower := (rows 7 74 164 152 304 96 96 128 256), losses := [] }

theorem u111 : Upper (D 10) (R 10) [6,72,160,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b111 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 74 164 152 304 96 320 161 289), lower := (rows 7 74 164 152 304 96 320 128 256), losses := [] }

theorem u112 : Upper (D 10) (R 10) [6,72,160,144,288,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b112 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 7 74 164 296 208 33 80 416 288), lower := (rows 7 74 164 296 208 33 80 128 256), losses := [] }

theorem u113 : Upper (D 10) (R 10) [6,72,160,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b113 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 296 208 33 96 400 272), lower := (rows 7 74 164 296 208 33 96 128 256), losses := [] }

theorem u114 : Upper (D 10) (R 10) [6,72,160,288,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b114 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 181, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 296 208 33 320 176 304), lower := (rows 7 74 164 296 208 33 320 128 256), losses := [] }

theorem u115 : Upper (D 10) (R 10) [6,72,160,288,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b115 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 165, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 296 273 96 80 160 416), lower := (rows 7 74 164 296 273 96 80 128 256), losses := [] }

theorem u116 : Upper (D 10) (R 10) [6,72,160,288,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b116 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 400, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 74 164 296 273 96 96 144 400), lower := (rows 7 74 164 296 273 96 96 128 256), losses := [] }

theorem u117 : Upper (D 10) (R 10) [6,72,160,288,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b117 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 228, targets := 256 }], pairs := [(2,8),(3,7)], upper := (rows 7 74 164 296 273 96 192 176 304), lower := (rows 7 74 164 296 273 96 192 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 17 98 64 0 257), good := (rows 319 106 36 296 281 96 96 0 256) }] }

theorem u118 : Upper (D 10) (R 10) [6,72,160,288,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b118 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 7 74 164 296 336 33 80 160 416), lower := (rows 7 74 164 296 336 33 80 128 256), losses := [] }

theorem u119 : Upper (D 10) (R 10) [6,72,160,288,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b119 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P10
