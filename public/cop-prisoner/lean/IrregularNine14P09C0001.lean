import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 70 133 25 400 288 72 160 320), lower := (rows 35 70 133 25 400 288 72 160 256), losses := [] }

theorem u60 : Upper (D 9) (R 9) [34,68,129,17,384,256,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b60 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 198, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 70 133 25 400 288 72 192 288), lower := (rows 35 70 133 25 400 288 72 192 256), losses := [] }

theorem u61 : Upper (D 9) (R 9) [34,68,129,17,384,256,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b61 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 70 133 152 273 288 72 160 320), lower := (rows 35 70 133 152 273 288 72 160 256), losses := [] }

theorem u62 : Upper (D 9) (R 9) [34,68,129,144,257,256,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b62 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 206, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 70 133 152 273 288 72 192 288), lower := (rows 35 70 133 152 273 288 72 192 256), losses := [] }

theorem u63 : Upper (D 9) (R 9) [34,68,129,144,257,256,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b63 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 140, targets := 320 }], pairs := [(2,6),(2,8),(3,6)], upper := (rows 35 70 133 168 273 48 320 136 320), lower := (rows 35 70 133 168 273 48 320 136 256), losses := [] }

theorem u64 : Upper (D 9) (R 9) [34,68,129,160,257,16,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b64 [(5,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 312, targets := 64 },{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(4,6)], upper := (rows 35 70 133 168 273 48 320 192 264), lower := (rows 35 70 133 168 273 48 320 192 256), losses := [] }

theorem u65 : Upper (D 9) (R 9) [34,68,129,160,257,16,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b65 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 140, targets := 320 }], pairs := [(2,6),(2,8),(3,6)], upper := (rows 35 70 133 168 273 288 80 136 320), lower := (rows 35 70 133 168 273 288 80 136 256), losses := [] }

theorem u66 : Upper (D 9) (R 9) [34,68,129,160,257,256,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b66 [(6,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 198, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 70 133 168 273 288 80 192 264), lower := (rows 35 70 133 168 273 288 80 192 256), losses := [] }

theorem u67 : Upper (D 9) (R 9) [34,68,129,160,257,256,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b67 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 140, targets := 320 }], pairs := [(2,6),(2,8),(3,6),(3,8)], upper := (rows 35 70 133 168 280 48 320 129 320), lower := (rows 35 70 133 168 280 48 320 129 256), losses := [] }

theorem u68 : Upper (D 9) (R 9) [34,68,129,160,264,16,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b68 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 312, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,6)], upper := (rows 35 70 133 168 280 48 320 192 257), lower := (rows 35 70 133 168 280 48 320 192 256), losses := [] }

theorem u69 : Upper (D 9) (R 9) [34,68,129,160,264,16,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b69 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 140, targets := 320 }], pairs := [(2,6),(2,8),(3,6),(3,8)], upper := (rows 35 70 133 168 280 288 80 129 320), lower := (rows 35 70 133 168 280 288 80 129 256), losses := [] }

theorem u70 : Upper (D 9) (R 9) [34,68,129,160,264,256,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b70 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 289, targets := 192 },{ cop := 2, region := 312, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 35 70 133 168 280 288 80 192 257), lower := (rows 35 70 133 168 280 288 80 192 256), losses := [] }

theorem u71 : Upper (D 9) (R 9) [34,68,129,160,264,256,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b71 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 136, targets := 289 }], pairs := [(3,0),(3,5),(3,8)], upper := (rows 35 70 133 200 273 48 320 136 288), lower := (rows 35 70 133 200 273 48 320 136 256), losses := [] }

theorem u72 : Upper (D 9) (R 9) [34,68,129,192,257,16,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b72 [(5,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 70 133 200 273 48 320 160 264), lower := (rows 35 70 133 200 273 48 320 160 256), losses := [] }

theorem u73 : Upper (D 9) (R 9) [34,68,129,192,257,16,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b73 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 206, targets := 288 }], pairs := [(1,5),(1,8),(2,5)], upper := (rows 35 70 133 200 273 288 80 136 288), lower := (rows 35 70 133 200 273 288 80 136 256), losses := [] }

theorem u74 : Upper (D 9) (R 9) [34,68,129,192,257,256,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b74 [(6,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 70 133 200 273 288 80 160 264), lower := (rows 35 70 133 200 273 288 80 160 256), losses := [] }

theorem u75 : Upper (D 9) (R 9) [34,68,129,192,257,256,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b75 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 378, targets := 1 },{ cop := 7, region := 4, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(4,0)], upper := (rows 35 70 133 200 280 48 320 129 288), lower := (rows 35 70 133 200 280 48 320 129 256), losses := [] }

theorem u76 : Upper (D 9) (R 9) [34,68,129,192,264,16,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b76 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 6, region := 184, targets := 1 }], pairs := [(1,5),(3,0),(3,5),(4,5)], upper := (rows 35 70 133 200 280 48 320 160 257), lower := (rows 35 70 133 200 280 48 320 160 256), losses := [] }

theorem u77 : Upper (D 9) (R 9) [34,68,129,192,264,16,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b77 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 148, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 35 70 140 265 400 48 96 129 320), lower := (rows 35 70 140 265 400 48 96 129 256), losses := [] }

theorem u78 : Upper (D 9) (R 9) [34,68,136,257,384,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b78 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 246, targets := 1 },{ cop := 0, region := 264, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 35 70 140 265 400 48 96 192 257), lower := (rows 35 70 140 265 400 48 96 192 256), losses := [] }

theorem u79 : Upper (D 9) (R 9) [34,68,136,257,384,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b79 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5),(3,5)], upper := (rows 35 70 140 280 145 288 65 160 320), lower := (rows 35 70 140 280 145 288 65 160 256), losses := [] }

theorem u80 : Upper (D 9) (R 9) [34,68,136,272,129,256,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b80 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 300, targets := 65 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(2,6),(3,0),(3,6),(4,5)], upper := (rows 35 70 140 280 145 288 65 192 288), lower := (rows 35 70 140 280 145 288 65 192 256), losses := [] }

theorem u81 : Upper (D 9) (R 9) [34,68,136,272,129,256,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b81 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 70 164 200 273 48 320 129 264), lower := (rows 35 70 164 200 273 48 320 129 256), losses := [] }

theorem u82 : Upper (D 9) (R 9) [34,68,160,192,257,16,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b82 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 289 }], pairs := [(3,0),(3,5),(3,8)], upper := (rows 35 70 164 200 273 48 320 136 257), lower := (rows 35 70 164 200 273 48 320 136 256), losses := [] }

theorem u83 : Upper (D 9) (R 9) [34,68,160,192,257,16,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b83 [(5,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 132, targets := 320 }], pairs := [(2,6),(2,8),(3,5),(4,5)], upper := (rows 35 70 164 200 273 288 80 129 264), lower := (rows 35 70 164 200 273 288 80 129 256), losses := [] }

theorem u84 : Upper (D 9) (R 9) [34,68,160,192,257,256,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b84 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 289 }], pairs := [(3,0),(3,5),(3,8)], upper := (rows 35 70 164 200 273 288 80 136 257), lower := (rows 35 70 164 200 273 288 80 136 256), losses := [] }

theorem u85 : Upper (D 9) (R 9) [34,68,160,192,257,256,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b85 [(6,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 342, targets := 32 },{ cop := 4, region := 164, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(4,5)], upper := (rows 35 70 388 137 280 48 65 160 320), lower := (rows 35 70 388 137 280 48 65 160 256), losses := [] }

theorem u86 : Upper (D 9) (R 9) [34,68,384,129,264,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b86 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 308, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 70 388 137 280 48 65 192 288), lower := (rows 35 70 388 137 280 48 65 192 256), losses := [] }

theorem u87 : Upper (D 9) (R 9) [34,68,384,129,264,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b87 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 374, targets := 1 },{ cop := 7, region := 8, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 35 70 388 137 280 48 96 129 320), lower := (rows 35 70 388 137 280 48 96 129 256), losses := [] }

theorem u88 : Upper (D 9) (R 9) [34,68,384,129,264,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b88 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 276, targets := 32 },{ cop := 3, region := 276, targets := 64 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 35 70 388 137 280 48 96 192 257), lower := (rows 35 70 388 137 280 48 96 192 256), losses := [] }

theorem u89 : Upper (D 9) (R 9) [34,68,384,129,264,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b89 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 292, targets := 65 },{ cop := 0, region := 336, targets := 128 }], pairs := [(2,0),(2,6),(4,0),(4,7)], upper := (rows 35 70 388 152 336 40 65 129 288), lower := (rows 35 70 388 152 336 40 65 129 256), losses := [{ target := 0, region := (rows 0 2 140 8 80 40 64 128 297), good := (rows 290 86 388 444 336 300 336 388 256) }] }

theorem u90 : Upper (D 9) (R 9) [34,68,384,144,320,8,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b90 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 174, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(4,5)], upper := (rows 35 70 388 152 336 40 65 160 257), lower := (rows 35 70 388 152 336 40 65 160 256), losses := [] }

theorem u91 : Upper (D 9) (R 9) [34,68,384,144,320,8,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b91 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 312, targets := 1 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 194 13 88 400 288 65 132 288), lower := (rows 35 194 13 88 400 288 65 132 256), losses := [] }

theorem u92 : Upper (D 9) (R 9) [34,192,9,80,384,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b92 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 5, region := 195, targets := 256 }], pairs := [(0,8),(1,0),(1,8),(4,0),(4,6)], upper := (rows 35 194 13 88 400 288 65 160 260), lower := (rows 35 194 13 88 400 288 65 160 256), losses := [{ target := 0, region := (rows 0 74 4 8 308 308 64 445 260), good := (rows 178 194 446 250 432 432 194 176 432) }] }

theorem u93 : Upper (D 9) (R 9) [34,192,9,80,384,256,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b93 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 128, camps := [{ cop := 0, region := 80, targets := 384 },{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0),(4,7),(4,8)], upper := (rows 35 194 13 280 112 288 65 132 384), lower := (rows 35 194 13 280 112 288 65 132 256), losses := [] }

theorem u94 : Upper (D 9) (R 9) [34,192,9,272,96,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b94 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 312, targets := 1 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 194 13 328 176 288 65 132 272), lower := (rows 35 194 13 328 176 288 65 132 256), losses := [] }

theorem u95 : Upper (D 9) (R 9) [34,192,9,320,160,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b95 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 5, region := 211, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7)], upper := (rows 35 194 13 328 176 288 65 144 260), lower := (rows 35 194 13 328 176 288 65 144 256), losses := [] }

theorem u96 : Upper (D 9) (R 9) [34,192,9,320,160,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b96 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 194 13 328 400 36 96 129 272), lower := (rows 35 194 13 328 400 36 96 129 256), losses := [] }

theorem u97 : Upper (D 9) (R 9) [34,192,9,320,384,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b97 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 146, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 13 328 400 36 96 144 257), lower := (rows 35 194 13 328 400 36 96 144 256), losses := [] }

theorem u98 : Upper (D 9) (R 9) [34,192,9,320,384,4,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b98 [(5,2),(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 5, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(3,0),(4,0)], upper := (rows 35 194 28 104 400 288 65 129 260), lower := (rows 35 194 28 104 400 288 65 129 256), losses := [] }

theorem u99 : Upper (D 9) (R 9) [34,192,24,96,384,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b99 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 194 28 104 400 288 65 132 257), lower := (rows 35 194 28 104 400 288 65 132 256), losses := [] }

theorem u100 : Upper (D 9) (R 9) [34,192,24,96,384,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b100 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 284, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(4,0)], upper := (rows 35 194 28 328 400 33 65 160 260), lower := (rows 35 194 28 328 400 33 65 160 256), losses := [] }

theorem u101 : Upper (D 9) (R 9) [34,192,24,320,384,1,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 28 328 400 33 68 160 257), lower := (rows 35 194 28 328 400 33 68 160 256), losses := [] }

theorem u102 : Upper (D 9) (R 9) [34,192,24,320,384,1,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b102 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 326, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 168 273 48 320 129 260), lower := (rows 35 194 76 168 273 48 320 129 256), losses := [] }

theorem u103 : Upper (D 9) (R 9) [34,192,72,160,257,16,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b103 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 168 273 48 320 132 257), lower := (rows 35 194 76 168 273 48 320 132 256), losses := [] }

theorem u104 : Upper (D 9) (R 9) [34,192,72,160,257,16,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b104 [(5,4),(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 207, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 76 168 273 288 65 132 272), lower := (rows 35 194 76 168 273 288 65 132 256), losses := [] }

theorem u105 : Upper (D 9) (R 9) [34,192,72,160,257,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b105 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 300, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 194 76 168 273 288 65 144 260), lower := (rows 35 194 76 168 273 288 65 144 256), losses := [] }

theorem u106 : Upper (D 9) (R 9) [34,192,72,160,257,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b106 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 136, targets := 320 },{ cop := 1, region := 300, targets := 1 }], pairs := [(2,0),(3,0),(3,6),(3,8)], upper := (rows 35 194 76 168 273 288 80 129 260), lower := (rows 35 194 76 168 273 288 80 129 256), losses := [] }

theorem u107 : Upper (D 9) (R 9) [34,192,72,160,257,256,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b107 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 168 273 288 80 132 257), lower := (rows 35 194 76 168 273 288 80 132 256), losses := [] }

theorem u108 : Upper (D 9) (R 9) [34,192,72,160,257,256,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b108 [(6,4),(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 0, region := 136, targets := 64 },{ cop := 0, region := 136, targets := 256 }], pairs := [(1,5),(2,5),(3,6),(3,8)], upper := (rows 35 194 76 168 276 48 320 129 257), lower := (rows 35 194 76 168 276 48 320 129 256), losses := [{ target := 5, region := (rows 1 139 12 8 24 0 475 129 385), good := (rows 451 450 94 478 340 80 320 451 320) }] }

theorem u109 : Upper (D 9) (R 9) [34,192,72,160,260,16,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b109 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 207, targets := 256 },{ cop := 1, region := 316, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 194 76 168 276 288 65 129 272), lower := (rows 35 194 76 168 276 288 65 129 256), losses := [] }

theorem u110 : Upper (D 9) (R 9) [34,192,72,160,260,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 168 276 288 65 144 257), lower := (rows 35 194 76 168 276 288 65 144 256), losses := [] }

theorem u111 : Upper (D 9) (R 9) [34,192,72,160,260,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b111 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 5, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(3,0),(4,0)], upper := (rows 35 194 76 280 176 288 65 129 260), lower := (rows 35 194 76 280 176 288 65 129 256), losses := [] }

theorem u112 : Upper (D 9) (R 9) [34,192,72,272,160,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 },{ cop := 2, region := 130, targets := 1 }], pairs := [(0,6),(1,0),(3,6),(4,6)], upper := (rows 35 194 76 280 176 288 65 132 257), lower := (rows 35 194 76 280 176 288 65 132 256), losses := [] }

theorem u113 : Upper (D 9) (R 9) [34,192,72,272,160,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b113 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 392 273 48 65 132 288), lower := (rows 35 194 76 392 273 48 65 132 256), losses := [] }

theorem u114 : Upper (D 9) (R 9) [34,192,72,384,257,16,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b114 [(5,4),(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 268, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 392 273 48 65 160 260), lower := (rows 35 194 76 392 273 48 65 160 256), losses := [] }

theorem u115 : Upper (D 9) (R 9) [34,192,72,384,257,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b115 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 268, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 392 273 48 96 129 260), lower := (rows 35 194 76 392 273 48 96 129 256), losses := [] }

theorem u116 : Upper (D 9) (R 9) [34,192,72,384,257,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b116 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 392 273 48 96 132 257), lower := (rows 35 194 76 392 273 48 96 132 256), losses := [] }

theorem u117 : Upper (D 9) (R 9) [34,192,72,384,257,16,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b117 [(5,4),(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 194 76 392 276 48 65 129 288), lower := (rows 35 194 76 392 276 48 65 129 256), losses := [] }

theorem u118 : Upper (D 9) (R 9) [34,192,72,384,260,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b118 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 168, targets := 65 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8),(3,0),(3,6)], upper := (rows 35 194 76 392 276 48 65 160 257), lower := (rows 35 194 76 392 276 48 65 160 256), losses := [] }

theorem u119 : Upper (D 9) (R 9) [34,192,72,384,260,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b119 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P09
