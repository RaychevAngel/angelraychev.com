import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 152 274 33 192 129 320), lower := (rows 7 98 44 152 274 33 192 129 256), losses := [] }

theorem u120 : Upper (D 7) (R 7) [6,96,40,144,258,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 200, targets := 35 },{ cop := 0, region := 272, targets := 64 }], pairs := [(3,0),(3,1),(3,5),(4,6)], upper := (rows 7 98 44 152 274 33 192 192 257), lower := (rows 7 98 44 152 274 33 192 192 256), losses := [] }

theorem u121 : Upper (D 7) (R 7) [6,96,40,144,258,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 161 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 152 336 33 192 129 258), lower := (rows 7 98 44 152 336 33 192 129 256), losses := [] }

theorem u122 : Upper (D 7) (R 7) [6,96,40,144,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,5)], upper := (rows 7 98 44 152 336 33 192 130 257), lower := (rows 7 98 44 152 336 33 192 130 256), losses := [{ target := 1, region := (rows 1 0 4 136 22 33 200 128 289), good := (rows 309 368 380 216 336 289 200 216 256) }] }

theorem u123 : Upper (D 7) (R 7) [6,96,40,144,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 328, targets := 35 },{ cop := 0, region := 144, targets := 32 }], pairs := [(3,0),(3,1),(3,5),(4,5)], upper := (rows 7 98 44 280 146 33 192 129 320), lower := (rows 7 98 44 280 146 33 192 129 256), losses := [] }

theorem u124 : Upper (D 7) (R 7) [6,96,40,272,130,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 280 146 33 192 192 257), lower := (rows 7 98 44 280 146 33 192 192 256), losses := [] }

theorem u125 : Upper (D 7) (R 7) [6,96,40,272,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 328, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 98 44 392 146 33 80 129 320), lower := (rows 7 98 44 392 146 33 80 129 256), losses := [] }

theorem u126 : Upper (D 7) (R 7) [6,96,40,384,130,1,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b126 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 392 146 33 80 192 257), lower := (rows 7 98 44 392 146 33 80 192 256), losses := [] }

theorem u127 : Upper (D 7) (R 7) [6,96,40,384,130,1,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b127 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 172, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 7 98 133 56 273 160 66 136 320), lower := (rows 7 98 133 56 273 160 66 136 256), losses := [] }

theorem u128 : Upper (D 7) (R 7) [6,96,129,48,257,128,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b128 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 312, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 7 98 133 56 273 160 66 192 264), lower := (rows 7 98 133 56 273 160 66 192 256), losses := [] }

theorem u129 : Upper (D 7) (R 7) [6,96,129,48,257,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 346, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 56 336 160 66 129 264), lower := (rows 7 98 133 56 336 160 66 129 256), losses := [] }

theorem u130 : Upper (D 7) (R 7) [6,96,129,48,320,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 56 336 160 66 136 257), lower := (rows 7 98 133 56 336 160 66 136 256), losses := [] }

theorem u131 : Upper (D 7) (R 7) [6,96,129,48,320,128,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b131 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 338, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 140 25 304 160 66 129 320), lower := (rows 7 98 140 25 304 160 66 129 256), losses := [] }

theorem u132 : Upper (D 7) (R 7) [6,96,136,17,288,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 230, targets := 1 },{ cop := 4, region := 66, targets := 128 },{ cop := 8, region := 242, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 7 98 140 25 304 160 66 192 257), lower := (rows 7 98 140 25 304 160 66 192 256), losses := [] }

theorem u133 : Upper (D 7) (R 7) [6,96,136,17,288,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 280, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 140 26 304 33 192 129 320), lower := (rows 7 98 140 26 304 33 192 129 256), losses := [] }

theorem u134 : Upper (D 7) (R 7) [6,96,136,18,288,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 312, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 140 26 304 33 192 192 257), lower := (rows 7 98 140 26 304 33 192 192 256), losses := [] }

theorem u135 : Upper (D 7) (R 7) [6,96,136,18,288,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 280, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 140 56 274 33 192 129 320), lower := (rows 7 98 140 56 274 33 192 129 256), losses := [] }

theorem u136 : Upper (D 7) (R 7) [6,96,136,48,258,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 312, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 140 56 274 33 192 192 257), lower := (rows 7 98 140 56 274 33 192 192 256), losses := [] }

theorem u137 : Upper (D 7) (R 7) [6,96,136,48,258,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 280, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 140 56 336 33 192 129 258), lower := (rows 7 98 140 56 336 33 192 129 256), losses := [] }

theorem u138 : Upper (D 7) (R 7) [6,96,136,48,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 198, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(2,0),(2,1),(4,5)], upper := (rows 7 98 140 56 336 33 192 130 257), lower := (rows 7 98 140 56 336 33 192 130 256), losses := [{ target := 1, region := (rows 1 0 132 43 19 33 196 128 289), good := (rows 381 376 204 312 336 313 196 220 256) }] }

theorem u139 : Upper (D 7) (R 7) [6,96,136,48,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 129 },{ cop := 0, region := 144, targets := 32 }], pairs := [(3,0),(3,7),(4,5)], upper := (rows 7 98 140 296 146 33 80 129 320), lower := (rows 7 98 140 296 146 33 80 129 256), losses := [] }

theorem u140 : Upper (D 7) (R 7) [6,96,136,288,130,1,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b140 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 296, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 140 296 146 33 80 192 257), lower := (rows 7 98 140 296 146 33 80 192 256), losses := [] }

theorem u141 : Upper (D 7) (R 7) [6,96,136,288,130,1,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b141 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 192 130 264), lower := (rows 7 98 164 25 336 33 192 130 256), losses := [] }

theorem u142 : Upper (D 7) (R 7) [6,96,160,17,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 98 164 25 336 33 192 136 258), lower := (rows 7 98 164 25 336 33 192 136 256), losses := [] }

theorem u143 : Upper (D 7) (R 7) [6,96,160,17,320,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b143 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 164 26 400 33 72 129 320), lower := (rows 7 98 164 26 400 33 72 129 256), losses := [] }

theorem u144 : Upper (D 7) (R 7) [6,96,160,18,384,1,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b144 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 132, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 26 400 33 72 192 257), lower := (rows 7 98 164 26 400 33 72 192 256), losses := [] }

theorem u145 : Upper (D 7) (R 7) [6,96,160,18,384,1,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b145 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 280, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 7 98 164 88 274 33 192 129 264), lower := (rows 7 98 164 88 274 33 192 129 256), losses := [] }

theorem u146 : Upper (D 7) (R 7) [6,96,160,80,258,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 200, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 98 164 88 274 33 192 136 257), lower := (rows 7 98 164 88 274 33 192 136 256), losses := [] }

theorem u147 : Upper (D 7) (R 7) [6,96,160,80,258,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b147 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 98 164 152 274 33 72 129 320), lower := (rows 7 98 164 152 274 33 72 129 256), losses := [] }

theorem u148 : Upper (D 7) (R 7) [6,96,160,144,258,1,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b148 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 200, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 98 164 152 274 33 72 192 257), lower := (rows 7 98 164 152 274 33 72 192 256), losses := [] }

theorem u149 : Upper (D 7) (R 7) [6,96,160,144,258,1,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b149 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 346, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 164 200 274 33 80 129 264), lower := (rows 7 98 164 200 274 33 80 129 256), losses := [] }

theorem u150 : Upper (D 7) (R 7) [6,96,160,192,258,1,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b150 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 200 274 33 80 136 257), lower := (rows 7 98 164 200 274 33 80 136 256), losses := [] }

theorem u151 : Upper (D 7) (R 7) [6,96,160,192,258,1,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b151 [(6,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 261 56 146 33 192 136 320), lower := (rows 7 98 261 56 146 33 192 136 256), losses := [] }

theorem u152 : Upper (D 7) (R 7) [6,96,257,48,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b152 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 261 56 146 33 192 192 264), lower := (rows 7 98 261 56 146 33 192 192 256), losses := [] }

theorem u153 : Upper (D 7) (R 7) [6,96,257,48,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 325, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 98 268 138 49 160 65 144 320), lower := (rows 7 98 268 138 49 160 65 144 256), losses := [] }

theorem u154 : Upper (D 7) (R 7) [6,96,264,130,33,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b154 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 309, targets := 64 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 98 268 138 49 160 65 192 272), lower := (rows 7 98 268 138 49 160 65 192 256), losses := [] }

theorem u155 : Upper (D 7) (R 7) [6,96,264,130,33,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 202, targets := 1 },{ cop := 0, region := 208, targets := 32 },{ cop := 0, region := 168, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,5)], upper := (rows 7 98 268 168 81 33 192 130 272), lower := (rows 7 98 268 168 81 33 192 130 256), losses := [] }

theorem u156 : Upper (D 7) (R 7) [6,96,264,160,65,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 248, targets := 2 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 7 98 268 168 81 33 192 144 258), lower := (rows 7 98 268 168 81 33 192 144 256), losses := [] }

theorem u157 : Upper (D 7) (R 7) [6,96,264,160,65,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b157 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 292 25 146 33 192 136 320), lower := (rows 7 98 292 25 146 33 192 136 256), losses := [] }

theorem u158 : Upper (D 7) (R 7) [6,96,288,17,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b158 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 292 25 146 33 192 192 264), lower := (rows 7 98 292 25 146 33 192 192 256), losses := [] }

theorem u159 : Upper (D 7) (R 7) [6,96,288,17,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 292 26 145 33 192 136 320), lower := (rows 7 98 292 26 145 33 192 136 256), losses := [] }

theorem u160 : Upper (D 7) (R 7) [6,96,288,18,129,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b160 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 293, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 292 26 145 33 192 192 264), lower := (rows 7 98 292 26 145 33 192 192 256), losses := [] }

theorem u161 : Upper (D 7) (R 7) [6,96,288,18,129,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 293, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 98 292 73 146 33 192 136 272), lower := (rows 7 98 292 73 146 33 192 136 256), losses := [] }

theorem u162 : Upper (D 7) (R 7) [6,96,288,65,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b162 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 8, camps := [{ cop := 6, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 292 73 146 33 192 144 264), lower := (rows 7 98 292 73 146 33 192 144 256), losses := [] }

theorem u163 : Upper (D 7) (R 7) [6,96,288,65,130,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b163 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 292 137 146 33 80 136 320), lower := (rows 7 98 292 137 146 33 80 136 256), losses := [] }

theorem u164 : Upper (D 7) (R 7) [6,96,288,129,130,1,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b164 [(6,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 292, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 7 98 292 137 146 33 80 192 264), lower := (rows 7 98 292 137 146 33 80 192 256), losses := [] }

theorem u165 : Upper (D 7) (R 7) [6,96,288,129,130,1,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b165 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 266, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7)], upper := (rows 7 259 44 26 81 160 192 160 320), lower := (rows 7 259 44 26 81 160 192 160 256), losses := [] }

theorem u166 : Upper (D 7) (R 7) [6,257,40,18,65,128,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 259 44 26 81 160 192 192 288), lower := (rows 7 259 44 26 81 160 192 192 256), losses := [] }

theorem u167 : Upper (D 7) (R 7) [6,257,40,18,65,128,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 6, region := 298, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 266 21 104 176 34 192 129 320), lower := (rows 7 266 21 104 176 34 192 129 256), losses := [] }

theorem u168 : Upper (D 7) (R 7) [6,264,17,96,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 216, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 266 21 104 176 34 192 192 257), lower := (rows 7 266 21 104 176 34 192 192 256), losses := [] }

theorem u169 : Upper (D 7) (R 7) [6,264,17,96,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 266, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 266 52 74 145 96 192 129 288), lower := (rows 7 266 52 74 145 96 192 129 256), losses := [] }

theorem u170 : Upper (D 7) (R 7) [6,264,48,66,129,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 266 52 74 145 96 192 160 257), lower := (rows 7 266 52 74 145 96 192 160 256), losses := [] }

theorem u171 : Upper (D 7) (R 7) [6,264,48,66,129,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 184, targets := 64 },{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,6),(4,6)], upper := (rows 7 266 100 25 146 33 192 160 320), lower := (rows 7 266 100 25 146 33 192 160 256), losses := [] }

theorem u172 : Upper (D 7) (R 7) [6,264,96,17,130,1,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 290, targets := 192 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 7 266 100 25 146 33 192 192 288), lower := (rows 7 266 100 25 146 33 192 192 256), losses := [] }

theorem u173 : Upper (D 7) (R 7) [6,264,96,17,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 184, targets := 64 },{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,6),(4,6)], upper := (rows 7 266 100 25 176 34 192 129 320), lower := (rows 7 266 100 25 176 34 192 129 256), losses := [] }

theorem u174 : Upper (D 7) (R 7) [6,264,96,17,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 266 100 25 176 34 192 192 257), lower := (rows 7 266 100 25 176 34 192 192 256), losses := [] }

theorem u175 : Upper (D 7) (R 7) [6,264,96,17,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 7 266 100 26 145 33 192 160 320), lower := (rows 7 266 100 26 145 33 192 160 256), losses := [] }

theorem u176 : Upper (D 7) (R 7) [6,264,96,18,129,1,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 298, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 266 100 26 145 33 192 192 288), lower := (rows 7 266 100 26 145 33 192 192 256), losses := [] }

theorem u177 : Upper (D 7) (R 7) [6,264,96,18,129,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 128, camps := [{ cop := 7, region := 378, targets := 1 },{ cop := 4, region := 258, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 290 13 88 176 96 66 129 384), lower := (rows 7 290 13 88 176 96 66 129 256), losses := [] }

theorem u178 : Upper (D 7) (R 7) [6,288,9,80,160,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 5, region := 338, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 7 290 13 200 112 160 66 129 272), lower := (rows 7 290 13 200 112 160 66 129 256), losses := [] }

theorem u179 : Upper (D 7) (R 7) [6,288,9,192,96,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P07
