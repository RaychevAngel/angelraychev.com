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

def b120 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 136, targets := 320 },{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0),(3,6),(3,8),(4,0)], upper := (rows 97 7 28 137 304 160 320 130 320), lower := (rows 97 7 28 137 304 160 320 130 256), losses := [] }

theorem u120 : Upper (D 9) (R 9) [96,5,24,129,288,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b120 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 310, targets := 64 },{ cop := 6, region := 169, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,8),(4,6)], upper := (rows 97 7 28 137 304 160 320 192 258), lower := (rows 97 7 28 137 304 160 320 192 256), losses := [] }

theorem u121 : Upper (D 9) (R 9) [96,5,24,129,288,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b121 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 174, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 134 56 273 160 320 136 320), lower := (rows 97 7 134 56 273 160 320 136 256), losses := [] }

theorem u122 : Upper (D 9) (R 9) [96,5,130,48,257,128,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b122 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 6, region := 167, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 134 56 273 160 320 192 264), lower := (rows 97 7 134 56 273 160 320 192 256), losses := [] }

theorem u123 : Upper (D 9) (R 9) [96,5,130,48,257,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b123 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 174, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 140 56 273 160 320 130 320), lower := (rows 97 7 140 56 273 160 320 130 256), losses := [] }

theorem u124 : Upper (D 9) (R 9) [96,5,136,48,257,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b124 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 1, region := 272, targets := 32 },{ cop := 1, region := 272, targets := 64 },{ cop := 1, region := 272, targets := 128 }], pairs := [(2,0),(3,0),(4,5),(4,6),(4,7)], upper := (rows 97 7 140 56 273 160 320 192 258), lower := (rows 97 7 140 56 273 160 320 192 256), losses := [] }

theorem u125 : Upper (D 9) (R 9) [96,5,136,48,257,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b125 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 336, targets := 33 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 97 7 140 56 400 34 320 129 320), lower := (rows 97 7 140 56 400 34 320 129 256), losses := [] }

theorem u126 : Upper (D 9) (R 9) [96,5,136,48,384,2,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b126 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 144, targets := 33 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 97 7 140 56 400 34 320 192 257), lower := (rows 97 7 140 56 400 34 320 192 256), losses := [] }

theorem u127 : Upper (D 9) (R 9) [96,5,136,48,384,2,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b127 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 182, targets := 64 },{ cop := 6, region := 289, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 7 140 265 50 288 192 144 320), lower := (rows 97 7 140 265 50 288 192 144 256), losses := [] }

theorem u128 : Upper (D 9) (R 9) [96,5,136,257,34,256,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b128 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 312, targets := 192 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 7 140 265 50 288 192 192 272), lower := (rows 97 7 140 265 50 288 192 192 256), losses := [] }

theorem u129 : Upper (D 9) (R 9) [96,5,136,257,34,256,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b129 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 7 140 280 176 33 320 130 320), lower := (rows 97 7 140 280 176 33 320 130 256), losses := [] }

theorem u130 : Upper (D 9) (R 9) [96,5,136,272,160,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b130 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 196, targets := 33 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(2,5)], upper := (rows 97 7 140 280 176 33 320 192 258), lower := (rows 97 7 140 280 176 33 320 192 256), losses := [] }

theorem u131 : Upper (D 9) (R 9) [96,5,136,272,160,1,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b131 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 144, targets := 320 },{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0),(4,6),(4,8)], upper := (rows 97 7 140 296 145 48 320 130 320), lower := (rows 97 7 140 296 145 48 320 130 256), losses := [] }

theorem u132 : Upper (D 9) (R 9) [96,5,136,288,129,16,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b132 [(5,4),(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 64 },{ cop := 3, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(2,6),(3,6)], upper := (rows 97 7 140 296 145 48 320 192 258), lower := (rows 97 7 140 296 145 48 320 192 256), losses := [] }

theorem u133 : Upper (D 9) (R 9) [96,5,136,288,129,16,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b133 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 336, targets := 33 },{ cop := 0, region := 264, targets := 1 }], pairs := [(3,0),(4,0),(4,5)], upper := (rows 97 7 140 296 400 34 80 129 320), lower := (rows 97 7 140 296 400 34 80 129 256), losses := [] }

theorem u134 : Upper (D 9) (R 9) [96,5,136,288,384,2,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b134 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 7 140 296 400 34 80 192 257), lower := (rows 97 7 140 296 400 34 80 192 256), losses := [] }

theorem u135 : Upper (D 9) (R 9) [96,5,136,288,384,2,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b135 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 166, targets := 320 }], pairs := [(1,6),(1,8),(2,6)], upper := (rows 97 7 164 25 400 34 320 136 320), lower := (rows 97 7 164 25 400 34 320 136 256), losses := [] }

theorem u136 : Upper (D 9) (R 9) [96,5,160,17,384,2,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b136 [(5,1),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 8, camps := [{ cop := 6, region := 167, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 25 400 34 320 192 264), lower := (rows 97 7 164 25 400 34 320 192 256), losses := [] }

theorem u137 : Upper (D 9) (R 9) [96,5,160,17,384,2,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b137 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 174, targets := 320 }], pairs := [(1,6),(1,8),(2,6)], upper := (rows 97 7 164 152 273 34 320 136 320), lower := (rows 97 7 164 152 273 34 320 136 256), losses := [] }

theorem u138 : Upper (D 9) (R 9) [96,5,160,144,257,2,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b138 [(5,1),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 8, camps := [{ cop := 6, region := 167, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 152 273 34 320 192 264), lower := (rows 97 7 164 152 273 34 320 192 256), losses := [] }

theorem u139 : Upper (D 9) (R 9) [96,5,160,144,257,2,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b139 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 184, targets := 320 }], pairs := [(3,6),(3,8),(4,6)], upper := (rows 97 7 388 42 145 48 320 136 320), lower := (rows 97 7 388 42 145 48 320 136 256), losses := [] }

theorem u140 : Upper (D 9) (R 9) [96,5,384,34,129,16,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b140 [(5,4),(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 302, targets := 64 },{ cop := 3, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(2,6),(3,6)], upper := (rows 97 7 388 42 145 48 320 192 264), lower := (rows 97 7 388 42 145 48 320 192 256), losses := [] }

theorem u141 : Upper (D 9) (R 9) [96,5,384,34,129,16,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b141 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 65, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,7)], upper := (rows 97 7 388 56 146 288 65 136 320), lower := (rows 97 7 388 56 146 288 65 136 256), losses := [] }

theorem u142 : Upper (D 9) (R 9) [96,5,384,48,130,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b142 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 300, targets := 65 },{ cop := 1, region := 208, targets := 32 }], pairs := [(2,0),(2,6),(3,0),(3,6),(4,5)], upper := (rows 97 7 388 56 146 288 65 192 264), lower := (rows 97 7 388 56 146 288 65 192 256), losses := [] }

theorem u143 : Upper (D 9) (R 9) [96,5,384,48,130,256,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b143 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 7 388 56 208 288 65 130 264), lower := (rows 97 7 388 56 208 288 65 130 256), losses := [] }

theorem u144 : Upper (D 9) (R 9) [96,5,384,48,192,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b144 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 217, targets := 256 },{ cop := 0, region := 152, targets := 1 }], pairs := [(0,8),(3,0),(3,8),(4,8)], upper := (rows 97 7 388 56 208 288 65 136 258), lower := (rows 97 7 388 56 208 288 65 136 256), losses := [] }

theorem u145 : Upper (D 9) (R 9) [96,5,384,48,192,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b145 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 65, targets := 384 },{ cop := 3, region := 80, targets := 288 }], pairs := [(0,7),(0,8),(1,0),(4,5),(4,8)], upper := (rows 97 14 52 137 208 288 65 384 258), lower := (rows 97 14 52 137 208 288 65 384 256), losses := [{ target := 0, region := (rows 0 10 29 8 17 426 64 426 266), good := (rows 244 430 180 446 244 416 84 416 416) }] }

theorem u146 : Upper (D 9) (R 9) [96,12,48,129,192,256,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b146 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 174, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 14 52 137 273 160 320 130 320), lower := (rows 97 14 52 137 273 160 320 130 256), losses := [] }

theorem u147 : Upper (D 9) (R 9) [96,12,48,129,257,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b147 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 310, targets := 64 },{ cop := 6, region := 169, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,8),(4,6)], upper := (rows 97 14 52 137 273 160 320 192 258), lower := (rows 97 14 52 137 273 160 320 192 256), losses := [] }

theorem u148 : Upper (D 9) (R 9) [96,12,48,129,257,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b148 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 164, targets := 320 },{ cop := 6, region := 169, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(0,8),(2,6),(2,8),(3,5),(3,8)], upper := (rows 97 14 52 200 273 160 320 129 258), lower := (rows 97 14 52 200 273 160 320 129 256), losses := [] }

theorem u149 : Upper (D 9) (R 9) [96,12,48,192,257,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b149 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 238, targets := 1 },{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0)], upper := (rows 97 14 52 200 273 160 320 130 257), lower := (rows 97 14 52 200 273 160 320 130 256), losses := [] }

theorem u150 : Upper (D 9) (R 9) [96,12,48,192,257,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b150 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6),(3,0)], upper := (rows 97 14 52 392 208 288 65 129 258), lower := (rows 97 14 52 392 208 288 65 129 256), losses := [] }

theorem u151 : Upper (D 9) (R 9) [96,12,48,384,192,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b151 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 293, targets := 128 },{ cop := 2, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(2,7)], upper := (rows 97 14 52 392 208 288 65 130 257), lower := (rows 97 14 52 392 208 288 65 130 256), losses := [{ target := 5, region := (rows 1 6 4 24 16 0 65 134 321), good := (rows 321 142 158 392 472 256 321 130 256) }] }

theorem u152 : Upper (D 9) (R 9) [96,12,48,384,192,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b152 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 272, targets := 1 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(4,0),(4,7)], upper := (rows 97 14 133 152 304 33 320 130 320), lower := (rows 97 14 133 152 304 33 320 130 256), losses := [] }

theorem u153 : Upper (D 9) (R 9) [96,12,129,144,288,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b153 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6),(4,7)], upper := (rows 97 14 133 152 304 33 320 192 258), lower := (rows 97 14 133 152 304 33 320 192 256), losses := [] }

theorem u154 : Upper (D 9) (R 9) [96,12,129,144,288,1,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b154 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 48, targets := 320 },{ cop := 4, region := 328, targets := 33 }], pairs := [(3,0),(3,5),(4,6),(4,8)], upper := (rows 97 14 133 280 176 33 320 130 320), lower := (rows 97 14 133 280 176 33 320 130 256), losses := [] }

theorem u155 : Upper (D 9) (R 9) [96,12,129,272,160,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b155 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 64 },{ cop := 6, region := 165, targets := 256 }], pairs := [(0,8),(1,6),(2,8),(3,6),(4,6)], upper := (rows 97 14 133 280 176 33 320 192 258), lower := (rows 97 14 133 280 176 33 320 192 256), losses := [] }

theorem u156 : Upper (D 9) (R 9) [96,12,129,272,160,1,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b156 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 4, region := 69, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(3,7)], upper := (rows 97 14 133 280 176 288 65 130 320), lower := (rows 97 14 133 280 176 288 65 130 256), losses := [] }

theorem u157 : Upper (D 9) (R 9) [96,12,129,272,160,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b157 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6),(4,0)], upper := (rows 97 14 133 280 176 288 65 192 258), lower := (rows 97 14 133 280 176 288 65 192 256), losses := [] }

theorem u158 : Upper (D 9) (R 9) [96,12,129,272,160,256,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b158 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 14 133 296 273 160 80 130 320), lower := (rows 97 14 133 296 273 160 80 130 256), losses := [] }

theorem u159 : Upper (D 9) (R 9) [96,12,129,288,257,128,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b159 [(6,4),(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 64 },{ cop := 2, region := 298, targets := 1 }], pairs := [(1,0),(1,6),(3,6),(4,6)], upper := (rows 97 14 133 296 273 160 80 192 258), lower := (rows 97 14 133 296 273 160 80 192 256), losses := [] }

theorem u160 : Upper (D 9) (R 9) [96,12,129,288,257,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b160 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 174, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 148 296 273 160 65 130 320), lower := (rows 97 14 148 296 273 160 65 130 256), losses := [] }

theorem u161 : Upper (D 9) (R 9) [96,12,144,288,257,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b161 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 298, targets := 65 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 14 148 296 273 160 65 192 258), lower := (rows 97 14 148 296 273 160 65 192 256), losses := [] }

theorem u162 : Upper (D 9) (R 9) [96,12,144,288,257,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b162 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 41, targets := 128 },{ cop := 4, region := 165, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,8),(3,7)], upper := (rows 97 14 148 296 336 33 192 129 258), lower := (rows 97 14 148 296 336 33 192 129 256), losses := [{ target := 0, region := (rows 0 131 196 41 215 32 196 128 487), good := (rows 382 350 470 296 340 314 470 478 256) }] }

theorem u163 : Upper (D 9) (R 9) [96,12,144,288,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b163 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 214, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 14 148 296 336 33 192 130 257), lower := (rows 97 14 148 296 336 33 192 130 256), losses := [] }

theorem u164 : Upper (D 9) (R 9) [96,12,144,288,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b164 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 298, targets := 65 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 14 148 296 336 160 65 129 258), lower := (rows 97 14 148 296 336 160 65 129 256), losses := [] }

theorem u165 : Upper (D 9) (R 9) [96,12,144,288,320,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b165 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 174, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 148 296 336 160 65 130 257), lower := (rows 97 14 148 296 336 160 65 130 256), losses := [] }

theorem u166 : Upper (D 9) (R 9) [96,12,144,288,320,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b166 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 366, targets := 1 },{ cop := 5, region := 209, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 97 14 164 328 145 288 80 129 258), lower := (rows 97 14 164 328 145 288 80 129 256), losses := [] }

theorem u167 : Upper (D 9) (R 9) [96,12,160,320,129,256,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b167 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 166, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 14 164 328 145 288 80 130 257), lower := (rows 97 14 164 328 145 288 80 130 256), losses := [] }

theorem u168 : Upper (D 9) (R 9) [96,12,160,320,129,256,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b168 [(6,4),(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 6, region := 313, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 38 133 88 273 288 192 130 264), lower := (rows 97 38 133 88 273 288 192 130 256), losses := [] }

theorem u169 : Upper (D 9) (R 9) [96,36,129,80,257,256,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b169 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 306, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 97 38 133 88 273 288 192 136 258), lower := (rows 97 38 133 88 273 288 192 136 256), losses := [] }

theorem u170 : Upper (D 9) (R 9) [96,36,129,80,257,256,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b170 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 378, targets := 1 },{ cop := 5, region := 199, targets := 256 }], pairs := [(0,8),(1,0),(1,8),(3,0),(4,0)], upper := (rows 97 38 133 88 274 288 192 129 264), lower := (rows 97 38 133 88 274 288 192 129 256), losses := [] }

theorem u171 : Upper (D 9) (R 9) [96,36,129,80,258,256,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b171 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 306, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 97 38 133 88 274 288 192 136 257), lower := (rows 97 38 133 88 274 288 192 136 256), losses := [] }

theorem u172 : Upper (D 9) (R 9) [96,36,129,80,258,256,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b172 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 306, targets := 65 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 38 140 88 400 288 65 129 258), lower := (rows 97 38 140 88 400 288 65 129 256), losses := [] }

theorem u173 : Upper (D 9) (R 9) [96,36,136,80,384,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b173 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 65, targets := 256 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,7)], upper := (rows 97 38 140 88 400 288 65 130 257), lower := (rows 97 38 140 88 400 288 65 130 256), losses := [] }

theorem u174 : Upper (D 9) (R 9) [96,36,136,80,384,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b174 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 182, targets := 320 }], pairs := [(1,6),(1,8),(2,6)], upper := (rows 97 38 140 265 145 48 320 130 320), lower := (rows 97 38 140 265 145 48 320 130 256), losses := [] }

theorem u175 : Upper (D 9) (R 9) [96,36,136,257,129,16,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b175 [(5,4),(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 140 265 145 48 320 192 258), lower := (rows 97 38 140 265 145 48 320 192 256), losses := [] }

theorem u176 : Upper (D 9) (R 9) [96,36,136,257,129,16,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b176 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 182, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 38 140 265 400 48 65 130 320), lower := (rows 97 38 140 265 400 48 65 130 256), losses := [] }

theorem u177 : Upper (D 9) (R 9) [96,36,136,257,384,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b177 [(5,4),(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 38 140 265 400 48 65 192 258), lower := (rows 97 38 140 265 400 48 65 192 256), losses := [] }

theorem u178 : Upper (D 9) (R 9) [96,36,136,257,384,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b178 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 38 140 280 145 33 320 130 320), lower := (rows 97 38 140 280 145 33 320 130 256), losses := [] }

theorem u179 : Upper (D 9) (R 9) [96,36,136,272,129,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b179 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P09
