import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 272, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 11 35 69 152 336 36 96 130 260), lower := (rows 11 35 69 152 336 36 96 130 256), losses := [] }

theorem u120 : Upper (D 6) (R 6) [10,33,65,144,320,4,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 11 35 69 152 336 36 96 132 258), lower := (rows 11 35 69 152 336 36 96 132 256), losses := [] }

theorem u121 : Upper (D 6) (R 6) [10,33,65,144,320,4,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 144, targets := 68 }], pairs := [(4,2),(4,6)], upper := (rows 11 35 70 88 176 36 320 129 260), lower := (rows 11 35 70 88 176 36 320 129 256), losses := [] }

theorem u122 : Upper (D 6) (R 6) [10,33,66,80,160,4,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b122 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 88 176 36 320 132 257), lower := (rows 11 35 70 88 176 36 320 132 256), losses := [] }

theorem u123 : Upper (D 6) (R 6) [10,33,66,80,160,4,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b123 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 139, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 152 304 96 68 129 260), lower := (rows 11 35 70 152 304 96 68 129 256), losses := [] }

theorem u124 : Upper (D 6) (R 6) [10,33,66,144,288,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 152 304 96 68 132 257), lower := (rows 11 35 70 152 304 96 68 132 256), losses := [] }

theorem u125 : Upper (D 6) (R 6) [10,33,66,144,288,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 140 276 96 65 130 288), lower := (rows 11 35 84 140 276 96 65 130 256), losses := [] }

theorem u126 : Upper (D 6) (R 6) [10,33,80,132,260,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 35 84 140 276 96 65 160 258), lower := (rows 11 35 84 140 276 96 65 160 256), losses := [] }

theorem u127 : Upper (D 6) (R 6) [10,33,80,132,260,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 140 304 96 65 130 260), lower := (rows 11 35 84 140 304 96 65 130 256), losses := [] }

theorem u128 : Upper (D 6) (R 6) [10,33,80,132,288,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 84 140 304 96 65 132 258), lower := (rows 11 35 84 140 304 96 65 132 256), losses := [] }

theorem u129 : Upper (D 6) (R 6) [10,33,80,132,288,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 200 273 36 96 130 260), lower := (rows 11 35 84 200 273 36 96 130 256), losses := [] }

theorem u130 : Upper (D 6) (R 6) [10,33,80,192,257,4,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 236, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 84 200 273 36 96 132 258), lower := (rows 11 35 84 200 273 36 96 132 256), losses := [] }

theorem u131 : Upper (D 6) (R 6) [10,33,80,192,257,4,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 200 274 36 96 129 260), lower := (rows 11 35 84 200 274 36 96 129 256), losses := [] }

theorem u132 : Upper (D 6) (R 6) [10,33,80,192,258,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 236, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 84 200 274 36 96 132 257), lower := (rows 11 35 84 200 274 36 96 132 256), losses := [] }

theorem u133 : Upper (D 6) (R 6) [10,33,80,192,258,4,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 84 200 304 36 66 129 260), lower := (rows 11 35 84 200 304 36 66 129 256), losses := [] }

theorem u134 : Upper (D 6) (R 6) [10,33,80,192,288,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 3 },{ cop := 1, region := 272, targets := 2 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 35 84 200 304 36 66 132 257), lower := (rows 11 35 84 200 304 36 66 132 256), losses := [] }

theorem u135 : Upper (D 6) (R 6) [10,33,80,192,288,4,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 88 148 288 66 129 260), lower := (rows 11 35 100 88 148 288 66 129 256), losses := [] }

theorem u136 : Upper (D 6) (R 6) [10,33,96,80,132,256,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b136 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 152, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 100 88 148 288 66 132 257), lower := (rows 11 35 100 88 148 288 66 132 256), losses := [] }

theorem u137 : Upper (D 6) (R 6) [10,33,96,80,132,256,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b137 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 140 276 48 65 130 320), lower := (rows 11 35 100 140 276 48 65 130 256), losses := [] }

theorem u138 : Upper (D 6) (R 6) [10,33,96,132,260,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b138 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 100 140 276 48 65 192 258), lower := (rows 11 35 100 140 276 48 65 192 256), losses := [] }

theorem u139 : Upper (D 6) (R 6) [10,33,96,132,260,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b139 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 140 276 48 66 129 320), lower := (rows 11 35 100 140 276 48 66 129 256), losses := [] }

theorem u140 : Upper (D 6) (R 6) [10,33,96,132,260,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 100 140 276 48 66 192 257), lower := (rows 11 35 100 140 276 48 66 192 256), losses := [] }

theorem u141 : Upper (D 6) (R 6) [10,33,96,132,260,16,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b141 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 152 336 36 65 130 260), lower := (rows 11 35 100 152 336 36 65 130 256), losses := [] }

theorem u142 : Upper (D 6) (R 6) [10,33,96,144,320,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 152 336 36 65 132 258), lower := (rows 11 35 100 152 336 36 65 132 256), losses := [] }

theorem u143 : Upper (D 6) (R 6) [10,33,96,144,320,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 152 336 36 66 129 260), lower := (rows 11 35 100 152 336 36 66 129 256), losses := [] }

theorem u144 : Upper (D 6) (R 6) [10,33,96,144,320,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 152 336 36 66 132 257), lower := (rows 11 35 100 152 336 36 66 132 256), losses := [] }

theorem u145 : Upper (D 6) (R 6) [10,33,96,144,320,4,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 35 100 200 276 48 66 129 260), lower := (rows 11 35 100 200 276 48 66 129 256), losses := [] }

theorem u146 : Upper (D 6) (R 6) [10,33,96,192,260,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b146 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 100 200 276 48 66 132 257), lower := (rows 11 35 100 200 276 48 66 132 256), losses := [] }

theorem u147 : Upper (D 6) (R 6) [10,33,96,192,260,16,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b147 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 13 336 96 68 130 288), lower := (rows 11 35 148 13 336 96 68 130 256), losses := [] }

theorem u148 : Upper (D 6) (R 6) [10,33,144,5,320,64,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 2, camps := [{ cop := 8, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 13 336 96 68 160 258), lower := (rows 11 35 148 13 336 96 68 160 256), losses := [] }

theorem u149 : Upper (D 6) (R 6) [10,33,144,5,320,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 148, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 148 268 52 96 65 130 320), lower := (rows 11 35 148 268 52 96 65 130 256), losses := [] }

theorem u150 : Upper (D 6) (R 6) [10,33,144,260,36,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 268 52 96 65 192 258), lower := (rows 11 35 148 268 52 96 65 192 256), losses := [] }

theorem u151 : Upper (D 6) (R 6) [10,33,144,260,36,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 148, targets := 2 },{ cop := 1, region := 148, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 35 148 268 52 96 66 129 320), lower := (rows 11 35 148 268 52 96 66 129 256), losses := [] }

theorem u152 : Upper (D 6) (R 6) [10,33,144,260,36,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 268 52 96 66 192 257), lower := (rows 11 35 148 268 52 96 66 192 256), losses := [] }

theorem u153 : Upper (D 6) (R 6) [10,33,144,260,36,64,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 35 148 268 84 96 65 130 288), lower := (rows 11 35 148 268 84 96 65 130 256), losses := [] }

theorem u154 : Upper (D 6) (R 6) [10,33,144,260,68,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 268 84 96 65 160 258), lower := (rows 11 35 148 268 84 96 65 160 256), losses := [] }

theorem u155 : Upper (D 6) (R 6) [10,33,144,260,68,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 35 164 76 276 48 65 130 320), lower := (rows 11 35 164 76 276 48 65 130 256), losses := [] }

theorem u156 : Upper (D 6) (R 6) [10,33,160,68,260,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b156 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 307, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 76 276 48 65 192 258), lower := (rows 11 35 164 76 276 48 65 192 256), losses := [] }

theorem u157 : Upper (D 6) (R 6) [10,33,160,68,260,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b157 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 164 76 276 48 66 129 320), lower := (rows 11 35 164 76 276 48 66 129 256), losses := [] }

theorem u158 : Upper (D 6) (R 6) [10,33,160,68,260,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b158 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 307, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 76 276 48 66 192 257), lower := (rows 11 35 164 76 276 48 66 192 256), losses := [] }

theorem u159 : Upper (D 6) (R 6) [10,33,160,68,260,16,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b159 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 148, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 35 164 268 21 96 80 130 320), lower := (rows 11 35 164 268 21 96 80 130 256), losses := [] }

theorem u160 : Upper (D 6) (R 6) [10,33,160,260,5,64,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b160 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 267, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 268 21 96 80 192 258), lower := (rows 11 35 164 268 21 96 80 192 256), losses := [] }

theorem u161 : Upper (D 6) (R 6) [10,33,160,260,5,64,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b161 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 35 164 268 84 48 65 130 320), lower := (rows 11 35 164 268 84 48 65 130 256), losses := [] }

theorem u162 : Upper (D 6) (R 6) [10,33,160,260,68,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b162 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 180, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 164 268 84 48 65 192 258), lower := (rows 11 35 164 268 84 48 65 192 256), losses := [] }

theorem u163 : Upper (D 6) (R 6) [10,33,160,260,68,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b163 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 164 268 84 48 66 129 320), lower := (rows 11 35 164 268 84 48 66 129 256), losses := [] }

theorem u164 : Upper (D 6) (R 6) [10,33,160,260,68,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b164 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 180, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 164 268 84 48 66 192 257), lower := (rows 11 35 164 268 84 48 66 192 256), losses := [] }

theorem u165 : Upper (D 6) (R 6) [10,33,160,260,68,16,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b165 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 132, targets := 65 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 35 164 268 84 96 65 130 272), lower := (rows 11 35 164 268 84 96 65 130 256), losses := [] }

theorem u166 : Upper (D 6) (R 6) [10,33,160,260,68,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 164 268 84 96 65 144 258), lower := (rows 11 35 164 268 84 96 65 144 256), losses := [] }

theorem u167 : Upper (D 6) (R 6) [10,33,160,260,68,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b167 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 35 196 328 21 36 80 130 288), lower := (rows 11 35 196 328 21 36 80 130 256), losses := [] }

theorem u168 : Upper (D 6) (R 6) [10,33,192,320,5,4,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b168 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 196 328 21 36 80 160 258), lower := (rows 11 35 196 328 21 36 80 160 256), losses := [] }

theorem u169 : Upper (D 6) (R 6) [10,33,192,320,5,4,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b169 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 217, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 88 176 288 65 129 260), lower := (rows 11 38 70 88 176 288 65 129 256), losses := [] }

theorem u170 : Upper (D 6) (R 6) [10,36,66,80,160,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b170 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 65 }], pairs := [(4,0),(4,6)], upper := (rows 11 38 70 88 176 288 65 132 257), lower := (rows 11 38 70 88 176 288 65 132 256), losses := [] }

theorem u171 : Upper (D 6) (R 6) [10,36,66,80,160,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b171 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 200 274 33 96 129 260), lower := (rows 11 38 84 200 274 33 96 129 256), losses := [] }

theorem u172 : Upper (D 6) (R 6) [10,36,80,192,258,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 38 84 200 274 33 96 132 257), lower := (rows 11 38 84 200 274 33 96 132 256), losses := [] }

theorem u173 : Upper (D 6) (R 6) [10,36,80,192,258,1,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 200 276 33 96 129 258), lower := (rows 11 38 84 200 276 33 96 129 256), losses := [] }

theorem u174 : Upper (D 6) (R 6) [10,36,80,192,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 38 84 200 276 33 96 130 257), lower := (rows 11 38 84 200 276 33 96 130 256), losses := [] }

theorem u175 : Upper (D 6) (R 6) [10,36,80,192,260,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 132, targets := 96 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(2,6)], upper := (rows 11 38 133 25 276 96 96 130 320), lower := (rows 11 38 133 25 276 96 96 130 256), losses := [] }

theorem u176 : Upper (D 6) (R 6) [10,36,129,17,260,64,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 133 25 276 96 96 192 258), lower := (rows 11 38 133 25 276 96 96 192 256), losses := [] }

theorem u177 : Upper (D 6) (R 6) [10,36,129,17,260,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 133 28 273 96 66 160 320), lower := (rows 11 38 133 28 273 96 66 160 256), losses := [] }

theorem u178 : Upper (D 6) (R 6) [10,36,129,20,257,64,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 28 273 96 66 192 288), lower := (rows 11 38 133 28 273 96 66 192 256), losses := [] }

theorem u179 : Upper (D 6) (R 6) [10,36,129,20,257,64,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P06
