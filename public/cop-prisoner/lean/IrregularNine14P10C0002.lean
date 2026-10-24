import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0000

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 296 336 33 96 144 400), lower := (rows 7 74 164 296 336 33 96 128 256), losses := [] }

theorem u120 : Upper (D 10) (R 10) [6,72,160,288,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b120 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r121 : Route 9 := (fun mask => (mask,id))

def c121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u121 : Upper (D 10) (R 10) [6,72,160,288,320,1,128] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,320,1,128] 13 (by decide) (choices 1) [16,32] r121 c121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b122 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 7 74 164 296 400 33 80 224 352), lower := (rows 7 74 164 296 400 33 80 128 256), losses := [] }

theorem u122 : Upper (D 10) (R 10) [6,72,160,288,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b122 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 296 400 33 96 208 336), lower := (rows 7 74 164 296 400 33 96 128 256), losses := [] }

theorem u123 : Upper (D 10) (R 10) [6,72,160,288,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b123 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 296 400 96 65 176 304), lower := (rows 7 74 164 296 400 96 65 128 256), losses := [] }

theorem u124 : Upper (D 10) (R 10) [6,72,160,288,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b124 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 296 400 96 80 161 289), lower := (rows 7 74 164 296 400 96 80 128 256), losses := [] }

theorem u125 : Upper (D 10) (R 10) [6,72,160,288,384,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b125 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 400, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 74 164 296 400 96 96 145 273), lower := (rows 7 74 164 296 400 96 96 128 256), losses := [] }

theorem u126 : Upper (D 10) (R 10) [6,72,160,288,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b126 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 392 304 96 65 176 304), lower := (rows 7 74 164 392 304 96 65 128 256), losses := [] }

theorem u127 : Upper (D 10) (R 10) [6,72,160,384,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b127 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 392 304 96 80 161 289), lower := (rows 7 74 164 392 304 96 80 128 256), losses := [] }

theorem u128 : Upper (D 10) (R 10) [6,72,160,384,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b128 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 392 304 96 96 145 273), lower := (rows 7 74 164 392 304 96 96 128 256), losses := [] }

theorem u129 : Upper (D 10) (R 10) [6,72,160,384,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b129 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 388 152 304 96 65 160 288), lower := (rows 7 74 388 152 304 96 65 128 256), losses := [] }

theorem u130 : Upper (D 10) (R 10) [6,72,384,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b130 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 74 388 152 304 96 96 161 289), lower := (rows 7 74 388 152 304 96 96 128 256), losses := [] }

theorem u131 : Upper (D 10) (R 10) [6,72,384,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b131 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 107, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 388 168 304 96 65 176 304), lower := (rows 7 74 388 168 304 96 65 128 256), losses := [] }

theorem u132 : Upper (D 10) (R 10) [6,72,384,160,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b132 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 388 168 304 96 80 161 289), lower := (rows 7 74 388 168 304 96 80 128 256), losses := [] }

theorem u133 : Upper (D 10) (R 10) [6,72,384,160,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b133 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 107, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 388 168 304 96 96 145 273), lower := (rows 7 74 388 168 304 96 96 128 256), losses := [] }

theorem u134 : Upper (D 10) (R 10) [6,72,384,160,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b134 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 41 208 288 72 400 272), lower := (rows 7 98 164 41 208 288 72 128 256), losses := [] }

theorem u135 : Upper (D 10) (R 10) [6,96,160,33,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b135 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 83, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 41 208 288 80 392 264), lower := (rows 7 98 164 41 208 288 80 128 256), losses := [] }

theorem u136 : Upper (D 10) (R 10) [6,96,160,33,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b136 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 157, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 98 164 41 208 288 320 152 280), lower := (rows 7 98 164 41 208 288 320 128 256), losses := [] }

theorem u137 : Upper (D 10) (R 10) [6,96,160,33,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b137 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 133, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 41 280 288 80 192 448), lower := (rows 7 98 164 41 280 288 80 128 256), losses := [] }

theorem u138 : Upper (D 10) (R 10) [6,96,160,33,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b138 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 41 280 288 192 208 336), lower := (rows 7 98 164 41 280 288 192 128 256), losses := [] }

theorem u139 : Upper (D 10) (R 10) [6,96,160,33,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b139 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 56 208 288 65 392 264), lower := (rows 7 98 164 56 208 288 65 128 256), losses := [] }

theorem u140 : Upper (D 10) (R 10) [6,96,160,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b140 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 56 208 288 72 385 257), lower := (rows 7 98 164 56 208 288 72 128 256), losses := [] }

theorem u141 : Upper (D 10) (R 10) [6,96,160,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b141 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 157, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 98 164 56 208 288 320 137 265), lower := (rows 7 98 164 56 208 288 320 128 256), losses := [] }

theorem u142 : Upper (D 10) (R 10) [6,96,160,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b142 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 7 98 164 88 400 33 72 416 288), lower := (rows 7 98 164 88 400 33 72 128 256), losses := [] }

theorem u143 : Upper (D 10) (R 10) [6,96,160,80,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b143 [(5,0),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 88 400 33 96 392 264), lower := (rows 7 98 164 88 400 33 96 128 256), losses := [] }

theorem u144 : Upper (D 10) (R 10) [6,96,160,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b144 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 88 400 33 320 168 296), lower := (rows 7 98 164 88 400 33 320 128 256), losses := [] }

theorem u145 : Upper (D 10) (R 10) [6,96,160,80,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b145 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 7 98 164 200 273 48 72 416 288), lower := (rows 7 98 164 200 273 48 72 128 256), losses := [] }

theorem u146 : Upper (D 10) (R 10) [6,96,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b146 [(5,4),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 273 48 96 392 264), lower := (rows 7 98 164 200 273 48 96 128 256), losses := [] }

theorem u147 : Upper (D 10) (R 10) [6,96,160,192,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b147 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 141, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 273 48 320 168 296), lower := (rows 7 98 164 200 273 48 320 128 256), losses := [] }

theorem u148 : Upper (D 10) (R 10) [6,96,160,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b148 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 200 273 288 72 176 304), lower := (rows 7 98 164 200 273 288 72 128 256), losses := [] }

theorem u149 : Upper (D 10) (R 10) [6,96,160,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b149 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 141, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 273 288 80 168 296), lower := (rows 7 98 164 200 273 288 80 128 256), losses := [] }

theorem u150 : Upper (D 10) (R 10) [6,96,160,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b150 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 200 273 288 96 152 280), lower := (rows 7 98 164 200 273 288 96 128 256), losses := [] }

theorem u151 : Upper (D 10) (R 10) [6,96,160,192,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b151 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 280 288 65 176 304), lower := (rows 7 98 164 200 280 288 65 128 256), losses := [] }

theorem u152 : Upper (D 10) (R 10) [6,96,160,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b152 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 133, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 280 288 80 161 289), lower := (rows 7 98 164 200 280 288 80 128 256), losses := [] }

theorem u153 : Upper (D 10) (R 10) [6,96,160,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b153 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 200 280 288 96 145 273), lower := (rows 7 98 164 200 280 288 96 128 256), losses := [] }

theorem u154 : Upper (D 10) (R 10) [6,96,160,192,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b154 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 7 98 164 265 336 40 80 160 416), lower := (rows 7 98 164 265 336 40 80 128 256), losses := [] }

theorem u155 : Upper (D 10) (R 10) [6,96,160,257,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b155 [(5,3),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 265 336 40 96 144 400), lower := (rows 7 98 164 265 336 40 96 128 256), losses := [] }

theorem u156 : Upper (D 10) (R 10) [6,96,160,257,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b156 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 265 336 40 192 176 304), lower := (rows 7 98 164 265 336 40 192 128 256), losses := [] }

theorem u157 : Upper (D 10) (R 10) [6,96,160,257,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b157 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 7 98 164 328 400 33 72 176 304), lower := (rows 7 98 164 328 400 33 72 128 256), losses := [] }

theorem u158 : Upper (D 10) (R 10) [6,96,160,320,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b158 [(5,0),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 7 98 164 328 400 33 80 168 296), lower := (rows 7 98 164 328 400 33 80 128 256), losses := [] }

theorem u159 : Upper (D 10) (R 10) [6,96,160,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b159 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 328 400 33 96 152 280), lower := (rows 7 98 164 328 400 33 96 128 256), losses := [] }

theorem u160 : Upper (D 10) (R 10) [6,96,160,320,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b160 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 152, targets := 256 }], pairs := [(3,8)], upper := (rows 7 98 388 56 208 288 65 168 296), lower := (rows 7 98 388 56 208 288 65 128 256), losses := [] }

theorem u161 : Upper (D 10) (R 10) [6,96,384,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b161 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 56 208 288 72 161 289), lower := (rows 7 98 388 56 208 288 72 128 256), losses := [] }

theorem u162 : Upper (D 10) (R 10) [6,96,384,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b162 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 388 56 208 288 96 137 265), lower := (rows 7 98 388 56 208 288 96 128 256), losses := [] }

theorem u163 : Upper (D 10) (R 10) [6,96,384,48,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b163 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 152, targets := 256 }], pairs := [(3,8)], upper := (rows 7 98 388 88 176 288 65 168 296), lower := (rows 7 98 388 88 176 288 65 128 256), losses := [] }

theorem u164 : Upper (D 10) (R 10) [6,96,384,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b164 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 88 176 288 72 161 289), lower := (rows 7 98 388 88 176 288 72 128 256), losses := [] }

theorem u165 : Upper (D 10) (R 10) [6,96,384,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b165 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 66, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 98 388 88 176 288 96 137 265), lower := (rows 7 98 388 88 176 288 96 128 256), losses := [] }

theorem u166 : Upper (D 10) (R 10) [6,96,384,80,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b166 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 7 98 388 152 336 33 72 160 288), lower := (rows 7 98 388 152 336 33 72 128 256), losses := [] }

theorem u167 : Upper (D 10) (R 10) [6,96,384,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b167 [(5,0),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 388 152 336 33 96 168 296), lower := (rows 7 98 388 152 336 33 96 128 256), losses := [] }

theorem u168 : Upper (D 10) (R 10) [6,96,384,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b168 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 112 288 80 384 384), lower := (rows 35 70 44 137 112 288 80 128 256), losses := [] }

theorem u169 : Upper (D 10) (R 10) [34,68,40,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b169 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 35 70 44 137 112 288 192 400 272), lower := (rows 35 70 44 137 112 288 192 128 256), losses := [] }

theorem u170 : Upper (D 10) (R 10) [34,68,40,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b170 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 137 112 288 320 144 400), lower := (rows 35 70 44 137 112 288 320 128 256), losses := [] }

theorem u171 : Upper (D 10) (R 10) [34,68,40,129,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b171 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 208 288 80 416 288), lower := (rows 35 70 44 137 208 288 80 128 256), losses := [] }

theorem u172 : Upper (D 10) (R 10) [34,68,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b172 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 44 137 208 288 96 400 272), lower := (rows 35 70 44 137 208 288 96 128 256), losses := [] }

theorem u173 : Upper (D 10) (R 10) [34,68,40,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b173 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 48, camps := [], pairs := [(0,6),(1,5)], upper := (rows 35 70 44 137 208 288 320 176 304), lower := (rows 35 70 44 137 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 352 128 256), good := (rows 67 70 78 137 208 320 320 128 320) },{ target := 6, region := (rows 3 2 4 8 16 368 0 144 272), good := (rows 35 39 44 137 432 288 288 128 288) }] }

theorem u174 : Upper (D 10) (R 10) [34,68,40,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b174 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 336 288 80 160 416), lower := (rows 35 70 44 137 336 288 80 128 256), losses := [] }

theorem u175 : Upper (D 10) (R 10) [34,68,40,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b175 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 44 137 336 288 96 144 400), lower := (rows 35 70 44 137 336 288 96 128 256), losses := [] }

theorem u176 : Upper (D 10) (R 10) [34,68,40,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b176 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 35 70 44 137 336 288 192 176 304), lower := (rows 35 70 44 137 336 288 192 128 256), losses := [] }

theorem u177 : Upper (D 10) (R 10) [34,68,40,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b177 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 112 288 65 384 384), lower := (rows 35 70 44 152 112 288 65 128 256), losses := [] }

theorem u178 : Upper (D 10) (R 10) [34,68,40,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b178 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 35 70 44 152 112 288 192 385 257), lower := (rows 35 70 44 152 112 288 192 128 256), losses := [] }

theorem u179 : Upper (D 10) (R 10) [34,68,40,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b179 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P10
