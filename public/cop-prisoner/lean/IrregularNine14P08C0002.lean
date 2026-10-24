import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 280 112 160 65 160 288), lower := (rows 7 67 140 280 112 160 65 128 256), losses := [] }

theorem u120 : Upper (D 8) (R 8) [6,65,136,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 280 112 160 96 161 289), lower := (rows 7 67 140 280 112 160 96 128 256), losses := [] }

theorem u121 : Upper (D 8) (R 8) [6,65,136,272,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 296 112 160 65 176 304), lower := (rows 7 67 140 296 112 160 65 128 256), losses := [] }

theorem u122 : Upper (D 8) (R 8) [6,65,136,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 140 296 112 160 80 161 289), lower := (rows 7 67 140 296 112 160 80 128 256), losses := [] }

theorem u123 : Upper (D 8) (R 8) [6,65,136,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b123 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 296 112 160 96 145 273), lower := (rows 7 67 140 296 112 160 96 128 256), losses := [] }

theorem u124 : Upper (D 8) (R 8) [6,65,136,288,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 176 96 65 176 304), lower := (rows 7 67 140 296 176 96 65 128 256), losses := [] }

theorem u125 : Upper (D 8) (R 8) [6,65,136,288,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 140 296 176 96 80 161 289), lower := (rows 7 67 140 296 176 96 80 128 256), losses := [] }

theorem u126 : Upper (D 8) (R 8) [6,65,136,288,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b126 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 296 176 96 96 145 273), lower := (rows 7 67 140 296 176 96 96 128 256), losses := [] }

theorem u127 : Upper (D 8) (R 8) [6,65,136,288,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 280 96 65 160 416), lower := (rows 7 67 164 56 280 96 65 128 256), losses := [] }

theorem u128 : Upper (D 8) (R 8) [6,65,160,48,264,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 56 280 96 96 129 385), lower := (rows 7 67 164 56 280 96 96 128 256), losses := [] }

theorem u129 : Upper (D 8) (R 8) [6,65,160,48,264,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 312, targets := 128 }], pairs := [(3,7)], upper := (rows 7 67 164 56 280 96 192 161 289), lower := (rows 7 67 164 56 280 96 192 128 256), losses := [] }

theorem u130 : Upper (D 8) (R 8) [6,65,160,48,264,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 400 96 65 168 296), lower := (rows 7 67 164 56 400 96 65 128 256), losses := [] }

theorem u131 : Upper (D 8) (R 8) [6,65,160,48,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 164 56 400 96 72 161 289), lower := (rows 7 67 164 56 400 96 72 128 256), losses := [] }

theorem u132 : Upper (D 8) (R 8) [6,65,160,48,384,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b132 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 56 400 96 96 137 265), lower := (rows 7 67 164 56 400 96 96 128 256), losses := [] }

theorem u133 : Upper (D 8) (R 8) [6,65,160,48,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 152 304 96 65 168 296), lower := (rows 7 67 164 152 304 96 65 128 256), losses := [] }

theorem u134 : Upper (D 8) (R 8) [6,65,160,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 164 152 304 96 72 161 289), lower := (rows 7 67 164 152 304 96 72 128 256), losses := [] }

theorem u135 : Upper (D 8) (R 8) [6,65,160,144,288,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b135 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 152 304 96 96 137 265), lower := (rows 7 67 164 152 304 96 96 128 256), losses := [] }

theorem u136 : Upper (D 8) (R 8) [6,65,160,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 268 152 112 160 65 160 288), lower := (rows 7 67 268 152 112 160 65 128 256), losses := [] }

theorem u137 : Upper (D 8) (R 8) [6,65,264,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 268 152 112 160 96 161 289), lower := (rows 7 67 268 152 112 160 96 128 256), losses := [] }

theorem u138 : Upper (D 8) (R 8) [6,65,264,144,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 56 152 96 65 160 416), lower := (rows 7 67 292 56 152 96 65 128 256), losses := [] }

theorem u139 : Upper (D 8) (R 8) [6,65,288,48,136,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 56 152 96 96 129 385), lower := (rows 7 67 292 56 152 96 96 128 256), losses := [] }

theorem u140 : Upper (D 8) (R 8) [6,65,288,48,136,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 263, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 56 152 96 192 161 289), lower := (rows 7 67 292 56 152 96 192 128 256), losses := [] }

theorem u141 : Upper (D 8) (R 8) [6,65,288,48,136,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 404, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 104 152 160 65 176 304), lower := (rows 7 67 292 104 152 160 65 128 256), losses := [] }

theorem u142 : Upper (D 8) (R 8) [6,65,288,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 292 104 152 160 80 161 289), lower := (rows 7 67 292 104 152 160 80 128 256), losses := [] }

theorem u143 : Upper (D 8) (R 8) [6,65,288,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b143 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 104 152 160 96 145 273), lower := (rows 7 67 292 104 152 160 96 128 256), losses := [] }

theorem u144 : Upper (D 8) (R 8) [6,65,288,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 25 304 96 65 160 416), lower := (rows 7 74 164 25 304 96 65 128 256), losses := [] }

theorem u145 : Upper (D 8) (R 8) [6,72,160,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 25 304 96 96 129 385), lower := (rows 7 74 164 25 304 96 96 128 256), losses := [] }

theorem u146 : Upper (D 8) (R 8) [6,72,160,17,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 25 304 96 192 161 289), lower := (rows 7 74 164 25 304 96 192 128 256), losses := [] }

theorem u147 : Upper (D 8) (R 8) [6,72,160,17,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 56 273 96 65 160 416), lower := (rows 7 74 164 56 273 96 65 128 256), losses := [] }

theorem u148 : Upper (D 8) (R 8) [6,72,160,48,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 56 273 96 96 129 385), lower := (rows 7 74 164 56 273 96 96 128 256), losses := [] }

theorem u149 : Upper (D 8) (R 8) [6,72,160,48,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 56 273 96 192 161 289), lower := (rows 7 74 164 56 273 96 192 128 256), losses := [] }

theorem u150 : Upper (D 8) (R 8) [6,72,160,48,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r151 : Route 9 := (fun mask => (mask,id))

def c151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u151 : Upper (D 8) (R 8) [6,72,160,48,384,64,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,384,64,1] 13 (by decide) (choices 1) [1,32] r151 c151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b152 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 56 400 96 96 129 257), lower := (rows 7 74 164 56 400 96 96 128 256), losses := [] }

theorem u152 : Upper (D 8) (R 8) [6,72,160,48,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 394, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 296 112 33 65 144 400), lower := (rows 7 74 164 296 112 33 65 128 256), losses := [] }

theorem u153 : Upper (D 8) (R 8) [6,72,160,288,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 74 164 296 112 33 80 129 385), lower := (rows 7 74 164 296 112 33 80 128 256), losses := [] }

theorem u154 : Upper (D 8) (R 8) [6,72,160,288,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b154 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 296 112 33 192 145 273), lower := (rows 7 74 164 296 112 33 192 128 256), losses := [] }

theorem u155 : Upper (D 8) (R 8) [6,72,160,288,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 48, camps := [], pairs := [(1,5)], upper := (rows 7 74 164 296 208 33 65 176 304), lower := (rows 7 74 164 296 208 33 65 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 20 0 97 128 256), good := (rows 87 74 212 330 208 65 65 128 256) }] }

theorem u156 : Upper (D 8) (R 8) [6,72,160,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 164 296 208 33 80 161 289), lower := (rows 7 74 164 296 208 33 80 128 256), losses := [] }

theorem u157 : Upper (D 8) (R 8) [6,72,160,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b157 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 296 208 33 96 145 273), lower := (rows 7 74 164 296 208 33 96 128 256), losses := [] }

theorem u158 : Upper (D 8) (R 8) [6,72,160,288,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 25 176 96 65 160 416), lower := (rows 7 74 292 25 176 96 65 128 256), losses := [] }

theorem u159 : Upper (D 8) (R 8) [6,72,288,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 25 176 96 96 129 385), lower := (rows 7 74 292 25 176 96 96 128 256), losses := [] }

theorem u160 : Upper (D 8) (R 8) [6,72,288,17,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 25 176 96 192 161 289), lower := (rows 7 74 292 25 176 96 192 128 256), losses := [] }

theorem u161 : Upper (D 8) (R 8) [6,72,288,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 41 112 160 65 144 400), lower := (rows 7 74 292 41 112 160 65 128 256), losses := [] }

theorem u162 : Upper (D 8) (R 8) [6,72,288,33,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 74 292 41 112 160 80 129 385), lower := (rows 7 74 292 41 112 160 80 128 256), losses := [] }

theorem u163 : Upper (D 8) (R 8) [6,72,288,33,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b163 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 41 112 160 192 145 273), lower := (rows 7 74 292 41 112 160 192 128 256), losses := [] }

theorem u164 : Upper (D 8) (R 8) [6,72,288,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 41 208 160 65 176 304), lower := (rows 7 74 292 41 208 160 65 128 256), losses := [] }

theorem u165 : Upper (D 8) (R 8) [6,72,288,33,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 292 41 208 160 80 161 289), lower := (rows 7 74 292 41 208 160 80 128 256), losses := [] }

theorem u166 : Upper (D 8) (R 8) [6,72,288,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b166 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 41 208 160 96 145 273), lower := (rows 7 74 292 41 208 160 96 128 256), losses := [] }

theorem u167 : Upper (D 8) (R 8) [6,72,288,33,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 56 145 96 65 160 416), lower := (rows 7 74 292 56 145 96 65 128 256), losses := [] }

theorem u168 : Upper (D 8) (R 8) [6,72,288,48,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 56 145 96 96 129 385), lower := (rows 7 74 292 56 145 96 96 128 256), losses := [] }

theorem u169 : Upper (D 8) (R 8) [6,72,288,48,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 56 145 96 192 161 289), lower := (rows 7 74 292 56 145 96 192 128 256), losses := [] }

theorem u170 : Upper (D 8) (R 8) [6,72,288,48,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 404, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 137 176 96 65 176 304), lower := (rows 7 74 292 137 176 96 65 128 256), losses := [] }

theorem u171 : Upper (D 8) (R 8) [6,72,288,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 292 137 176 96 80 161 289), lower := (rows 7 74 292 137 176 96 80 128 256), losses := [] }

theorem u172 : Upper (D 8) (R 8) [6,72,288,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b172 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 137 176 96 96 145 273), lower := (rows 7 74 292 137 176 96 96 128 256), losses := [] }

theorem u173 : Upper (D 8) (R 8) [6,72,288,129,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 138, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 168 112 33 65 144 400), lower := (rows 7 74 292 168 112 33 65 128 256), losses := [] }

theorem u174 : Upper (D 8) (R 8) [6,72,288,160,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 74 292 168 112 33 80 129 385), lower := (rows 7 74 292 168 112 33 80 128 256), losses := [] }

theorem u175 : Upper (D 8) (R 8) [6,72,288,160,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b175 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 168 112 33 192 145 273), lower := (rows 7 74 292 168 112 33 192 128 256), losses := [] }

theorem u176 : Upper (D 8) (R 8) [6,72,288,160,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 48, camps := [], pairs := [(1,5)], upper := (rows 7 74 292 168 208 33 65 176 304), lower := (rows 7 74 292 168 208 33 65 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 24 0 97 128 256), good := (rows 71 90 324 218 208 65 65 128 256) }] }

theorem u177 : Upper (D 8) (R 8) [6,72,288,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 292 168 208 33 80 161 289), lower := (rows 7 74 292 168 208 33 80 128 256), losses := [] }

theorem u178 : Upper (D 8) (R 8) [6,72,288,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b178 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 168 208 33 96 145 273), lower := (rows 7 74 292 168 208 33 96 128 256), losses := [] }

theorem u179 : Upper (D 8) (R 8) [6,72,288,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P08
