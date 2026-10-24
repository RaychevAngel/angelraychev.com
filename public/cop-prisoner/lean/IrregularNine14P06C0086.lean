import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5160 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 13 82 96 65 148 276), lower := (rows 11 162 292 13 82 96 65 128 256), losses := [] }

theorem u5160 : Upper (D 6) (R 6) [10,160,288,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5161 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 292 13 82 96 68 145 273), lower := (rows 11 162 292 13 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 260 8 17 381 332 128 256), good := (rows 122 162 356 124 114 96 100 128 356) }] }

theorem u5161 : Upper (D 6) (R 6) [10,160,288,5,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5162 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 292 13 82 96 80 133 261), lower := (rows 11 162 292 13 82 96 80 128 256), losses := [] }

theorem u5162 : Upper (D 6) (R 6) [10,160,288,5,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5162 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5163 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 292 13 84 48 65 194 322), lower := (rows 11 162 292 13 84 48 65 128 256), losses := [] }

theorem u5163 : Upper (D 6) (R 6) [10,160,288,5,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5163 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5164 : PairBound 9 := { available := 65, camps := [], pairs := [(4,0),(4,5)], upper := (rows 11 162 292 13 84 48 66 193 321), lower := (rows 11 162 292 13 84 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 57 67 128 256), good := (rows 122 226 292 124 116 48 66 128 256) },{ target := 5, region := (rows 1 2 4 8 24 0 67 137 265), good := (rows 475 194 260 477 84 16 66 128 256) }] }

theorem u5164 : Upper (D 6) (R 6) [10,160,288,5,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5164 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 13 84 96 65 146 274), lower := (rows 11 162 292 13 84 96 65 128 256), losses := [] }

theorem u5165 : Upper (D 6) (R 6) [10,160,288,5,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5166 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 292 13 84 96 66 145 273), lower := (rows 11 162 292 13 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 130 4 8 24 251 195 128 256), good := (rows 122 226 292 124 116 96 98 226 256) }] }

theorem u5166 : Upper (D 6) (R 6) [10,160,288,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5167 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 292 13 84 96 80 131 259), lower := (rows 11 162 292 13 84 96 80 128 256), losses := [] }

theorem u5167 : Upper (D 6) (R 6) [10,160,288,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5167 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5168 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 25 84 96 65 134 262), lower := (rows 11 162 292 25 84 96 65 128 256), losses := [] }

theorem u5168 : Upper (D 6) (R 6) [10,160,288,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5169 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 162 292 25 84 96 66 133 261), lower := (rows 11 162 292 25 84 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 112 64 137 265), good := (rows 397 160 292 445 116 96 96 128 256) }] }

theorem u5169 : Upper (D 6) (R 6) [10,160,288,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5170 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 292 25 84 96 68 131 259), lower := (rows 11 162 292 25 84 96 68 128 256), losses := [] }

theorem u5170 : Upper (D 6) (R 6) [10,160,288,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5171 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 292 28 81 33 66 196 324), lower := (rows 11 162 292 28 81 33 66 128 256), losses := [] }

theorem u5171 : Upper (D 6) (R 6) [10,160,288,20,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5172 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 292 28 81 33 68 194 322), lower := (rows 11 162 292 28 81 33 68 128 256), losses := [] }

theorem u5172 : Upper (D 6) (R 6) [10,160,288,20,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5173 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 292 28 81 96 65 134 262), lower := (rows 11 162 292 28 81 96 65 128 256), losses := [] }

theorem u5173 : Upper (D 6) (R 6) [10,160,288,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5174 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 292 28 81 96 66 133 261), lower := (rows 11 162 292 28 81 96 66 128 256), losses := [] }

theorem u5174 : Upper (D 6) (R 6) [10,160,288,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5175 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 11 162 292 28 81 96 68 131 259), lower := (rows 11 162 292 28 81 96 68 128 256), losses := [] }

theorem u5175 : Upper (D 6) (R 6) [10,160,288,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5176 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 292 28 82 33 65 196 324), lower := (rows 11 162 292 28 82 33 65 128 256), losses := [] }

theorem u5176 : Upper (D 6) (R 6) [10,160,288,20,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5177 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 11 162 292 28 82 33 68 193 321), lower := (rows 11 162 292 28 82 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 32 76 128 256), good := (rows 90 162 356 92 82 48 68 128 256) },{ target := 1, region := (rows 1 0 39 24 16 33 127 161 289), good := (rows 493 484 484 92 92 485 68 128 256) }] }

theorem u5177 : Upper (D 6) (R 6) [10,160,288,20,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5178 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 292 28 82 96 65 133 261), lower := (rows 11 162 292 28 82 96 65 128 256), losses := [] }

theorem u5178 : Upper (D 6) (R 6) [10,160,288,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5179 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 292 28 82 96 68 129 257), lower := (rows 11 162 292 28 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 260 8 17 381 332 128 256), good := (rows 122 162 356 124 114 96 100 128 356) }] }

theorem u5179 : Upper (D 6) (R 6) [10,160,288,20,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5180 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 292 73 21 96 66 148 276), lower := (rows 11 162 292 73 21 96 66 128 256), losses := [] }

theorem u5180 : Upper (D 6) (R 6) [10,160,288,65,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5181 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 162 292 73 21 96 68 146 274), lower := (rows 11 162 292 73 21 96 68 128 256), losses := [] }

theorem u5181 : Upper (D 6) (R 6) [10,160,288,65,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5182 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 162 292 73 21 96 80 134 262), lower := (rows 11 162 292 73 21 96 80 128 256), losses := [] }

theorem u5182 : Upper (D 6) (R 6) [10,160,288,65,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5182 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5183 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 292 73 22 96 65 148 276), lower := (rows 11 162 292 73 22 96 65 128 256), losses := [] }

theorem u5183 : Upper (D 6) (R 6) [10,160,288,65,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5184 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 73, targets := 32 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 162 292 73 22 96 68 145 273), lower := (rows 11 162 292 73 22 96 68 128 256), losses := [] }

theorem u5184 : Upper (D 6) (R 6) [10,160,288,65,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5185 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 292 73 22 96 80 133 261), lower := (rows 11 162 292 73 22 96 80 128 256), losses := [] }

theorem u5185 : Upper (D 6) (R 6) [10,160,288,65,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5185 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5186 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 292 73 84 48 65 134 262), lower := (rows 11 162 292 73 84 48 65 128 256), losses := [] }

theorem u5186 : Upper (D 6) (R 6) [10,160,288,65,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5186 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5187 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 292 73 84 48 66 133 261), lower := (rows 11 162 292 73 84 48 66 128 256), losses := [] }

theorem u5187 : Upper (D 6) (R 6) [10,160,288,65,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5187 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5188 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 292 73 84 48 68 131 259), lower := (rows 11 162 292 73 84 48 68 128 256), losses := [] }

theorem u5188 : Upper (D 6) (R 6) [10,160,288,65,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5188 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,5)], upper := (rows 11 162 292 76 21 33 66 208 336), lower := (rows 11 162 292 76 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 67 144 272), good := (rows 74 226 292 76 476 96 66 128 256) },{ target := 5, region := (rows 1 2 4 24 16 0 67 144 272), good := (rows 75 194 260 76 477 65 66 128 256) }] }

theorem u5189 : Upper (D 6) (R 6) [10,160,288,68,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 292 76 21 33 80 194 322), lower := (rows 11 162 292 76 21 33 80 128 256), losses := [] }

theorem u5190 : Upper (D 6) (R 6) [10,160,288,68,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5190 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 72, targets := 2 },{ cop := 4, region := 226, targets := 4 },{ cop := 4, region := 72, targets := 32 }], pairs := [(1,2),(3,1),(3,5)], upper := (rows 11 162 292 76 21 96 65 146 274), lower := (rows 11 162 292 76 21 96 65 128 256), losses := [] }

theorem u5191 : Upper (D 6) (R 6) [10,160,288,68,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5192 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 162 292 76 21 96 66 145 273), lower := (rows 11 162 292 76 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 130 4 24 16 251 195 128 256), good := (rows 106 226 292 108 124 96 98 226 256) }] }

theorem u5192 : Upper (D 6) (R 6) [10,160,288,68,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5193 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 292 76 21 96 80 131 259), lower := (rows 11 162 292 76 21 96 80 128 256), losses := [] }

theorem u5193 : Upper (D 6) (R 6) [10,160,288,68,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5193 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5194 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 162 292 76 22 33 65 208 336), lower := (rows 11 162 292 76 22 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 97 97 128 256), good := (rows 105 224 364 108 28 97 97 128 256) }] }

theorem u5194 : Upper (D 6) (R 6) [10,160,288,68,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5195 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 292 76 22 33 80 193 321), lower := (rows 11 162 292 76 22 33 80 128 256), losses := [] }

theorem u5195 : Upper (D 6) (R 6) [10,160,288,68,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5195 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5196 : Route 9 := (fun mask => (mask,id))

def c5196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5196 : Upper (D 6) (R 6) [10,160,288,68,6,64,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,6,64,1] 13 (by decide) (choices 1) [1,16] r5196 c5196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u382
  · exact u383

def b5197 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 292 76 22 96 80 129 257), lower := (rows 11 162 292 76 22 96 80 128 256), losses := [] }

theorem u5197 : Upper (D 6) (R 6) [10,160,288,68,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5197 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5198 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 162 292 76 81 33 66 148 276), lower := (rows 11 162 292 76 81 33 66 128 256), losses := [] }

theorem u5198 : Upper (D 6) (R 6) [10,160,288,68,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5199 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 292 76 81 33 68 146 274), lower := (rows 11 162 292 76 81 33 68 128 256), losses := [] }

theorem u5199 : Upper (D 6) (R 6) [10,160,288,68,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5200 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 162 292 76 81 33 80 134 262), lower := (rows 11 162 292 76 81 33 80 128 256), losses := [] }

theorem u5200 : Upper (D 6) (R 6) [10,160,288,68,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5200 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5201 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 292 76 82 33 65 148 276), lower := (rows 11 162 292 76 82 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 97 97 144 272), good := (rows 105 224 364 108 508 97 97 128 256) }] }

theorem u5201 : Upper (D 6) (R 6) [10,160,288,68,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5202 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 292 76 82 33 68 145 273), lower := (rows 11 162 292 76 82 33 68 128 256), losses := [] }

theorem u5202 : Upper (D 6) (R 6) [10,160,288,68,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5203 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 292 76 82 33 80 133 261), lower := (rows 11 162 292 76 82 33 80 128 256), losses := [] }

theorem u5203 : Upper (D 6) (R 6) [10,160,288,68,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5203 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,2),(4,5)], upper := (rows 11 162 292 76 82 48 65 133 261), lower := (rows 11 162 292 76 82 48 65 128 256), losses := [] }

theorem u5204 : Upper (D 6) (R 6) [10,160,288,68,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5204 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5205 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 292 76 82 48 68 129 257), lower := (rows 11 162 292 76 82 48 68 128 256), losses := [] }

theorem u5205 : Upper (D 6) (R 6) [10,160,288,68,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5205 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5206 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 292 88 21 96 65 134 262), lower := (rows 11 162 292 88 21 96 65 128 256), losses := [] }

theorem u5206 : Upper (D 6) (R 6) [10,160,288,80,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5207 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 162 292 88 21 96 66 133 261), lower := (rows 11 162 292 88 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 130 4 24 16 251 195 128 256), good := (rows 106 226 292 120 124 96 98 226 256) }] }

theorem u5207 : Upper (D 6) (R 6) [10,160,288,80,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5208 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 292 88 21 96 68 131 259), lower := (rows 11 162 292 88 21 96 68 128 256), losses := [] }

theorem u5208 : Upper (D 6) (R 6) [10,160,288,80,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5209 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 162 324 13 81 36 66 176 304), lower := (rows 11 162 324 13 81 36 66 128 256), losses := [] }

theorem u5209 : Upper (D 6) (R 6) [10,160,320,5,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5210 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 324 13 81 36 80 162 290), lower := (rows 11 162 324 13 81 36 80 128 256), losses := [] }

theorem u5210 : Upper (D 6) (R 6) [10,160,320,5,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5210 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5211 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 3, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 162 324 13 81 36 96 146 274), lower := (rows 11 162 324 13 81 36 96 128 256), losses := [] }

theorem u5211 : Upper (D 6) (R 6) [10,160,320,5,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5212 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 13 82 36 65 176 304), lower := (rows 11 162 324 13 82 36 65 128 256), losses := [] }

theorem u5212 : Upper (D 6) (R 6) [10,160,320,5,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5213 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 324 13 82 36 80 161 289), lower := (rows 11 162 324 13 82 36 80 128 256), losses := [] }

theorem u5213 : Upper (D 6) (R 6) [10,160,320,5,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5213 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5214 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 324 13 82 36 96 145 273), lower := (rows 11 162 324 13 82 36 96 128 256), losses := [] }

theorem u5214 : Upper (D 6) (R 6) [10,160,320,5,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5215 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 324 13 82 48 65 164 292), lower := (rows 11 162 324 13 82 48 65 128 256), losses := [] }

theorem u5215 : Upper (D 6) (R 6) [10,160,320,5,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5215 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5216 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 324 13 82 48 68 161 289), lower := (rows 11 162 324 13 82 48 68 128 256), losses := [] }

theorem u5216 : Upper (D 6) (R 6) [10,160,320,5,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5216 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5217 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 162 324 13 82 48 96 133 261), lower := (rows 11 162 324 13 82 48 96 128 256), losses := [] }

theorem u5217 : Upper (D 6) (R 6) [10,160,320,5,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5217 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5218 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 13 112 36 65 146 274), lower := (rows 11 162 324 13 112 36 65 128 256), losses := [] }

theorem u5218 : Upper (D 6) (R 6) [10,160,320,5,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5219 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 2, region := 48, targets := 2 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 162 324 13 112 36 66 145 273), lower := (rows 11 162 324 13 112 36 66 128 256), losses := [] }

theorem u5219 : Upper (D 6) (R 6) [10,160,320,5,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P06
