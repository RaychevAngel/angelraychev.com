import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9180 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 137 208 48 66 168 296), lower := (rows 37 259 70 137 208 48 66 128 256), losses := [] }

theorem u9180 : Upper (D 7) (R 7) [36,257,66,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9180 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9181 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 259 70 137 208 48 72 162 290), lower := (rows 37 259 70 137 208 48 72 128 256), losses := [] }

theorem u9181 : Upper (D 7) (R 7) [36,257,66,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9181 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9182 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 37 259 70 137 208 48 96 138 266), lower := (rows 37 259 70 137 208 48 96 128 256), losses := [] }

theorem u9182 : Upper (D 7) (R 7) [36,257,66,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9182 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9183 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 1 }], pairs := [(2,5),(2,7),(3,0)], upper := (rows 37 259 70 138 208 40 65 176 304), lower := (rows 37 259 70 138 208 40 65 128 256), losses := [] }

theorem u9183 : Upper (D 7) (R 7) [36,257,66,130,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9183 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9184 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 259 70 138 208 40 80 161 289), lower := (rows 37 259 70 138 208 40 80 128 256), losses := [] }

theorem u9184 : Upper (D 7) (R 7) [36,257,66,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9184 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9185 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 116, targets := 1 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,0),(4,0)], upper := (rows 37 259 70 138 208 40 96 145 273), lower := (rows 37 259 70 138 208 40 96 128 256), losses := [] }

theorem u9185 : Upper (D 7) (R 7) [36,257,66,130,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9185 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9186 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,6),(2,5),(3,6)], upper := (rows 37 259 70 138 208 48 65 168 296), lower := (rows 37 259 70 138 208 48 65 128 256), losses := [] }

theorem u9186 : Upper (D 7) (R 7) [36,257,66,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9186 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9187 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 259 70 138 208 48 72 161 289), lower := (rows 37 259 70 138 208 48 72 128 256), losses := [] }

theorem u9187 : Upper (D 7) (R 7) [36,257,66,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9187 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9188 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 37 259 70 138 208 48 96 137 265), lower := (rows 37 259 70 138 208 48 96 128 256), losses := [] }

theorem u9188 : Upper (D 7) (R 7) [36,257,66,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9188 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9189 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 168 208 33 66 152 280), lower := (rows 37 259 70 168 208 33 66 128 256), losses := [] }

theorem u9189 : Upper (D 7) (R 7) [36,257,66,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9190 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 259 70 168 208 33 72 146 274), lower := (rows 37 259 70 168 208 33 72 128 256), losses := [] }

theorem u9190 : Upper (D 7) (R 7) [36,257,66,160,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9190 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9191 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 70 168 208 33 80 138 266), lower := (rows 37 259 70 168 208 33 80 128 256), losses := [] }

theorem u9191 : Upper (D 7) (R 7) [36,257,66,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9191 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9192 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 259 76 25 146 34 96 192 448), lower := (rows 37 259 76 25 146 34 96 128 256), losses := [] }

theorem u9192 : Upper (D 7) (R 7) [36,257,72,17,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9193 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 37 259 76 25 146 34 192 224 352), lower := (rows 37 259 76 25 146 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 50 50 255 187 315), good := (rows 500 498 460 508 498 498 192 192 256) }] }

theorem u9193 : Upper (D 7) (R 7) [36,257,72,17,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9194 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,5),(2,1),(2,5),(4,0)], upper := (rows 37 259 76 25 176 34 66 192 448), lower := (rows 37 259 76 25 176 34 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 11 17 32 64 196 324), good := (rows 445 281 460 25 176 40 460 128 256) }] }

theorem u9194 : Upper (D 7) (R 7) [36,257,72,17,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9195 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 37 259 76 25 176 34 192 194 322), lower := (rows 37 259 76 25 176 34 192 128 256), losses := [] }

theorem u9195 : Upper (D 7) (R 7) [36,257,72,17,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9196 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(4,0)], upper := (rows 37 259 76 25 208 34 66 160 416), lower := (rows 37 259 76 25 208 34 66 128 256), losses := [{ target := 7, region := (rows 21 2 20 24 16 98 98 0 256), good := (rows 101 355 109 29 125 98 98 0 256) }] }

theorem u9196 : Upper (D 7) (R 7) [36,257,72,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9197 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 386, targets := 32 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,6),(1,5),(1,6),(4,0)], upper := (rows 37 259 76 25 208 34 96 130 386), lower := (rows 37 259 76 25 208 34 96 128 256), losses := [] }

theorem u9197 : Upper (D 7) (R 7) [36,257,72,17,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9198 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 76 25 208 34 192 162 290), lower := (rows 37 259 76 25 208 34 192 128 256), losses := [] }

theorem u9198 : Upper (D 7) (R 7) [36,257,72,17,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9199 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7),(4,0)], upper := (rows 37 259 76 26 208 160 65 162 290), lower := (rows 37 259 76 26 208 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 190 64 138 266), good := (rows 52 418 508 442 240 160 64 160 256) }] }

theorem u9199 : Upper (D 7) (R 7) [36,257,72,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9200 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 259 76 26 208 160 66 161 289), lower := (rows 37 259 76 26 208 160 66 128 256), losses := [] }

theorem u9200 : Upper (D 7) (R 7) [36,257,72,18,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9201 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 37 259 76 26 208 160 96 131 259), lower := (rows 37 259 76 26 208 160 96 128 256), losses := [] }

theorem u9201 : Upper (D 7) (R 7) [36,257,72,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9202 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 259 76 42 82 160 65 144 400), lower := (rows 37 259 76 42 82 160 65 128 256), losses := [] }

theorem u9202 : Upper (D 7) (R 7) [36,257,72,34,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9203 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 259 76 42 82 160 80 129 385), lower := (rows 37 259 76 42 82 160 80 128 256), losses := [] }

theorem u9203 : Upper (D 7) (R 7) [36,257,72,34,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9203 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9204 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 37 259 76 42 82 160 192 145 273), lower := (rows 37 259 76 42 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 24 224 224 128 256), good := (rows 100 258 124 126 126 224 224 224 256) }] }

theorem u9204 : Upper (D 7) (R 7) [36,257,72,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9205 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 76 42 208 160 65 146 274), lower := (rows 37 259 76 42 208 160 65 128 256), losses := [] }

theorem u9205 : Upper (D 7) (R 7) [36,257,72,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9206 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,5),(4,1),(4,5)], upper := (rows 37 259 76 42 208 160 66 145 273), lower := (rows 37 259 76 42 208 160 66 128 256), losses := [] }

theorem u9206 : Upper (D 7) (R 7) [36,257,72,34,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9207 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 76 42 208 160 80 131 259), lower := (rows 37 259 76 42 208 160 80 128 256), losses := [] }

theorem u9207 : Upper (D 7) (R 7) [36,257,72,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9207 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9208 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 76 137 82 34 80 160 416), lower := (rows 37 259 76 137 82 34 80 128 256), losses := [] }

theorem u9208 : Upper (D 7) (R 7) [36,257,72,129,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9208 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9209 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 112, targets := 1 },{ cop := 1, region := 112, targets := 128 }], pairs := [(2,0),(2,1),(4,0),(4,7)], upper := (rows 37 259 76 137 82 34 96 144 400), lower := (rows 37 259 76 137 82 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 50 50 115 243 371), good := (rows 500 498 460 460 498 498 496 128 256) },{ target := 1, region := (rows 1 0 12 8 16 32 97 144 272), good := (rows 101 321 76 205 464 96 96 128 256) }] }

theorem u9209 : Upper (D 7) (R 7) [36,257,72,129,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9210 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 259 76 137 82 34 192 176 304), lower := (rows 37 259 76 137 82 34 192 128 256), losses := [] }

theorem u9210 : Upper (D 7) (R 7) [36,257,72,129,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9211 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 141, targets := 2 },{ cop := 1, region := 112, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 259 76 137 112 34 66 144 400), lower := (rows 37 259 76 137 112 34 66 128 256), losses := [] }

theorem u9211 : Upper (D 7) (R 7) [36,257,72,129,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9212 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 76 137 112 34 80 130 386), lower := (rows 37 259 76 137 112 34 80 128 256), losses := [] }

theorem u9212 : Upper (D 7) (R 7) [36,257,72,129,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9212 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9213 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 259 76 137 112 34 192 146 274), lower := (rows 37 259 76 137 112 34 192 128 256), losses := [] }

theorem u9213 : Upper (D 7) (R 7) [36,257,72,129,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9214 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 37 259 76 137 146 34 80 224 352), lower := (rows 37 259 76 137 146 34 80 128 256), losses := [] }

theorem u9214 : Upper (D 7) (R 7) [36,257,72,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9214 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9215 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(1,5),(2,0),(2,1),(4,0)], upper := (rows 37 259 76 137 146 34 96 208 336), lower := (rows 37 259 76 137 146 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 50 50 115 243 371), good := (rows 500 498 460 460 498 498 496 128 256) },{ target := 1, region := (rows 1 0 12 8 16 32 97 128 256), good := (rows 101 321 76 205 144 96 96 128 256) },{ target := 5, region := (rows 1 3 4 9 25 0 64 132 260), good := (rows 415 283 476 155 146 2 64 128 256) }] }

theorem u9215 : Upper (D 7) (R 7) [36,257,72,129,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9216 : Route 9 := (fun mask => (mask,id))

def c9216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9216 : Upper (D 7) (R 7) [36,257,72,129,160,2,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,160,2,2] 13 (by decide) (choices 1) [16,64] r9216 c9216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u733
  · exact u734

def b9217 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 259 76 137 176 34 80 194 322), lower := (rows 37 259 76 137 176 34 80 128 256), losses := [] }

theorem u9217 : Upper (D 7) (R 7) [36,257,72,129,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9217 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9218 : Route 9 := (fun mask => (mask,id))

def c9218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9218 : Upper (D 7) (R 7) [36,257,72,129,192,2,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,192,2,2] 13 (by decide) (choices 1) [16,32] r9218 c9218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u735
  · exact u736

def b9219 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 37 259 76 137 208 34 80 162 290), lower := (rows 37 259 76 137 208 34 80 128 256), losses := [] }

theorem u9219 : Upper (D 7) (R 7) [36,257,72,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9219 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9220 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 37 259 76 137 208 34 96 146 274), lower := (rows 37 259 76 137 208 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 123 34 99 162 290), good := (rows 500 498 92 220 208 498 496 128 256) },{ target := 1, region := (rows 1 0 12 8 24 32 97 128 256), good := (rows 101 321 92 221 208 96 96 128 256) }] }

theorem u9220 : Upper (D 7) (R 7) [36,257,72,129,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9221 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 259 76 138 82 48 65 160 416), lower := (rows 37 259 76 138 82 48 65 128 256), losses := [] }

theorem u9221 : Upper (D 7) (R 7) [36,257,72,130,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9221 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9222 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 37 259 76 138 82 48 96 129 385), lower := (rows 37 259 76 138 82 48 96 128 256), losses := [] }

theorem u9222 : Upper (D 7) (R 7) [36,257,72,130,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9222 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9223 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 259 76 138 82 48 192 161 289), lower := (rows 37 259 76 138 82 48 192 128 256), losses := [] }

theorem u9223 : Upper (D 7) (R 7) [36,257,72,130,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9223 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9224 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 76 138 145 48 66 224 352), lower := (rows 37 259 76 138 145 48 66 128 256), losses := [] }

theorem u9224 : Upper (D 7) (R 7) [36,257,72,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9224 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9225 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 259 76 138 145 48 96 194 322), lower := (rows 37 259 76 138 145 48 96 128 256), losses := [] }

theorem u9225 : Upper (D 7) (R 7) [36,257,72,130,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9225 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9226 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 76 138 208 33 66 176 304), lower := (rows 37 259 76 138 208 33 66 128 256), losses := [] }

theorem u9226 : Upper (D 7) (R 7) [36,257,72,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9227 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 259 76 138 208 33 80 162 290), lower := (rows 37 259 76 138 208 33 80 128 256), losses := [] }

theorem u9227 : Upper (D 7) (R 7) [36,257,72,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9227 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9228 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 117, targets := 2 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 259 76 138 208 33 96 146 274), lower := (rows 37 259 76 138 208 33 96 128 256), losses := [] }

theorem u9228 : Upper (D 7) (R 7) [36,257,72,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9229 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(2,7),(3,0),(4,1)], upper := (rows 37 259 76 138 208 34 65 176 304), lower := (rows 37 259 76 138 208 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 84 42 64 133 261), good := (rows 436 426 508 170 208 42 464 128 256) }] }

theorem u9229 : Upper (D 7) (R 7) [36,257,72,130,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9230 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 37 259 76 138 208 34 80 161 289), lower := (rows 37 259 76 138 208 34 80 128 256), losses := [] }

theorem u9230 : Upper (D 7) (R 7) [36,257,72,130,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9230 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9231 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 116, targets := 1 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,0),(2,7),(4,0)], upper := (rows 37 259 76 138 208 34 96 145 273), lower := (rows 37 259 76 138 208 34 96 128 256), losses := [] }

theorem u9231 : Upper (D 7) (R 7) [36,257,72,130,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9232 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 80, targets := 32 },{ cop := 1, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(4,5),(4,7)], upper := (rows 37 259 76 152 81 34 66 160 416), lower := (rows 37 259 76 152 81 34 66 128 256), losses := [] }

theorem u9232 : Upper (D 7) (R 7) [36,257,72,144,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9233 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 259 76 152 81 34 96 130 386), lower := (rows 37 259 76 152 81 34 96 128 256), losses := [] }

theorem u9233 : Upper (D 7) (R 7) [36,257,72,144,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9234 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 259 76 152 81 34 192 162 290), lower := (rows 37 259 76 152 81 34 192 128 256), losses := [] }

theorem u9234 : Upper (D 7) (R 7) [36,257,72,144,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9235 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 172, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,0)], upper := (rows 37 259 76 152 82 34 65 160 416), lower := (rows 37 259 76 152 82 34 65 128 256), losses := [] }

theorem u9235 : Upper (D 7) (R 7) [36,257,72,144,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9236 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 112, targets := 129 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,7)], upper := (rows 37 259 76 152 82 34 96 129 385), lower := (rows 37 259 76 152 82 34 96 128 256), losses := [] }

theorem u9236 : Upper (D 7) (R 7) [36,257,72,144,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9237 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 259 76 152 82 34 192 161 289), lower := (rows 37 259 76 152 82 34 192 128 256), losses := [] }

theorem u9237 : Upper (D 7) (R 7) [36,257,72,144,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9238 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,1),(4,7)], upper := (rows 37 259 76 152 112 34 65 130 386), lower := (rows 37 259 76 152 112 34 65 128 256), losses := [] }

theorem u9238 : Upper (D 7) (R 7) [36,257,72,144,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9239 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 2 },{ cop := 1, region := 112, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 259 76 152 112 34 66 129 385), lower := (rows 37 259 76 152 112 34 66 128 256), losses := [] }

theorem u9239 : Upper (D 7) (R 7) [36,257,72,144,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9239
end Delivery.IrregularNine14.P07
