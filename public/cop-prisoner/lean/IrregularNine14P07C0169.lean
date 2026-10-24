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

def b10140 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 144, targets := 32 },{ cop := 3, region := 144, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(2,0),(4,5),(4,6)], upper := (rows 37 322 76 11 145 160 96 146 274), lower := (rows 37 322 76 11 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 18 12 8 16 176 241 144 272), good := (rows 100 322 76 78 498 224 96 224 256) }] }

theorem u10140 : Upper (D 7) (R 7) [36,320,72,3,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10141 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 322 76 11 146 160 65 176 304), lower := (rows 37 322 76 11 146 160 65 128 256), losses := [] }

theorem u10141 : Upper (D 7) (R 7) [36,320,72,3,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10142 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 3, region := 176, targets := 64 }], pairs := [(0,1),(0,6),(4,6)], upper := (rows 37 322 76 11 146 160 80 161 289), lower := (rows 37 322 76 11 146 160 80 128 256), losses := [] }

theorem u10142 : Upper (D 7) (R 7) [36,320,72,3,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10142 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10143 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 144, targets := 32 },{ cop := 3, region := 144, targets := 64 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 37 322 76 11 146 160 96 145 273), lower := (rows 37 322 76 11 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 241 128 256), good := (rows 100 322 76 78 242 224 96 224 256) },{ target := 1, region := (rows 1 0 12 8 16 176 241 128 256), good := (rows 101 320 76 77 240 224 96 224 256) }] }

theorem u10143 : Upper (D 7) (R 7) [36,320,72,3,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10144 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 76 25 50 160 65 130 386), lower := (rows 37 322 76 25 50 160 65 128 256), losses := [] }

theorem u10144 : Upper (D 7) (R 7) [36,320,72,17,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10145 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 8, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 76 25 50 160 66 129 385), lower := (rows 37 322 76 25 50 160 66 128 256), losses := [] }

theorem u10145 : Upper (D 7) (R 7) [36,320,72,17,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10146 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(0,1),(1,5),(2,5),(4,0)], upper := (rows 37 322 76 25 50 160 192 131 259), lower := (rows 37 322 76 25 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 108 24 114 224 224 224 256) },{ target := 1, region := (rows 21 0 20 24 16 224 224 128 256), good := (rows 101 352 109 29 125 224 224 224 256) }] }

theorem u10146 : Upper (D 7) (R 7) [36,320,72,17,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10147 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 322 76 25 146 34 65 160 416), lower := (rows 37 322 76 25 146 34 65 128 256), losses := [] }

theorem u10147 : Upper (D 7) (R 7) [36,320,72,17,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10148 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 8, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 76 25 146 34 96 129 385), lower := (rows 37 322 76 25 146 34 96 128 256), losses := [] }

theorem u10148 : Upper (D 7) (R 7) [36,320,72,17,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10149 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 37 322 76 25 146 34 192 161 289), lower := (rows 37 322 76 25 146 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 208 128 256), good := (rows 36 354 76 124 242 34 192 192 256) },{ target := 1, region := (rows 1 0 12 8 16 32 217 129 257), good := (rows 485 320 76 477 208 32 192 192 256) }] }

theorem u10149 : Upper (D 7) (R 7) [36,320,72,17,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10150 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 322 76 25 146 160 65 162 290), lower := (rows 37 322 76 25 146 160 65 128 256), losses := [] }

theorem u10150 : Upper (D 7) (R 7) [36,320,72,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10151 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 322 76 25 146 160 66 161 289), lower := (rows 37 322 76 25 146 160 66 128 256), losses := [] }

theorem u10151 : Upper (D 7) (R 7) [36,320,72,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10152 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 37 322 76 25 146 160 96 131 259), lower := (rows 37 322 76 25 146 160 96 128 256), losses := [] }

theorem u10152 : Upper (D 7) (R 7) [36,320,72,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10153 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 76 25 176 34 65 130 386), lower := (rows 37 322 76 25 176 34 65 128 256), losses := [] }

theorem u10153 : Upper (D 7) (R 7) [36,320,72,17,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10154 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 76 25 176 34 66 129 385), lower := (rows 37 322 76 25 176 34 66 128 256), losses := [] }

theorem u10154 : Upper (D 7) (R 7) [36,320,72,17,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10155 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 37 322 76 25 176 34 192 131 259), lower := (rows 37 322 76 25 176 34 192 128 256), losses := [] }

theorem u10155 : Upper (D 7) (R 7) [36,320,72,17,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10156 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 322 76 26 145 160 65 162 290), lower := (rows 37 322 76 26 145 160 65 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 93 128 256), good := (rows 101 320 77 125 241 160 65 160 256) }] }

theorem u10156 : Upper (D 7) (R 7) [36,320,72,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10157 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 76 26 145 160 66 161 289), lower := (rows 37 322 76 26 145 160 66 128 256), losses := [] }

theorem u10157 : Upper (D 7) (R 7) [36,320,72,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10158 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,7),(2,0),(2,1)], upper := (rows 37 322 76 26 145 160 96 131 259), lower := (rows 37 322 76 26 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 249 128 256), good := (rows 100 322 76 126 240 224 96 224 256) },{ target := 1, region := (rows 9 0 12 8 16 176 249 128 256), good := (rows 101 320 77 125 241 224 96 224 256) }] }

theorem u10158 : Upper (D 7) (R 7) [36,320,72,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10159 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 322 76 42 19 160 65 144 400), lower := (rows 37 322 76 42 19 160 65 128 256), losses := [] }

theorem u10159 : Upper (D 7) (R 7) [36,320,72,34,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10160 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 322 76 42 19 160 80 129 385), lower := (rows 37 322 76 42 19 160 80 128 256), losses := [] }

theorem u10160 : Upper (D 7) (R 7) [36,320,72,34,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10160 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10161 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 168, targets := 64 }], pairs := [(1,5),(2,0),(3,6),(4,5)], upper := (rows 37 322 76 42 19 160 192 145 273), lower := (rows 37 322 76 42 19 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 16 224 224 128 256), good := (rows 100 366 108 110 30 224 224 224 256) }] }

theorem u10161 : Upper (D 7) (R 7) [36,320,72,34,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10162 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 76 42 145 48 65 130 386), lower := (rows 37 322 76 42 145 48 65 128 256), losses := [] }

theorem u10162 : Upper (D 7) (R 7) [36,320,72,34,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10162 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10163 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 76 42 145 48 66 129 385), lower := (rows 37 322 76 42 145 48 66 128 256), losses := [] }

theorem u10163 : Upper (D 7) (R 7) [36,320,72,34,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10163 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10164 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 76 42 145 48 192 131 259), lower := (rows 37 322 76 42 145 48 192 128 256), losses := [{ target := 5, region := (rows 1 51 12 8 17 0 241 145 273), good := (rows 471 322 76 78 467 466 192 192 256) }] }

theorem u10164 : Upper (D 7) (R 7) [36,320,72,34,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10164 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10165 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 76 42 145 160 65 146 274), lower := (rows 37 322 76 42 145 160 65 128 256), losses := [] }

theorem u10165 : Upper (D 7) (R 7) [36,320,72,34,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10166 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 76 42 145 160 66 145 273), lower := (rows 37 322 76 42 145 160 66 128 256), losses := [] }

theorem u10166 : Upper (D 7) (R 7) [36,320,72,34,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10167 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 37 322 76 42 145 160 80 131 259), lower := (rows 37 322 76 42 145 160 80 128 256), losses := [] }

theorem u10167 : Upper (D 7) (R 7) [36,320,72,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10167 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10168 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 76 56 145 34 65 130 386), lower := (rows 37 322 76 56 145 34 65 128 256), losses := [] }

theorem u10168 : Upper (D 7) (R 7) [36,320,72,48,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10169 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 76 56 145 34 66 129 385), lower := (rows 37 322 76 56 145 34 66 128 256), losses := [] }

theorem u10169 : Upper (D 7) (R 7) [36,320,72,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10170 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 37 322 76 56 145 34 192 131 259), lower := (rows 37 322 76 56 145 34 192 128 256), losses := [] }

theorem u10170 : Upper (D 7) (R 7) [36,320,72,48,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10171 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 322 76 137 19 34 80 160 416), lower := (rows 37 322 76 137 19 34 80 128 256), losses := [] }

theorem u10171 : Upper (D 7) (R 7) [36,320,72,129,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10171 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10172 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 34 },{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 322 76 137 19 34 96 144 400), lower := (rows 37 322 76 137 19 34 96 128 256), losses := [] }

theorem u10172 : Upper (D 7) (R 7) [36,320,72,129,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10173 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 322 76 137 19 34 192 176 304), lower := (rows 37 322 76 137 19 34 192 128 256), losses := [] }

theorem u10173 : Upper (D 7) (R 7) [36,320,72,129,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10174 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 322 76 137 146 34 65 176 304), lower := (rows 37 322 76 137 146 34 65 128 256), losses := [] }

theorem u10174 : Upper (D 7) (R 7) [36,320,72,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10175 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 37 322 76 137 146 34 80 161 289), lower := (rows 37 322 76 137 146 34 80 128 256), losses := [] }

theorem u10175 : Upper (D 7) (R 7) [36,320,72,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10175 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10176 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 322 76 137 146 34 96 145 273), lower := (rows 37 322 76 137 146 34 96 128 256), losses := [{ target := 0, region := (rows 0 258 12 8 16 306 371 128 256), good := (rows 100 354 76 204 242 98 96 128 354) },{ target := 1, region := (rows 1 0 12 8 16 32 97 128 256), good := (rows 101 320 76 205 144 96 96 128 256) }] }

theorem u10176 : Upper (D 7) (R 7) [36,320,72,129,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10177 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 322 76 137 146 48 65 162 290), lower := (rows 37 322 76 137 146 48 65 128 256), losses := [] }

theorem u10177 : Upper (D 7) (R 7) [36,320,72,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10177 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10178 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 76 137 146 48 66 161 289), lower := (rows 37 322 76 137 146 48 66 128 256), losses := [] }

theorem u10178 : Upper (D 7) (R 7) [36,320,72,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10178 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10179 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 76 137 146 48 96 131 259), lower := (rows 37 322 76 137 146 48 96 128 256), losses := [] }

theorem u10179 : Upper (D 7) (R 7) [36,320,72,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10179 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10180 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 322 76 137 176 34 65 146 274), lower := (rows 37 322 76 137 176 34 65 128 256), losses := [] }

theorem u10180 : Upper (D 7) (R 7) [36,320,72,129,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10181 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 76 137 176 34 66 145 273), lower := (rows 37 322 76 137 176 34 66 128 256), losses := [] }

theorem u10181 : Upper (D 7) (R 7) [36,320,72,129,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10182 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 76 137 176 34 80 131 259), lower := (rows 37 322 76 137 176 34 80 128 256), losses := [] }

theorem u10182 : Upper (D 7) (R 7) [36,320,72,129,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10182 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10183 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 322 76 138 19 48 65 160 416), lower := (rows 37 322 76 138 19 48 65 128 256), losses := [] }

theorem u10183 : Upper (D 7) (R 7) [36,320,72,130,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10183 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10184 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 322 76 138 19 48 96 129 385), lower := (rows 37 322 76 138 19 48 96 128 256), losses := [] }

theorem u10184 : Upper (D 7) (R 7) [36,320,72,130,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10184 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10185 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 322 76 138 19 48 192 161 289), lower := (rows 37 322 76 138 19 48 192 128 256), losses := [] }

theorem u10185 : Upper (D 7) (R 7) [36,320,72,130,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10185 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10186 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 117, targets := 128 },{ cop := 4, region := 136, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 322 76 138 50 33 65 144 400), lower := (rows 37 322 76 138 50 33 65 128 256), losses := [] }

theorem u10186 : Upper (D 7) (R 7) [36,320,72,130,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10187 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 322 76 138 50 33 80 129 385), lower := (rows 37 322 76 138 50 33 80 128 256), losses := [] }

theorem u10187 : Upper (D 7) (R 7) [36,320,72,130,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10187 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10188 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 37 322 76 138 50 33 192 145 273), lower := (rows 37 322 76 138 50 33 192 128 256), losses := [] }

theorem u10188 : Upper (D 7) (R 7) [36,320,72,130,34,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10189 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 76 138 145 48 65 162 290), lower := (rows 37 322 76 138 145 48 65 128 256), losses := [] }

theorem u10189 : Upper (D 7) (R 7) [36,320,72,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10189 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10190 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 76 138 145 48 66 161 289), lower := (rows 37 322 76 138 145 48 66 128 256), losses := [] }

theorem u10190 : Upper (D 7) (R 7) [36,320,72,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10190 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10191 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 76 138 145 48 96 131 259), lower := (rows 37 322 76 138 145 48 96 128 256), losses := [] }

theorem u10191 : Upper (D 7) (R 7) [36,320,72,130,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10191 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10192 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 117, targets := 2 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 322 76 138 176 33 65 146 274), lower := (rows 37 322 76 138 176 33 65 128 256), losses := [] }

theorem u10192 : Upper (D 7) (R 7) [36,320,72,130,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10193 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 76 138 176 33 66 145 273), lower := (rows 37 322 76 138 176 33 66 128 256), losses := [] }

theorem u10193 : Upper (D 7) (R 7) [36,320,72,130,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10194 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 76 138 176 33 80 131 259), lower := (rows 37 322 76 138 176 33 80 128 256), losses := [] }

theorem u10194 : Upper (D 7) (R 7) [36,320,72,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10194 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10195 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 168, targets := 65 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,6)], upper := (rows 37 322 76 152 19 34 65 160 416), lower := (rows 37 322 76 152 19 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 16 32 81 161 289), good := (rows 485 320 76 220 477 416 449 128 256) }] }

theorem u10195 : Upper (D 7) (R 7) [36,320,72,144,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10196 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 136, targets := 34 },{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 322 76 152 19 34 96 129 385), lower := (rows 37 322 76 152 19 34 96 128 256), losses := [] }

theorem u10196 : Upper (D 7) (R 7) [36,320,72,144,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10197 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 322 76 152 19 34 192 161 289), lower := (rows 37 322 76 152 19 34 192 128 256), losses := [] }

theorem u10197 : Upper (D 7) (R 7) [36,320,72,144,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10198 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 76 168 19 34 65 144 400), lower := (rows 37 322 76 168 19 34 65 128 256), losses := [] }

theorem u10198 : Upper (D 7) (R 7) [36,320,72,160,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10199 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6)], upper := (rows 37 322 76 168 19 34 80 129 385), lower := (rows 37 322 76 168 19 34 80 128 256), losses := [] }

theorem u10199 : Upper (D 7) (R 7) [36,320,72,160,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10199 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10199
end Delivery.IrregularNine14.P07
