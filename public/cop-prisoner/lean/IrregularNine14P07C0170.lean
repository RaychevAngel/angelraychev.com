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

def b10200 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,7)], upper := (rows 37 322 76 168 19 34 192 145 273), lower := (rows 37 322 76 168 19 34 192 128 256), losses := [] }

theorem u10200 : Upper (D 7) (R 7) [36,320,72,160,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10201 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 322 76 168 145 34 65 146 274), lower := (rows 37 322 76 168 145 34 65 128 256), losses := [] }

theorem u10201 : Upper (D 7) (R 7) [36,320,72,160,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10202 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 76 168 145 34 66 145 273), lower := (rows 37 322 76 168 145 34 66 128 256), losses := [] }

theorem u10202 : Upper (D 7) (R 7) [36,320,72,160,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10203 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 76 168 145 34 80 131 259), lower := (rows 37 322 76 168 145 34 80 128 256), losses := [] }

theorem u10203 : Upper (D 7) (R 7) [36,320,72,160,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10203 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10204 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 11 88 48 66 160 416), lower := (rows 37 322 133 11 88 48 66 128 256), losses := [] }

theorem u10204 : Upper (D 7) (R 7) [36,320,129,3,72,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10204 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10205 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 112, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 37 322 133 11 88 48 96 130 386), lower := (rows 37 322 133 11 88 48 96 128 256), losses := [] }

theorem u10205 : Upper (D 7) (R 7) [36,320,129,3,72,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10205 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10206 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 322 133 11 88 48 192 162 290), lower := (rows 37 322 133 11 88 48 192 128 256), losses := [] }

theorem u10206 : Upper (D 7) (R 7) [36,320,129,3,72,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10206 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10207 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 11 112 34 72 144 400), lower := (rows 37 322 133 11 112 34 72 128 256), losses := [] }

theorem u10207 : Upper (D 7) (R 7) [36,320,129,3,96,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10207 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10208 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 322 133 11 112 34 80 136 392), lower := (rows 37 322 133 11 112 34 80 128 256), losses := [] }

theorem u10208 : Upper (D 7) (R 7) [36,320,129,3,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10208 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10209 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(2,1),(4,0),(4,7)], upper := (rows 37 322 133 11 112 34 192 152 280), lower := (rows 37 322 133 11 112 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 32 204 136 264), good := (rows 117 320 213 477 112 32 192 192 256) }] }

theorem u10209 : Upper (D 7) (R 7) [36,320,129,3,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10210 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 354, targets := 128 },{ cop := 8, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 322 133 11 152 96 66 176 304), lower := (rows 37 322 133 11 152 96 66 128 256), losses := [] }

theorem u10210 : Upper (D 7) (R 7) [36,320,129,3,136,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10211 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 322 133 11 152 96 80 162 290), lower := (rows 37 322 133 11 152 96 80 128 256), losses := [] }

theorem u10211 : Upper (D 7) (R 7) [36,320,129,3,136,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10211 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10212 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 37 322 133 11 152 96 96 146 274), lower := (rows 37 322 133 11 152 96 96 128 256), losses := [] }

theorem u10212 : Upper (D 7) (R 7) [36,320,129,3,136,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10213 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 322 133 11 208 34 72 176 304), lower := (rows 37 322 133 11 208 34 72 128 256), losses := [] }

theorem u10213 : Upper (D 7) (R 7) [36,320,129,3,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10213 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10214 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 133 11 208 34 80 168 296), lower := (rows 37 322 133 11 208 34 80 128 256), losses := [] }

theorem u10214 : Upper (D 7) (R 7) [36,320,129,3,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10214 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10215 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 8, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(4,0)], upper := (rows 37 322 133 11 208 34 96 152 280), lower := (rows 37 322 133 11 208 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 28 32 97 136 264), good := (rows 117 320 213 477 208 96 96 128 256) }] }

theorem u10215 : Upper (D 7) (R 7) [36,320,129,3,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10216 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 133 11 208 40 66 176 304), lower := (rows 37 322 133 11 208 40 66 128 256), losses := [] }

theorem u10216 : Upper (D 7) (R 7) [36,320,129,3,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10216 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10217 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 322 133 11 208 40 80 162 290), lower := (rows 37 322 133 11 208 40 80 128 256), losses := [] }

theorem u10217 : Upper (D 7) (R 7) [36,320,129,3,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10217 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10218 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 322 133 11 208 40 96 146 274), lower := (rows 37 322 133 11 208 40 96 128 256), losses := [] }

theorem u10218 : Upper (D 7) (R 7) [36,320,129,3,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10218 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10219 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 25 26 96 66 160 416), lower := (rows 37 322 133 25 26 96 66 128 256), losses := [] }

theorem u10219 : Upper (D 7) (R 7) [36,320,129,17,10,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10220 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 322 133 25 26 96 96 130 386), lower := (rows 37 322 133 25 26 96 96 128 256), losses := [] }

theorem u10220 : Upper (D 7) (R 7) [36,320,129,17,10,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10221 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 6, region := 37, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 322 133 25 26 96 192 162 290), lower := (rows 37 322 133 25 26 96 192 128 256), losses := [] }

theorem u10221 : Upper (D 7) (R 7) [36,320,129,17,10,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10222 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 },{ cop := 8, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 322 133 25 208 34 66 168 296), lower := (rows 37 322 133 25 208 34 66 128 256), losses := [] }

theorem u10222 : Upper (D 7) (R 7) [36,320,129,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10223 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 37 322 133 25 208 34 72 162 290), lower := (rows 37 322 133 25 208 34 72 128 256), losses := [] }

theorem u10223 : Upper (D 7) (R 7) [36,320,129,17,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10223 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10224 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,1),(4,0)], upper := (rows 37 322 133 25 208 34 96 138 266), lower := (rows 37 322 133 25 208 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 20 32 97 128 256), good := (rows 125 320 221 89 208 96 96 128 256) }] }

theorem u10224 : Upper (D 7) (R 7) [36,320,129,17,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10225 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 322 133 26 208 34 65 168 296), lower := (rows 37 322 133 26 208 34 65 128 256), losses := [] }

theorem u10225 : Upper (D 7) (R 7) [36,320,129,18,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10226 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 26 208 34 72 161 289), lower := (rows 37 322 133 26 208 34 72 128 256), losses := [] }

theorem u10226 : Upper (D 7) (R 7) [36,320,129,18,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10226 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10227 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 8, region := 98, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 322 133 26 208 34 96 137 265), lower := (rows 37 322 133 26 208 34 96 128 256), losses := [] }

theorem u10227 : Upper (D 7) (R 7) [36,320,129,18,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10228 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 56 81 34 66 136 392), lower := (rows 37 322 133 56 81 34 66 128 256), losses := [] }

theorem u10228 : Upper (D 7) (R 7) [36,320,129,48,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10229 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 322 133 56 81 34 72 130 386), lower := (rows 37 322 133 56 81 34 72 128 256), losses := [] }

theorem u10229 : Upper (D 7) (R 7) [36,320,129,48,65,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10229 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10230 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 4, region := 298, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 37 322 133 56 81 34 192 138 266), lower := (rows 37 322 133 56 81 34 192 128 256), losses := [] }

theorem u10230 : Upper (D 7) (R 7) [36,320,129,48,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10231 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 322 133 56 208 34 65 138 266), lower := (rows 37 322 133 56 208 34 65 128 256), losses := [] }

theorem u10231 : Upper (D 7) (R 7) [36,320,129,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10232 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 56 208 34 66 137 265), lower := (rows 37 322 133 56 208 34 66 128 256), losses := [] }

theorem u10232 : Upper (D 7) (R 7) [36,320,129,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10233 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,0)], upper := (rows 37 322 133 56 208 34 72 131 259), lower := (rows 37 322 133 56 208 34 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 34 77 128 256), good := (rows 124 354 220 120 208 34 72 128 256) }] }

theorem u10233 : Upper (D 7) (R 7) [36,320,129,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10233 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10234 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 133 73 146 40 66 176 304), lower := (rows 37 322 133 73 146 40 66 128 256), losses := [] }

theorem u10234 : Upper (D 7) (R 7) [36,320,129,65,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10234 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10235 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 322 133 73 146 40 80 162 290), lower := (rows 37 322 133 73 146 40 80 128 256), losses := [] }

theorem u10235 : Upper (D 7) (R 7) [36,320,129,65,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10235 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10236 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 322 133 73 146 40 96 146 274), lower := (rows 37 322 133 73 146 40 96 128 256), losses := [] }

theorem u10236 : Upper (D 7) (R 7) [36,320,129,65,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10236 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10237 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 354, targets := 128 },{ cop := 8, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 322 133 73 152 34 66 176 304), lower := (rows 37 322 133 73 152 34 66 128 256), losses := [] }

theorem u10237 : Upper (D 7) (R 7) [36,320,129,65,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10238 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 37 322 133 73 152 34 80 162 290), lower := (rows 37 322 133 73 152 34 80 128 256), losses := [] }

theorem u10238 : Upper (D 7) (R 7) [36,320,129,65,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10238 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10239 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 133 73 152 34 96 146 274), lower := (rows 37 322 133 73 152 34 96 128 256), losses := [] }

theorem u10239 : Upper (D 7) (R 7) [36,320,129,65,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10240 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 322 133 88 146 34 65 168 296), lower := (rows 37 322 133 88 146 34 65 128 256), losses := [] }

theorem u10240 : Upper (D 7) (R 7) [36,320,129,80,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10241 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 322 133 88 146 34 72 161 289), lower := (rows 37 322 133 88 146 34 72 128 256), losses := [] }

theorem u10241 : Upper (D 7) (R 7) [36,320,129,80,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10241 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10242 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 129 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,7)], upper := (rows 37 322 133 88 146 34 96 137 265), lower := (rows 37 322 133 88 146 34 96 128 256), losses := [] }

theorem u10242 : Upper (D 7) (R 7) [36,320,129,80,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10243 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 133 88 146 40 65 162 290), lower := (rows 37 322 133 88 146 40 65 128 256), losses := [] }

theorem u10243 : Upper (D 7) (R 7) [36,320,129,80,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10243 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10244 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 88 146 40 66 161 289), lower := (rows 37 322 133 88 146 40 66 128 256), losses := [] }

theorem u10244 : Upper (D 7) (R 7) [36,320,129,80,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10244 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10245 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 133 88 146 40 96 131 259), lower := (rows 37 322 133 88 146 40 96 128 256), losses := [] }

theorem u10245 : Upper (D 7) (R 7) [36,320,129,80,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10245 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10246 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 322 133 104 152 34 65 146 274), lower := (rows 37 322 133 104 152 34 65 128 256), losses := [] }

theorem u10246 : Upper (D 7) (R 7) [36,320,129,96,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10247 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 149, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 104 152 34 66 145 273), lower := (rows 37 322 133 104 152 34 66 128 256), losses := [] }

theorem u10247 : Upper (D 7) (R 7) [36,320,129,96,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10248 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 40, targets := 129 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(3,0),(3,7)], upper := (rows 37 322 133 104 152 34 80 131 259), lower := (rows 37 322 133 104 152 34 80 128 256), losses := [] }

theorem u10248 : Upper (D 7) (R 7) [36,320,129,96,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10248 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10249 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 37 322 134 11 81 48 72 160 416), lower := (rows 37 322 134 11 81 48 72 128 256), losses := [] }

theorem u10249 : Upper (D 7) (R 7) [36,320,130,3,65,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10249 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10250 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 322 134 11 81 48 96 136 392), lower := (rows 37 322 134 11 81 48 96 128 256), losses := [] }

theorem u10250 : Upper (D 7) (R 7) [36,320,130,3,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10250 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10251 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 298, targets := 128 }], pairs := [(0,1),(1,7),(4,1)], upper := (rows 37 322 134 11 81 48 192 168 296), lower := (rows 37 322 134 11 81 48 192 128 256), losses := [] }

theorem u10251 : Upper (D 7) (R 7) [36,320,130,3,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10251 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10252 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 121, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 322 134 25 112 40 65 130 386), lower := (rows 37 322 134 25 112 40 65 128 256), losses := [] }

theorem u10252 : Upper (D 7) (R 7) [36,320,130,17,96,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10252 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10253 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 322 134 25 112 40 66 129 385), lower := (rows 37 322 134 25 112 40 66 128 256), losses := [] }

theorem u10253 : Upper (D 7) (R 7) [36,320,130,17,96,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10253 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10254 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 25 112 40 192 131 259), lower := (rows 37 322 134 25 112 40 192 128 256), losses := [] }

theorem u10254 : Upper (D 7) (R 7) [36,320,130,17,96,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10254 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10255 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 25 208 40 65 162 290), lower := (rows 37 322 134 25 208 40 65 128 256), losses := [] }

theorem u10255 : Upper (D 7) (R 7) [36,320,130,17,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10255 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10256 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 134 25 208 40 66 161 289), lower := (rows 37 322 134 25 208 40 66 128 256), losses := [] }

theorem u10256 : Upper (D 7) (R 7) [36,320,130,17,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10256 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10257 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 25 208 40 96 131 259), lower := (rows 37 322 134 25 208 40 96 128 256), losses := [] }

theorem u10257 : Upper (D 7) (R 7) [36,320,130,17,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10257 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10258 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 322 134 42 81 48 65 136 392), lower := (rows 37 322 134 42 81 48 65 128 256), losses := [] }

theorem u10258 : Upper (D 7) (R 7) [36,320,130,34,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10259 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 37 322 134 42 81 48 72 129 385), lower := (rows 37 322 134 42 81 48 72 128 256), losses := [] }

theorem u10259 : Upper (D 7) (R 7) [36,320,130,34,65,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10259 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10259
end Delivery.IrregularNine14.P07
