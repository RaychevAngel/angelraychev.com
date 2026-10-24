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

def b240 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 129 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,0),(3,6),(3,7)], upper := (rows 13 50 196 296 81 160 66 129 258), lower := (rows 13 50 196 296 81 160 66 129 256), losses := [] }

theorem u240 : Upper (D 7) (R 7) [12,48,192,288,65,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 2 },{ cop := 2, region := 297, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 13 50 196 296 81 160 66 130 257), lower := (rows 13 50 196 296 81 160 66 130 256), losses := [] }

theorem u241 : Upper (D 7) (R 7) [12,48,192,288,65,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 193 },{ cop := 8, region := 237, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 13 50 196 296 82 160 65 129 258), lower := (rows 13 50 196 296 82 160 65 129 256), losses := [] }

theorem u242 : Upper (D 7) (R 7) [12,48,192,288,66,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 333, targets := 2 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 196 296 82 160 65 130 257), lower := (rows 13 50 196 296 82 160 65 130 256), losses := [] }

theorem u243 : Upper (D 7) (R 7) [12,48,192,288,66,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 157, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 56 146 288 192 129 320), lower := (rows 13 98 7 56 146 288 192 129 256), losses := [] }

theorem u244 : Upper (D 7) (R 7) [12,96,3,48,130,256,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b244 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 13 98 7 56 146 288 192 192 257), lower := (rows 13 98 7 56 146 288 192 192 256), losses := [] }

theorem u245 : Upper (D 7) (R 7) [12,96,3,48,130,256,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b245 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 7 152 304 34 192 129 320), lower := (rows 13 98 7 152 304 34 192 129 256), losses := [] }

theorem u246 : Upper (D 7) (R 7) [12,96,3,144,288,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 2, region := 304, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 13 98 7 152 304 34 192 192 257), lower := (rows 13 98 7 152 304 34 192 192 256), losses := [] }

theorem u247 : Upper (D 7) (R 7) [12,96,3,144,288,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 168 274 48 192 129 320), lower := (rows 13 98 7 168 274 48 192 129 256), losses := [] }

theorem u248 : Upper (D 7) (R 7) [12,96,3,160,258,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b248 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 7 168 274 48 192 192 257), lower := (rows 13 98 7 168 274 48 192 192 256), losses := [] }

theorem u249 : Upper (D 7) (R 7) [12,96,3,160,258,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b249 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 98 7 280 176 33 192 130 320), lower := (rows 13 98 7 280 176 33 192 130 256), losses := [] }

theorem u250 : Upper (D 7) (R 7) [12,96,3,272,160,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 7 280 176 33 192 192 258), lower := (rows 13 98 7 280 176 33 192 192 256), losses := [] }

theorem u251 : Upper (D 7) (R 7) [12,96,3,272,160,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 98 7 280 176 34 192 129 320), lower := (rows 13 98 7 280 176 34 192 129 256), losses := [] }

theorem u252 : Upper (D 7) (R 7) [12,96,3,272,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 1, region := 144, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 7 280 176 34 192 192 257), lower := (rows 13 98 7 280 176 34 192 192 256), losses := [] }

theorem u253 : Upper (D 7) (R 7) [12,96,3,272,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 138 304 34 192 129 320), lower := (rows 13 98 21 138 304 34 192 129 256), losses := [] }

theorem u254 : Upper (D 7) (R 7) [12,96,17,130,288,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 21 138 304 34 192 192 257), lower := (rows 13 98 21 138 304 34 192 192 256), losses := [] }

theorem u255 : Upper (D 7) (R 7) [12,96,17,130,288,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 346, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 138 304 160 66 129 320), lower := (rows 13 98 21 138 304 160 66 129 256), losses := [] }

theorem u256 : Upper (D 7) (R 7) [12,96,17,130,288,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 138 304 160 66 192 257), lower := (rows 13 98 21 138 304 160 66 192 256), losses := [] }

theorem u257 : Upper (D 7) (R 7) [12,96,17,130,288,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 173, targets := 64 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 98 21 168 274 34 192 129 320), lower := (rows 13 98 21 168 274 34 192 129 256), losses := [] }

theorem u258 : Upper (D 7) (R 7) [12,96,17,160,258,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 1, region := 136, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 98 21 168 274 34 192 192 257), lower := (rows 13 98 21 168 274 34 192 192 256), losses := [] }

theorem u259 : Upper (D 7) (R 7) [12,96,17,160,258,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 168 336 34 192 129 258), lower := (rows 13 98 21 168 336 34 192 129 256), losses := [] }

theorem u260 : Upper (D 7) (R 7) [12,96,17,160,320,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 341, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 98 21 168 336 34 192 130 257), lower := (rows 13 98 21 168 336 34 192 130 256), losses := [] }

theorem u261 : Upper (D 7) (R 7) [12,96,17,160,320,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 13 98 21 266 176 34 192 129 320), lower := (rows 13 98 21 266 176 34 192 129 256), losses := [] }

theorem u262 : Upper (D 7) (R 7) [12,96,17,258,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 1, region := 144, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 21 266 176 34 192 192 257), lower := (rows 13 98 21 266 176 34 192 192 256), losses := [] }

theorem u263 : Upper (D 7) (R 7) [12,96,17,258,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 296 146 34 192 129 320), lower := (rows 13 98 21 296 146 34 192 129 256), losses := [] }

theorem u264 : Upper (D 7) (R 7) [12,96,17,288,130,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 21 296 146 34 192 192 257), lower := (rows 13 98 21 296 146 34 192 192 256), losses := [] }

theorem u265 : Upper (D 7) (R 7) [12,96,17,288,130,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 346, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 296 146 160 66 129 320), lower := (rows 13 98 21 296 146 160 66 129 256), losses := [] }

theorem u266 : Upper (D 7) (R 7) [12,96,17,288,130,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 296 146 160 66 192 257), lower := (rows 13 98 21 296 146 160 66 192 256), losses := [] }

theorem u267 : Upper (D 7) (R 7) [12,96,17,288,130,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 346, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 296 208 160 66 129 258), lower := (rows 13 98 21 296 208 160 66 129 256), losses := [] }

theorem u268 : Upper (D 7) (R 7) [12,96,17,288,192,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 296 208 160 66 130 257), lower := (rows 13 98 21 296 208 160 66 130 256), losses := [] }

theorem u269 : Upper (D 7) (R 7) [12,96,17,288,192,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 276, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 22 138 304 33 192 129 320), lower := (rows 13 98 22 138 304 33 192 129 256), losses := [] }

theorem u270 : Upper (D 7) (R 7) [12,96,18,130,288,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 22 138 304 33 192 192 257), lower := (rows 13 98 22 138 304 33 192 192 256), losses := [] }

theorem u271 : Upper (D 7) (R 7) [12,96,18,130,288,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 5, region := 202, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(3,6)], upper := (rows 13 98 22 168 273 33 192 130 320), lower := (rows 13 98 22 168 273 33 192 130 256), losses := [] }

theorem u272 : Upper (D 7) (R 7) [12,96,18,160,257,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 233, targets := 2 },{ cop := 5, region := 202, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(3,1)], upper := (rows 13 98 22 168 273 33 192 192 258), lower := (rows 13 98 22 168 273 33 192 192 256), losses := [] }

theorem u273 : Upper (D 7) (R 7) [12,96,18,160,257,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 13 98 22 168 336 33 192 129 258), lower := (rows 13 98 22 168 336 33 192 129 256), losses := [] }

theorem u274 : Upper (D 7) (R 7) [12,96,18,160,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 5, region := 202, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(3,6)], upper := (rows 13 98 22 168 336 33 192 130 257), lower := (rows 13 98 22 168 336 33 192 130 256), losses := [] }

theorem u275 : Upper (D 7) (R 7) [12,96,18,160,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 138 274 48 192 129 320), lower := (rows 13 98 37 138 274 48 192 129 256), losses := [] }

theorem u276 : Upper (D 7) (R 7) [12,96,33,130,258,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b276 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 13 98 37 138 274 48 192 192 257), lower := (rows 13 98 37 138 274 48 192 192 256), losses := [] }

theorem u277 : Upper (D 7) (R 7) [12,96,33,130,258,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b277 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 328 146 160 66 129 272), lower := (rows 13 98 37 328 146 160 66 129 256), losses := [] }

theorem u278 : Upper (D 7) (R 7) [12,96,33,320,130,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 37 328 146 160 66 144 257), lower := (rows 13 98 37 328 146 160 66 144 256), losses := [] }

theorem u279 : Upper (D 7) (R 7) [12,96,33,320,130,128,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b279 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 173, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 137 336 160 66 129 258), lower := (rows 13 98 52 137 336 160 66 129 256), losses := [] }

theorem u280 : Upper (D 7) (R 7) [12,96,48,129,320,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 13 98 52 137 336 160 66 130 257), lower := (rows 13 98 52 137 336 160 66 130 256), losses := [] }

theorem u281 : Upper (D 7) (R 7) [12,96,48,129,320,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 322, targets := 129 },{ cop := 4, region := 164, targets := 2 }], pairs := [(1,0),(1,7),(2,1)], upper := (rows 13 98 52 138 81 160 320 129 258), lower := (rows 13 98 52 138 81 160 320 129 256), losses := [] }

theorem u282 : Upper (D 7) (R 7) [12,96,48,130,65,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b282 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 13 98 52 138 81 160 320 130 257), lower := (rows 13 98 52 138 81 160 320 130 256), losses := [] }

theorem u283 : Upper (D 7) (R 7) [12,96,48,130,65,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b283 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 322, targets := 129 },{ cop := 3, region := 336, targets := 1 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 52 138 208 33 320 129 258), lower := (rows 13 98 52 138 208 33 320 129 256), losses := [] }

theorem u284 : Upper (D 7) (R 7) [12,96,48,130,192,1,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b284 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 13 98 52 138 208 33 320 130 257), lower := (rows 13 98 52 138 208 33 320 130 256), losses := [] }

theorem u285 : Upper (D 7) (R 7) [12,96,48,130,192,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b285 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 13 98 52 138 208 288 65 129 258), lower := (rows 13 98 52 138 208 288 65 129 256), losses := [] }

theorem u286 : Upper (D 7) (R 7) [12,96,48,130,192,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b286 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 13 98 52 138 208 288 65 130 257), lower := (rows 13 98 52 138 208 288 65 130 256), losses := [] }

theorem u287 : Upper (D 7) (R 7) [12,96,48,130,192,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b287 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 276, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 138 274 33 192 129 320), lower := (rows 13 98 52 138 274 33 192 129 256), losses := [] }

theorem u288 : Upper (D 7) (R 7) [12,96,48,130,258,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 52 138 274 33 192 192 257), lower := (rows 13 98 52 138 274 33 192 192 256), losses := [] }

theorem u289 : Upper (D 7) (R 7) [12,96,48,130,258,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 138 336 33 192 129 258), lower := (rows 13 98 52 138 336 33 192 129 256), losses := [] }

theorem u290 : Upper (D 7) (R 7) [12,96,48,130,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 373, targets := 2 },{ cop := 1, region := 136, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 98 52 138 336 33 192 130 257), lower := (rows 13 98 52 138 336 33 192 130 256), losses := [] }

theorem u291 : Upper (D 7) (R 7) [12,96,48,130,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 138 336 160 65 129 258), lower := (rows 13 98 52 138 336 160 65 129 256), losses := [] }

theorem u292 : Upper (D 7) (R 7) [12,96,48,130,320,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 98 52 138 336 160 65 130 257), lower := (rows 13 98 52 138 336 160 65 130 256), losses := [] }

theorem u293 : Upper (D 7) (R 7) [12,96,48,130,320,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 3, region := 336, targets := 33 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 52 138 400 33 66 129 320), lower := (rows 13 98 52 138 400 33 66 129 256), losses := [] }

theorem u294 : Upper (D 7) (R 7) [12,96,48,130,384,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 138 400 33 66 192 257), lower := (rows 13 98 52 138 400 33 66 192 256), losses := [] }

theorem u295 : Upper (D 7) (R 7) [12,96,48,130,384,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 322, targets := 129 },{ cop := 4, region := 328, targets := 1 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 52 200 146 33 320 129 258), lower := (rows 13 98 52 200 146 33 320 129 256), losses := [] }

theorem u296 : Upper (D 7) (R 7) [12,96,48,192,130,1,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b296 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 13 98 52 200 146 33 320 130 257), lower := (rows 13 98 52 200 146 33 320 130 256), losses := [] }

theorem u297 : Upper (D 7) (R 7) [12,96,48,192,130,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b297 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 13 98 52 200 146 288 65 129 258), lower := (rows 13 98 52 200 146 288 65 129 256), losses := [] }

theorem u298 : Upper (D 7) (R 7) [12,96,48,192,130,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b298 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 13 98 52 200 146 288 65 130 257), lower := (rows 13 98 52 200 146 288 65 130 256), losses := [] }

theorem u299 : Upper (D 7) (R 7) [12,96,48,192,130,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b299 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P07
