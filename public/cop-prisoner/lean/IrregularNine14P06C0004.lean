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

def b240 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 140 274 33 68 129 320), lower := (rows 11 98 52 140 274 33 68 129 256), losses := [] }

theorem u240 : Upper (D 6) (R 6) [10,96,48,132,258,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 136, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 52 140 274 33 68 192 257), lower := (rows 11 98 52 140 274 33 68 192 256), losses := [] }

theorem u241 : Upper (D 6) (R 6) [10,96,48,132,258,1,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 140 336 33 68 129 258), lower := (rows 11 98 52 140 336 33 68 129 256), losses := [] }

theorem u242 : Upper (D 6) (R 6) [10,96,48,132,320,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 98 52 140 336 33 68 130 257), lower := (rows 11 98 52 140 336 33 68 130 256), losses := [] }

theorem u243 : Upper (D 6) (R 6) [10,96,48,132,320,1,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 5 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 98 134 28 304 33 68 129 320), lower := (rows 11 98 134 28 304 33 68 129 256), losses := [] }

theorem u244 : Upper (D 6) (R 6) [10,96,130,20,288,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 304, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 98 134 28 304 33 68 192 257), lower := (rows 11 98 134 28 304 33 68 192 256), losses := [] }

theorem u245 : Upper (D 6) (R 6) [10,96,130,20,288,1,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 306, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 148 13 304 34 68 129 320), lower := (rows 11 98 148 13 304 34 68 129 256), losses := [] }

theorem u246 : Upper (D 6) (R 6) [10,96,144,5,288,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 304 34 68 192 257), lower := (rows 11 98 148 13 304 34 68 192 256), losses := [] }

theorem u247 : Upper (D 6) (R 6) [10,96,144,5,288,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 148 13 304 36 66 129 320), lower := (rows 11 98 148 13 304 36 66 129 256), losses := [] }

theorem u248 : Upper (D 6) (R 6) [10,96,144,5,288,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 304 36 66 192 257), lower := (rows 11 98 148 13 304 36 66 192 256), losses := [] }

theorem u249 : Upper (D 6) (R 6) [10,96,144,5,288,4,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 151, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 296 52 96 65 132 320), lower := (rows 11 131 22 296 52 96 65 132 256), losses := [] }

theorem u250 : Upper (D 6) (R 6) [10,129,18,288,36,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 264, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 22 296 52 96 65 192 260), lower := (rows 11 131 22 296 52 96 65 192 256), losses := [] }

theorem u251 : Upper (D 6) (R 6) [10,129,18,288,36,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 264, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 22 296 112 36 65 132 320), lower := (rows 11 131 22 296 112 36 65 132 256), losses := [] }

theorem u252 : Upper (D 6) (R 6) [10,129,18,288,96,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 22 296 112 36 65 192 260), lower := (rows 11 131 22 296 112 36 65 192 256), losses := [] }

theorem u253 : Upper (D 6) (R 6) [10,129,18,288,96,4,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 56 273 96 68 132 320), lower := (rows 11 131 38 56 273 96 68 132 256), losses := [] }

theorem u254 : Upper (D 6) (R 6) [10,129,34,48,257,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 131 38 56 273 96 68 192 260), lower := (rows 11 131 38 56 273 96 68 192 256), losses := [] }

theorem u255 : Upper (D 6) (R 6) [10,129,34,48,257,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 88 273 96 68 132 288), lower := (rows 11 131 38 88 273 96 68 132 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 255 215 215 511), good := (rows 494 486 486 504 508 480 484 484 256) },{ target := 1, region := (rows 1 0 4 14 19 238 196 196 495), good := (rows 313 505 508 504 273 480 492 492 256) }] }

theorem u256 : Upper (D 6) (R 6) [10,129,34,80,257,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 131 38 88 273 96 68 160 260), lower := (rows 11 131 38 88 273 96 68 160 256), losses := [] }

theorem u257 : Upper (D 6) (R 6) [10,129,34,80,257,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 88 304 96 68 129 260), lower := (rows 11 131 38 88 304 96 68 129 256), losses := [] }

theorem u258 : Upper (D 6) (R 6) [10,129,34,80,288,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,1),(4,1)], upper := (rows 11 131 38 88 304 96 68 132 257), lower := (rows 11 131 38 88 304 96 68 132 256), losses := [{ target := 1, region := (rows 1 0 4 206 23 238 196 196 259), good := (rows 313 505 508 248 304 232 252 252 256) }] }

theorem u259 : Upper (D 6) (R 6) [10,129,34,80,288,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 134, targets := 64 },{ cop := 0, region := 100, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 280 49 96 68 132 320), lower := (rows 11 131 38 280 49 96 68 132 256), losses := [] }

theorem u260 : Upper (D 6) (R 6) [10,129,34,272,33,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 131 38 280 49 96 68 192 260), lower := (rows 11 131 38 280 49 96 68 192 256), losses := [] }

theorem u261 : Upper (D 6) (R 6) [10,129,34,272,33,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 296 81 96 68 132 272), lower := (rows 11 131 38 296 81 96 68 132 256), losses := [] }

theorem u262 : Upper (D 6) (R 6) [10,129,34,288,65,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 364, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 131 38 296 81 96 68 144 260), lower := (rows 11 131 38 296 81 96 68 144 256), losses := [] }

theorem u263 : Upper (D 6) (R 6) [10,129,34,288,65,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b263 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 348, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 104 336 34 68 129 260), lower := (rows 11 131 52 104 336 34 68 129 256), losses := [] }

theorem u264 : Upper (D 6) (R 6) [10,129,48,96,320,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 52 104 336 34 68 132 257), lower := (rows 11 131 52 104 336 34 68 132 256), losses := [{ target := 1, region := (rows 1 0 44 44 51 32 237 237 259), good := (rows 477 465 252 252 464 508 204 204 256) }] }

theorem u265 : Upper (D 6) (R 6) [10,129,48,96,320,2,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 151, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 296 22 96 65 132 320), lower := (rows 11 131 52 296 22 96 65 132 256), losses := [] }

theorem u266 : Upper (D 6) (R 6) [10,129,48,288,6,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 264, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 52 296 22 96 65 192 260), lower := (rows 11 131 52 296 22 96 65 192 256), losses := [] }

theorem u267 : Upper (D 6) (R 6) [10,129,48,288,6,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 147, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 131 261 44 22 96 96 144 320), lower := (rows 11 131 261 44 22 96 96 144 256), losses := [] }

theorem u268 : Upper (D 6) (R 6) [10,129,257,36,6,64,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b268 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 131 261 44 22 96 96 192 272), lower := (rows 11 131 261 44 22 96 96 192 256), losses := [] }

theorem u269 : Upper (D 6) (R 6) [10,129,257,36,6,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 37 28 274 96 96 129 320), lower := (rows 11 134 37 28 274 96 96 129 256), losses := [] }

theorem u270 : Upper (D 6) (R 6) [10,132,33,20,258,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 37 28 274 96 96 192 257), lower := (rows 11 134 37 28 274 96 96 192 256), losses := [] }

theorem u271 : Upper (D 6) (R 6) [10,132,33,20,258,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 146, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 37 268 50 96 65 144 320), lower := (rows 11 134 37 268 50 96 65 144 256), losses := [] }

theorem u272 : Upper (D 6) (R 6) [10,132,33,260,34,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b272 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 134 37 268 50 96 65 192 272), lower := (rows 11 134 37 268 50 96 65 192 256), losses := [] }

theorem u273 : Upper (D 6) (R 6) [10,132,33,260,34,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 134 38 25 84 96 320 129 288), lower := (rows 11 134 38 25 84 96 320 129 256), losses := [] }

theorem u274 : Upper (D 6) (R 6) [10,132,34,17,68,64,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b274 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 38 25 84 96 320 160 257), lower := (rows 11 134 38 25 84 96 320 160 256), losses := [] }

theorem u275 : Upper (D 6) (R 6) [10,132,34,17,68,64,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b275 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 38 25 276 96 96 129 320), lower := (rows 11 134 38 25 276 96 96 129 256), losses := [] }

theorem u276 : Upper (D 6) (R 6) [10,132,34,17,260,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 38 25 276 96 96 192 257), lower := (rows 11 134 38 25 276 96 96 192 256), losses := [] }

theorem u277 : Upper (D 6) (R 6) [10,132,34,17,260,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 56 276 96 65 129 320), lower := (rows 11 134 38 56 276 96 65 129 256), losses := [] }

theorem u278 : Upper (D 6) (R 6) [10,132,34,48,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 38 56 276 96 65 192 257), lower := (rows 11 134 38 56 276 96 65 192 256), losses := [] }

theorem u279 : Upper (D 6) (R 6) [10,132,34,48,260,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 73 276 96 80 129 288), lower := (rows 11 134 38 73 276 96 80 129 256), losses := [] }

theorem u280 : Upper (D 6) (R 6) [10,132,34,65,260,64,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b280 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 38 73 276 96 80 160 257), lower := (rows 11 134 38 73 276 96 80 160 256), losses := [] }

theorem u281 : Upper (D 6) (R 6) [10,132,34,65,260,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b281 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 88 276 96 65 129 288), lower := (rows 11 134 38 88 276 96 65 129 256), losses := [] }

theorem u282 : Upper (D 6) (R 6) [10,132,34,80,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 88 276 96 65 160 257), lower := (rows 11 134 38 88 276 96 65 160 256), losses := [] }

theorem u283 : Upper (D 6) (R 6) [10,132,34,80,260,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 88 304 96 65 129 260), lower := (rows 11 134 38 88 304 96 65 129 256), losses := [] }

theorem u284 : Upper (D 6) (R 6) [10,132,34,80,288,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 376, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 11 134 38 88 304 96 65 132 257), lower := (rows 11 134 38 88 304 96 65 132 256), losses := [] }

theorem u285 : Upper (D 6) (R 6) [10,132,34,80,288,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 38 104 84 33 320 129 272), lower := (rows 11 134 38 104 84 33 320 129 256), losses := [] }

theorem u286 : Upper (D 6) (R 6) [10,132,34,96,68,1,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b286 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 150, targets := 1 }], pairs := [(1,0)], upper := (rows 11 134 38 104 84 33 320 144 257), lower := (rows 11 134 38 104 84 33 320 144 256), losses := [] }

theorem u287 : Upper (D 6) (R 6) [10,132,34,96,68,1,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b287 [(6,8),(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 38 104 276 33 80 129 320), lower := (rows 11 134 38 104 276 33 80 129 256), losses := [] }

theorem u288 : Upper (D 6) (R 6) [10,132,34,96,260,1,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b288 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 134 38 104 276 33 80 192 257), lower := (rows 11 134 38 104 276 33 80 192 256), losses := [] }

theorem u289 : Upper (D 6) (R 6) [10,132,34,96,260,1,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b289 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 296, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 280 84 96 65 129 288), lower := (rows 11 134 38 280 84 96 65 129 256), losses := [] }

theorem u290 : Upper (D 6) (R 6) [10,132,34,272,68,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 280 84 96 65 160 257), lower := (rows 11 134 38 280 84 96 65 160 256), losses := [] }

theorem u291 : Upper (D 6) (R 6) [10,132,34,272,68,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 296 84 96 65 129 272), lower := (rows 11 134 38 296 84 96 65 129 256), losses := [] }

theorem u292 : Upper (D 6) (R 6) [10,132,34,288,68,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 38 296 84 96 65 144 257), lower := (rows 11 134 38 296 84 96 65 144 256), losses := [] }

theorem u293 : Upper (D 6) (R 6) [10,132,34,288,68,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b293 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 41 276 96 66 129 320), lower := (rows 11 134 52 41 276 96 66 129 256), losses := [] }

theorem u294 : Upper (D 6) (R 6) [10,132,48,33,260,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 276, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 134 52 41 276 96 66 192 257), lower := (rows 11 134 52 41 276 96 66 192 256), losses := [] }

theorem u295 : Upper (D 6) (R 6) [10,132,48,33,260,64,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 73 276 34 96 129 320), lower := (rows 11 134 52 73 276 34 96 129 256), losses := [] }

theorem u296 : Upper (D 6) (R 6) [10,132,48,65,260,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 73 276 34 96 192 257), lower := (rows 11 134 52 73 276 34 96 192 256), losses := [] }

theorem u297 : Upper (D 6) (R 6) [10,132,48,65,260,2,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 73 336 34 96 129 260), lower := (rows 11 134 52 73 336 34 96 129 256), losses := [] }

theorem u298 : Upper (D 6) (R 6) [10,132,48,65,320,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 377, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 52 73 336 34 96 132 257), lower := (rows 11 134 52 73 336 34 96 132 256), losses := [] }

theorem u299 : Upper (D 6) (R 6) [10,132,48,65,320,2,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P06
