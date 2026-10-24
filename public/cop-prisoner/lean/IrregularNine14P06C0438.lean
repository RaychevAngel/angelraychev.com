import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0136

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26280 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 388 14 21 96 83 147 275), lower := (rows 41 98 388 14 21 96 64 128 256), losses := [] }

theorem u26280 : Upper (D 6) (R 6) [40,96,384,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26281 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 14 81 33 86 150 278), lower := (rows 41 98 388 14 81 33 64 128 256), losses := [] }

theorem u26281 : Upper (D 6) (R 6) [40,96,384,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26282 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 388 14 81 34 85 149 277), lower := (rows 41 98 388 14 81 34 64 128 256), losses := [] }

theorem u26282 : Upper (D 6) (R 6) [40,96,384,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26283 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 388 14 81 36 83 147 275), lower := (rows 41 98 388 14 81 36 64 128 256), losses := [] }

theorem u26283 : Upper (D 6) (R 6) [40,96,384,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26284 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 388 14 81 48 71 135 263), lower := (rows 41 98 388 14 81 48 64 128 256), losses := [] }

theorem u26284 : Upper (D 6) (R 6) [40,96,384,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26284 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26285 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 14 84 33 83 147 275), lower := (rows 41 98 388 14 84 33 64 128 256), losses := [] }

theorem u26285 : Upper (D 6) (R 6) [40,96,384,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26286 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 388 14 84 34 81 145 273), lower := (rows 41 98 388 14 84 34 64 128 256), losses := [] }

theorem u26286 : Upper (D 6) (R 6) [40,96,384,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26287 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 388 14 84 48 67 131 259), lower := (rows 41 98 388 14 84 48 64 128 256), losses := [] }

theorem u26287 : Upper (D 6) (R 6) [40,96,384,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26287 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26288 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 25 22 33 70 198 326), lower := (rows 41 98 388 25 22 33 64 128 256), losses := [] }

theorem u26288 : Upper (D 6) (R 6) [40,96,384,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26289 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 388 25 22 34 69 197 325), lower := (rows 41 98 388 25 22 34 64 128 256), losses := [] }

theorem u26289 : Upper (D 6) (R 6) [40,96,384,17,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26290 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 388 25 22 36 67 195 323), lower := (rows 41 98 388 25 22 36 64 128 256), losses := [] }

theorem u26290 : Upper (D 6) (R 6) [40,96,384,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26291 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 388 25 22 96 71 135 263), lower := (rows 41 98 388 25 22 96 64 128 256), losses := [] }

theorem u26291 : Upper (D 6) (R 6) [40,96,384,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26292 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 388 25 84 33 70 134 262), lower := (rows 41 98 388 25 84 33 64 128 256), losses := [] }

theorem u26292 : Upper (D 6) (R 6) [40,96,384,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26293 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 388 25 84 34 71 135 263), lower := (rows 41 98 388 25 84 34 64 128 256), losses := [] }

theorem u26293 : Upper (D 6) (R 6) [40,96,384,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26294 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 388 25 84 36 67 131 259), lower := (rows 41 98 388 25 84 36 64 128 256), losses := [] }

theorem u26294 : Upper (D 6) (R 6) [40,96,384,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26295 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 26 21 33 70 198 326), lower := (rows 41 98 388 26 21 33 64 128 256), losses := [] }

theorem u26295 : Upper (D 6) (R 6) [40,96,384,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26296 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 388 26 21 34 69 197 325), lower := (rows 41 98 388 26 21 34 64 128 256), losses := [] }

theorem u26296 : Upper (D 6) (R 6) [40,96,384,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26297 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,2),(3,2)], upper := (rows 41 98 388 26 21 36 67 195 323), lower := (rows 41 98 388 26 21 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 420 57 53 36 64 128 256) },{ target := 2, region := (rows 1 3 0 24 16 32 81 145 273), good := (rows 491 98 384 474 475 32 64 128 256) }] }

theorem u26297 : Upper (D 6) (R 6) [40,96,384,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26298 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 388 26 21 96 71 135 263), lower := (rows 41 98 388 26 21 96 64 128 256), losses := [] }

theorem u26298 : Upper (D 6) (R 6) [40,96,384,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26299 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 388 26 84 33 71 135 263), lower := (rows 41 98 388 26 84 33 64 128 256), losses := [] }

theorem u26299 : Upper (D 6) (R 6) [40,96,384,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26300 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 388 26 84 34 69 133 261), lower := (rows 41 98 388 26 84 34 64 128 256), losses := [] }

theorem u26300 : Upper (D 6) (R 6) [40,96,384,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26301 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 41 98 388 26 84 36 67 131 259), lower := (rows 41 98 388 26 84 36 64 128 256), losses := [] }

theorem u26301 : Upper (D 6) (R 6) [40,96,384,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26302 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 388 28 19 33 70 198 326), lower := (rows 41 98 388 28 19 33 64 128 256), losses := [] }

theorem u26302 : Upper (D 6) (R 6) [40,96,384,20,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26303 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 388 28 19 34 69 197 325), lower := (rows 41 98 388 28 19 34 64 128 256), losses := [] }

theorem u26303 : Upper (D 6) (R 6) [40,96,384,20,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26304 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 388 28 19 36 67 195 323), lower := (rows 41 98 388 28 19 36 64 128 256), losses := [] }

theorem u26304 : Upper (D 6) (R 6) [40,96,384,20,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26305 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 388 28 19 96 71 135 263), lower := (rows 41 98 388 28 19 96 64 128 256), losses := [] }

theorem u26305 : Upper (D 6) (R 6) [40,96,384,20,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26306 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 28 81 33 70 134 262), lower := (rows 41 98 388 28 81 33 64 128 256), losses := [] }

theorem u26306 : Upper (D 6) (R 6) [40,96,384,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26307 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 388 28 81 34 71 135 263), lower := (rows 41 98 388 28 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 122 64 128 256), good := (rows 41 98 384 59 115 34 98 128 256) }] }

theorem u26307 : Upper (D 6) (R 6) [40,96,384,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26308 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 388 28 81 36 67 131 259), lower := (rows 41 98 388 28 81 36 64 128 256), losses := [] }

theorem u26308 : Upper (D 6) (R 6) [40,96,384,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26309 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 388 76 21 33 82 146 274), lower := (rows 41 98 388 76 21 33 64 128 256), losses := [] }

theorem u26309 : Upper (D 6) (R 6) [40,96,384,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26310 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 388 76 21 34 83 147 275), lower := (rows 41 98 388 76 21 34 64 128 256), losses := [] }

theorem u26310 : Upper (D 6) (R 6) [40,96,384,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26311 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 388 76 21 48 67 131 259), lower := (rows 41 98 388 76 21 48 64 128 256), losses := [] }

theorem u26311 : Upper (D 6) (R 6) [40,96,384,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26311 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26312 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 76 22 33 83 147 275), lower := (rows 41 98 388 76 22 33 64 128 256), losses := [] }

theorem u26312 : Upper (D 6) (R 6) [40,96,384,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26313 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 41 98 388 76 22 34 81 145 273), lower := (rows 41 98 388 76 22 34 64 128 256), losses := [] }

theorem u26313 : Upper (D 6) (R 6) [40,96,384,68,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26314 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 388 76 22 48 67 131 259), lower := (rows 41 98 388 76 22 48 64 128 256), losses := [] }

theorem u26314 : Upper (D 6) (R 6) [40,96,384,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26314 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26315 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 98 388 88 21 33 70 134 262), lower := (rows 41 98 388 88 21 33 64 128 256), losses := [] }

theorem u26315 : Upper (D 6) (R 6) [40,96,384,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26316 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 388 88 21 34 71 135 263), lower := (rows 41 98 388 88 21 34 64 128 256), losses := [] }

theorem u26316 : Upper (D 6) (R 6) [40,96,384,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26317 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 388 88 21 36 67 131 259), lower := (rows 41 98 388 88 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 64 128 256), good := (rows 42 98 420 122 52 36 64 128 256) },{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 420 121 53 36 64 128 256) }] }

theorem u26317 : Upper (D 6) (R 6) [40,96,384,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26318 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 388 88 22 33 71 135 263), lower := (rows 41 98 388 88 22 33 64 128 256), losses := [] }

theorem u26318 : Upper (D 6) (R 6) [40,96,384,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26319 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 388, targets := 34 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,1),(2,5)], upper := (rows 41 98 388 88 22 34 69 133 261), lower := (rows 41 98 388 88 22 34 64 128 256), losses := [] }

theorem u26319 : Upper (D 6) (R 6) [40,96,384,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26320 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 388 88 22 36 67 131 259), lower := (rows 41 98 388 88 22 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 64 128 256), good := (rows 42 98 420 122 54 36 64 128 256) },{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 420 121 52 36 64 128 256) }] }

theorem u26320 : Upper (D 6) (R 6) [40,96,384,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26321 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 131 261 14 50 36 80 208 336), lower := (rows 41 131 261 14 50 36 64 128 256), losses := [] }

theorem u26321 : Upper (D 6) (R 6) [40,129,257,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26322 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 131 261 14 50 48 68 196 324), lower := (rows 41 131 261 14 50 48 64 128 256), losses := [] }

theorem u26322 : Upper (D 6) (R 6) [40,129,257,6,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26322 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26323 : Route 9 := (fun mask => (mask,id))

def c26323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26323 : Upper (D 6) (R 6) [40,129,257,6,34,64] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6,34,64] 13 (by decide) (choices 1) [4,16] r26323 c26323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8192
  · exact u8193

def b26324 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 261 14 82 36 112 240 368), lower := (rows 41 131 261 14 82 36 64 128 256), losses := [] }

theorem u26324 : Upper (D 6) (R 6) [40,129,257,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26325 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 3, region := 112, targets := 1 }], pairs := [(2,1),(4,0)], upper := (rows 41 131 261 14 82 48 100 228 356), lower := (rows 41 131 261 14 82 48 64 128 256), losses := [] }

theorem u26325 : Upper (D 6) (R 6) [40,129,257,6,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26325 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26326 : Route 9 := (fun mask => (mask,id))

def c26326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26326 : Upper (D 6) (R 6) [40,129,257,6,66,64] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6,66,64] 13 (by decide) (choices 1) [4,16,32] r26326 c26326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8194
  · exact u8195
  · exact u8196

def b26327 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 261 14 112 34 84 212 340), lower := (rows 41 131 261 14 112 34 64 128 256), losses := [] }

theorem u26327 : Upper (D 6) (R 6) [40,129,257,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26328 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 261 14 112 48 70 198 326), lower := (rows 41 131 261 14 112 48 64 128 256), losses := [] }

theorem u26328 : Upper (D 6) (R 6) [40,129,257,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26328 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26329 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 261 14 112 96 86 150 278), lower := (rows 41 131 261 14 112 96 64 128 256), losses := [] }

theorem u26329 : Upper (D 6) (R 6) [40,129,257,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26330 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 261 26 84 34 100 228 356), lower := (rows 41 131 261 26 84 34 64 128 256), losses := [] }

theorem u26330 : Upper (D 6) (R 6) [40,129,257,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26331 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 194, targets := 4 }], pairs := [(0,1),(1,2),(3,2)], upper := (rows 41 131 261 26 84 36 98 226 354), lower := (rows 41 131 261 26 84 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 129 293 57 116 36 64 128 256) },{ target := 2, region := (rows 1 7 0 24 16 32 97 161 289), good := (rows 491 451 451 26 90 482 64 128 256) }] }

theorem u26331 : Upper (D 6) (R 6) [40,129,257,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26332 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 131 261 26 84 96 102 166 294), lower := (rows 41 131 261 26 84 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 129 261 57 116 96 96 128 256) }] }

theorem u26332 : Upper (D 6) (R 6) [40,129,257,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26333 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 41 131 261 26 112 34 68 196 324), lower := (rows 41 131 261 26 112 34 64 128 256), losses := [] }

theorem u26333 : Upper (D 6) (R 6) [40,129,257,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26334 : Route 9 := (fun mask => (mask,id))

def c26334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26334 : Upper (D 6) (R 6) [40,129,257,18,96,4] 13 := by
  apply FastRouting.sound _ _ [40,129,257,18,96,4] 13 (by decide) (choices 1) [2,4] r26334 c26334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8197
  · exact u8198

def b26335 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 261 26 112 96 70 134 262), lower := (rows 41 131 261 26 112 96 64 128 256), losses := [] }

theorem u26335 : Upper (D 6) (R 6) [40,129,257,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26336 : Route 9 := (fun mask => (mask,id))

def c26336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26336 : Upper (D 6) (R 6) [40,129,257,66,6,4] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,6,4] 13 (by decide) (choices 1) [16,32] r26336 c26336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8199
  · exact u8200

def b26337 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 41 131 261 74 22 48 100 228 356), lower := (rows 41 131 261 74 22 48 64 128 256), losses := [] }

theorem u26337 : Upper (D 6) (R 6) [40,129,257,66,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26337 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26338 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 261 74 22 96 116 180 308), lower := (rows 41 131 261 74 22 96 64 128 256), losses := [] }

theorem u26338 : Upper (D 6) (R 6) [40,129,257,66,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26339 : Route 9 := (fun mask => (mask,id))

def c26339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26339 : Upper (D 6) (R 6) [40,129,257,66,34,4] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,34,4] 13 (by decide) (choices 1) [4,16] r26339 c26339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8201
  · exact u8202

#print axioms u26339
end Delivery.IrregularNine14.P06
