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

def b8280 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 131 292 14 84 96 65 146 274), lower := (rows 41 131 292 14 84 96 65 128 256), losses := [] }

theorem u8280 : Upper (D 6) (R 6) [40,129,288,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8281 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 1 },{ cop := 3, region := 97, targets := 4 },{ cop := 3, region := 80, targets := 32 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 41 131 292 14 84 96 66 145 273), lower := (rows 41 131 292 14 84 96 66 128 256), losses := [] }

theorem u8281 : Upper (D 6) (R 6) [40,129,288,6,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8282 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 292 14 84 96 80 131 259), lower := (rows 41 131 292 14 84 96 80 128 256), losses := [] }

theorem u8282 : Upper (D 6) (R 6) [40,129,288,6,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8282 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8283 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 41 131 292 25 84 34 66 196 324), lower := (rows 41 131 292 25 84 34 66 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 98 98 128 256), good := (rows 105 227 352 25 121 98 98 128 256) }] }

theorem u8283 : Upper (D 6) (R 6) [40,129,288,17,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8284 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 292 25 84 34 68 194 322), lower := (rows 41 131 292 25 84 34 68 128 256), losses := [] }

theorem u8284 : Upper (D 6) (R 6) [40,129,288,17,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8285 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 356, targets := 1 },{ cop := 1, region := 80, targets := 4 },{ cop := 1, region := 80, targets := 32 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 41 131 292 28 81 34 66 196 324), lower := (rows 41 131 292 28 81 34 66 128 256), losses := [] }

theorem u8285 : Upper (D 6) (R 6) [40,129,288,20,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8286 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 292 28 81 34 68 194 322), lower := (rows 41 131 292 28 81 34 68 128 256), losses := [] }

theorem u8286 : Upper (D 6) (R 6) [40,129,288,20,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8287 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 292 73 22 34 68 208 336), lower := (rows 41 131 292 73 22 34 68 128 256), losses := [] }

theorem u8287 : Upper (D 6) (R 6) [40,129,288,65,6,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8288 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 41 131 292 73 22 34 80 196 324), lower := (rows 41 131 292 73 22 34 80 128 256), losses := [] }

theorem u8288 : Upper (D 6) (R 6) [40,129,288,65,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8288 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8289 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 292 73 84 34 66 148 276), lower := (rows 41 131 292 73 84 34 66 128 256), losses := [] }

theorem u8289 : Upper (D 6) (R 6) [40,129,288,65,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8290 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 292 73 84 34 68 146 274), lower := (rows 41 131 292 73 84 34 68 128 256), losses := [] }

theorem u8290 : Upper (D 6) (R 6) [40,129,288,65,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8291 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 41 131 292 73 84 34 80 134 262), lower := (rows 41 131 292 73 84 34 80 128 256), losses := [] }

theorem u8291 : Upper (D 6) (R 6) [40,129,288,65,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8291 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8292 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 41 131 292 74 22 48 65 196 324), lower := (rows 41 131 292 74 22 48 65 128 256), losses := [] }

theorem u8292 : Upper (D 6) (R 6) [40,129,288,66,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8292 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8293 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 4, region := 72, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 41 131 292 74 22 48 68 193 321), lower := (rows 41 131 292 74 22 48 68 128 256), losses := [] }

theorem u8293 : Upper (D 6) (R 6) [40,129,288,66,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8293 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8294 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(1,5),(3,1)], upper := (rows 41 131 292 76 22 34 65 208 336), lower := (rows 41 131 292 76 22 34 65 128 256), losses := [{ target := 5, region := (rows 1 67 4 24 24 0 67 153 281), good := (rows 475 451 260 478 478 66 451 128 256) }] }

theorem u8294 : Upper (D 6) (R 6) [40,129,288,68,6,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8295 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 131 292 76 22 34 80 193 321), lower := (rows 41 131 292 76 22 34 80 128 256), losses := [] }

theorem u8295 : Upper (D 6) (R 6) [40,129,288,68,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8295 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8296 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 41 131 292 76 81 34 66 148 276), lower := (rows 41 131 292 76 81 34 66 128 256), losses := [] }

theorem u8296 : Upper (D 6) (R 6) [40,129,288,68,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8297 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 292 76 81 34 68 146 274), lower := (rows 41 131 292 76 81 34 68 128 256), losses := [] }

theorem u8297 : Upper (D 6) (R 6) [40,129,288,68,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8298 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 41 131 292 76 81 34 80 134 262), lower := (rows 41 131 292 76 81 34 80 128 256), losses := [] }

theorem u8298 : Upper (D 6) (R 6) [40,129,288,68,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8298 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8299 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 73, targets := 2 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,1),(2,0),(3,1)], upper := (rows 41 131 292 76 82 34 65 148 276), lower := (rows 41 131 292 76 82 34 65 128 256), losses := [] }

theorem u8299 : Upper (D 6) (R 6) [40,129,288,68,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8300 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 131 292 76 82 34 68 145 273), lower := (rows 41 131 292 76 82 34 68 128 256), losses := [] }

theorem u8300 : Upper (D 6) (R 6) [40,129,288,68,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8301 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 292 76 82 34 80 133 261), lower := (rows 41 131 292 76 82 34 80 128 256), losses := [] }

theorem u8301 : Upper (D 6) (R 6) [40,129,288,68,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8301 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8302 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 131 324 13 82 34 68 176 304), lower := (rows 41 131 324 13 82 34 68 128 256), losses := [] }

theorem u8302 : Upper (D 6) (R 6) [40,129,320,5,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8303 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 324 13 82 34 80 164 292), lower := (rows 41 131 324 13 82 34 80 128 256), losses := [] }

theorem u8303 : Upper (D 6) (R 6) [40,129,320,5,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8303 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8304 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 260, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 41 131 324 13 82 34 96 148 276), lower := (rows 41 131 324 13 82 34 96 128 256), losses := [] }

theorem u8304 : Upper (D 6) (R 6) [40,129,320,5,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8305 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 131 324 13 112 34 66 148 276), lower := (rows 41 131 324 13 112 34 66 128 256), losses := [] }

theorem u8305 : Upper (D 6) (R 6) [40,129,320,5,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8306 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 131 324 13 112 34 68 146 274), lower := (rows 41 131 324 13 112 34 68 128 256), losses := [] }

theorem u8306 : Upper (D 6) (R 6) [40,129,320,5,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8307 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 324 13 112 34 80 134 262), lower := (rows 41 131 324 13 112 34 80 128 256), losses := [] }

theorem u8307 : Upper (D 6) (R 6) [40,129,320,5,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8307 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8308 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 41 131 324 14 81 48 66 164 292), lower := (rows 41 131 324 14 81 48 66 128 256), losses := [] }

theorem u8308 : Upper (D 6) (R 6) [40,129,320,6,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8308 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8309 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 131 324 14 81 48 68 162 290), lower := (rows 41 131 324 14 81 48 68 128 256), losses := [] }

theorem u8309 : Upper (D 6) (R 6) [40,129,320,6,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8309 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8310 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 324 14 81 48 96 134 262), lower := (rows 41 131 324 14 81 48 96 128 256), losses := [] }

theorem u8310 : Upper (D 6) (R 6) [40,129,320,6,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8310 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8311 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 41 131 324 14 82 48 65 164 292), lower := (rows 41 131 324 14 82 48 65 128 256), losses := [] }

theorem u8311 : Upper (D 6) (R 6) [40,129,320,6,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8311 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8312 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 131 324 14 82 48 68 161 289), lower := (rows 41 131 324 14 82 48 68 128 256), losses := [] }

theorem u8312 : Upper (D 6) (R 6) [40,129,320,6,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8312 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8313 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 112, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 41 131 324 14 82 48 96 133 261), lower := (rows 41 131 324 14 82 48 96 128 256), losses := [] }

theorem u8313 : Upper (D 6) (R 6) [40,129,320,6,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8313 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8314 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 41 131 324 25 82 36 66 164 292), lower := (rows 41 131 324 25 82 36 66 128 256), losses := [] }

theorem u8314 : Upper (D 6) (R 6) [40,129,320,17,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8315 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 41 131 324 25 82 36 68 162 290), lower := (rows 41 131 324 25 82 36 68 128 256), losses := [] }

theorem u8315 : Upper (D 6) (R 6) [40,129,320,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8316 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 260, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 324 25 82 36 96 134 262), lower := (rows 41 131 324 25 82 36 96 128 256), losses := [] }

theorem u8316 : Upper (D 6) (R 6) [40,129,320,17,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8317 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 3 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 41 131 324 26 21 96 66 164 292), lower := (rows 41 131 324 26 21 96 66 128 256), losses := [] }

theorem u8317 : Upper (D 6) (R 6) [40,129,320,18,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8318 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 41 131 324 26 21 96 68 162 290), lower := (rows 41 131 324 26 21 96 68 128 256), losses := [] }

theorem u8318 : Upper (D 6) (R 6) [40,129,320,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8319 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 41 131 324 26 21 96 96 134 262), lower := (rows 41 131 324 26 21 96 96 128 256), losses := [] }

theorem u8319 : Upper (D 6) (R 6) [40,129,320,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8320 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 41 131 324 26 81 36 66 164 292), lower := (rows 41 131 324 26 81 36 66 128 256), losses := [] }

theorem u8320 : Upper (D 6) (R 6) [40,129,320,18,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8321 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 41 131 324 26 81 36 68 162 290), lower := (rows 41 131 324 26 81 36 68 128 256), losses := [] }

theorem u8321 : Upper (D 6) (R 6) [40,129,320,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8322 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 324 26 81 36 96 134 262), lower := (rows 41 131 324 26 81 36 96 128 256), losses := [] }

theorem u8322 : Upper (D 6) (R 6) [40,129,320,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8323 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 131 324 73 22 34 68 176 304), lower := (rows 41 131 324 73 22 34 68 128 256), losses := [] }

theorem u8323 : Upper (D 6) (R 6) [40,129,320,65,6,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8324 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 41 131 324 73 22 34 80 164 292), lower := (rows 41 131 324 73 22 34 80 128 256), losses := [] }

theorem u8324 : Upper (D 6) (R 6) [40,129,320,65,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8324 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8325 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 324 73 22 34 96 148 276), lower := (rows 41 131 324 73 22 34 96 128 256), losses := [] }

theorem u8325 : Upper (D 6) (R 6) [40,129,320,65,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8326 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 324 73 52 34 66 148 276), lower := (rows 41 131 324 73 52 34 66 128 256), losses := [] }

theorem u8326 : Upper (D 6) (R 6) [40,129,320,65,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8327 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 131 324 73 52 34 68 146 274), lower := (rows 41 131 324 73 52 34 68 128 256), losses := [] }

theorem u8327 : Upper (D 6) (R 6) [40,129,320,65,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8328 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 73, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 324 73 52 34 80 134 262), lower := (rows 41 131 324 73 52 34 80 128 256), losses := [] }

theorem u8328 : Upper (D 6) (R 6) [40,129,320,65,36,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8328 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8329 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 324 74 21 36 66 176 304), lower := (rows 41 131 324 74 21 36 66 128 256), losses := [] }

theorem u8329 : Upper (D 6) (R 6) [40,129,320,66,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8330 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 130, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 41 131 324 74 21 36 80 162 290), lower := (rows 41 131 324 74 21 36 80 128 256), losses := [] }

theorem u8330 : Upper (D 6) (R 6) [40,129,320,66,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8330 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8331 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 36 },{ cop := 8, region := 100, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 41 131 324 74 21 36 96 146 274), lower := (rows 41 131 324 74 21 36 96 128 256), losses := [] }

theorem u8331 : Upper (D 6) (R 6) [40,129,320,66,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8332 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 72, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 41 131 324 74 21 48 66 164 292), lower := (rows 41 131 324 74 21 48 66 128 256), losses := [] }

theorem u8332 : Upper (D 6) (R 6) [40,129,320,66,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8332 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8333 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 131 324 74 21 48 68 162 290), lower := (rows 41 131 324 74 21 48 68 128 256), losses := [] }

theorem u8333 : Upper (D 6) (R 6) [40,129,320,66,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8333 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8334 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 260, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 131 324 74 21 48 96 134 262), lower := (rows 41 131 324 74 21 48 96 128 256), losses := [] }

theorem u8334 : Upper (D 6) (R 6) [40,129,320,66,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8334 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8335 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 41 131 324 74 22 36 65 176 304), lower := (rows 41 131 324 74 22 36 65 128 256), losses := [] }

theorem u8335 : Upper (D 6) (R 6) [40,129,320,66,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8336 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 130, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 41 131 324 74 22 36 80 161 289), lower := (rows 41 131 324 74 22 36 80 128 256), losses := [] }

theorem u8336 : Upper (D 6) (R 6) [40,129,320,66,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8336 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8337 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 4, region := 104, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 41 131 324 74 22 36 96 145 273), lower := (rows 41 131 324 74 22 36 96 128 256), losses := [] }

theorem u8337 : Upper (D 6) (R 6) [40,129,320,66,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8338 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 41 131 324 74 22 48 65 164 292), lower := (rows 41 131 324 74 22 48 65 128 256), losses := [] }

theorem u8338 : Upper (D 6) (R 6) [40,129,320,66,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8338 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8339 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 131 324 74 22 48 68 161 289), lower := (rows 41 131 324 74 22 48 68 128 256), losses := [] }

theorem u8339 : Upper (D 6) (R 6) [40,129,320,66,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8339 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8339
end Delivery.IrregularNine14.P06
