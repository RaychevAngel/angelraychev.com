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

def b11280 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 290 7 88 145 160 68 138 266), lower := (rows 97 290 7 88 145 160 68 128 256), losses := [] }

theorem u11280 : Upper (D 7) (R 7) [96,288,3,80,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11280 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11281 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 88 145 160 72 134 262), lower := (rows 97 290 7 88 145 160 72 128 256), losses := [] }

theorem u11281 : Upper (D 7) (R 7) [96,288,3,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11281 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11282 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 7 88 146 36 65 136 392), lower := (rows 97 290 7 88 146 36 65 128 256), losses := [] }

theorem u11282 : Upper (D 7) (R 7) [96,288,3,80,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11282 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11283 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 7 88 146 36 72 129 385), lower := (rows 97 290 7 88 146 36 72 128 256), losses := [] }

theorem u11283 : Upper (D 7) (R 7) [96,288,3,80,130,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11283 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11284 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 7 88 146 36 192 137 265), lower := (rows 97 290 7 88 146 36 192 128 256), losses := [] }

theorem u11284 : Upper (D 7) (R 7) [96,288,3,80,130,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11284 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11285 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 88 146 160 65 140 268), lower := (rows 97 290 7 88 146 160 65 128 256), losses := [] }

theorem u11285 : Upper (D 7) (R 7) [96,288,3,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11286 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 290 7 88 146 160 68 137 265), lower := (rows 97 290 7 88 146 160 68 128 256), losses := [] }

theorem u11286 : Upper (D 7) (R 7) [96,288,3,80,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11286 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11287 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 88 146 160 72 133 261), lower := (rows 97 290 7 88 146 160 72 128 256), losses := [] }

theorem u11287 : Upper (D 7) (R 7) [96,288,3,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11287 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11288 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 88 148 160 65 138 266), lower := (rows 97 290 7 88 148 160 65 128 256), losses := [] }

theorem u11288 : Upper (D 7) (R 7) [96,288,3,80,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11289 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 88 148 160 66 137 265), lower := (rows 97 290 7 88 148 160 66 128 256), losses := [] }

theorem u11289 : Upper (D 7) (R 7) [96,288,3,80,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11290 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 88 148 160 72 131 259), lower := (rows 97 290 7 88 148 160 72 128 256), losses := [] }

theorem u11290 : Upper (D 7) (R 7) [96,288,3,80,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11290 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11291 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 402, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 97 290 7 137 146 36 72 208 336), lower := (rows 97 290 7 137 146 36 72 128 256), losses := [] }

theorem u11291 : Upper (D 7) (R 7) [96,288,3,129,130,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11291 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11292 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 97 290 7 137 146 36 80 200 328), lower := (rows 97 290 7 137 146 36 80 128 256), losses := [] }

theorem u11292 : Upper (D 7) (R 7) [96,288,3,129,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11292 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11293 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 136, targets := 34 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(3,1),(3,5)], upper := (rows 97 290 7 137 148 48 66 200 328), lower := (rows 97 290 7 137 148 48 66 128 256), losses := [] }

theorem u11293 : Upper (D 7) (R 7) [96,288,3,129,132,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11293 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11294 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 97 290 7 137 148 48 72 194 322), lower := (rows 97 290 7 137 148 48 72 128 256), losses := [] }

theorem u11294 : Upper (D 7) (R 7) [96,288,3,129,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11294 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11295 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 7 137 208 36 66 152 280), lower := (rows 97 290 7 137 208 36 66 128 256), losses := [] }

theorem u11295 : Upper (D 7) (R 7) [96,288,3,129,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11295 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11296 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 97 290 7 137 208 36 72 146 274), lower := (rows 97 290 7 137 208 36 72 128 256), losses := [] }

theorem u11296 : Upper (D 7) (R 7) [96,288,3,129,192,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11296 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11297 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 7 137 208 36 80 138 266), lower := (rows 97 290 7 137 208 36 80 128 256), losses := [] }

theorem u11297 : Upper (D 7) (R 7) [96,288,3,129,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11297 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11298 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 394, targets := 1 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,0),(3,0)], upper := (rows 97 290 7 138 148 48 65 200 328), lower := (rows 97 290 7 138 148 48 65 128 256), losses := [] }

theorem u11298 : Upper (D 7) (R 7) [96,288,3,130,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11299 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 97 290 7 138 148 48 72 193 321), lower := (rows 97 290 7 138 148 48 72 128 256), losses := [] }

theorem u11299 : Upper (D 7) (R 7) [96,288,3,130,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11299 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11300 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 7 138 208 36 65 152 280), lower := (rows 97 290 7 138 208 36 65 128 256), losses := [] }

theorem u11300 : Upper (D 7) (R 7) [96,288,3,130,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11300 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11301 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 97 290 7 138 208 36 72 145 273), lower := (rows 97 290 7 138 208 36 72 128 256), losses := [] }

theorem u11301 : Upper (D 7) (R 7) [96,288,3,130,192,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11301 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11302 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 7 138 208 36 80 137 265), lower := (rows 97 290 7 138 208 36 80 128 256), losses := [] }

theorem u11302 : Upper (D 7) (R 7) [96,288,3,130,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11302 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11303 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,0),(4,0)], upper := (rows 97 290 7 140 208 40 65 146 274), lower := (rows 97 290 7 140 208 40 65 128 256), losses := [] }

theorem u11303 : Upper (D 7) (R 7) [96,288,3,132,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11303 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11304 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 290 7 140 208 40 66 145 273), lower := (rows 97 290 7 140 208 40 66 128 256), losses := [] }

theorem u11304 : Upper (D 7) (R 7) [96,288,3,132,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11304 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11305 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 262, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 7 140 208 40 80 131 259), lower := (rows 97 290 7 140 208 40 80 128 256), losses := [] }

theorem u11305 : Upper (D 7) (R 7) [96,288,3,132,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11305 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11306 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 14 82 160 65 144 400), lower := (rows 97 290 13 14 82 160 65 128 256), losses := [] }

theorem u11306 : Upper (D 7) (R 7) [96,288,9,6,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11307 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 13 14 82 160 80 129 385), lower := (rows 97 290 13 14 82 160 80 128 256), losses := [] }

theorem u11307 : Upper (D 7) (R 7) [96,288,9,6,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11307 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11308 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 14 82 160 192 145 273), lower := (rows 97 290 13 14 82 160 192 128 256), losses := [] }

theorem u11308 : Upper (D 7) (R 7) [96,288,9,6,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11309 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 290 13 14 145 160 66 208 336), lower := (rows 97 290 13 14 145 160 66 128 256), losses := [] }

theorem u11309 : Upper (D 7) (R 7) [96,288,9,6,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11310 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 14 145 160 80 194 322), lower := (rows 97 290 13 14 145 160 80 128 256), losses := [] }

theorem u11310 : Upper (D 7) (R 7) [96,288,9,6,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11310 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11311 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 402, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 290 13 14 146 160 65 208 336), lower := (rows 97 290 13 14 146 160 65 128 256), losses := [] }

theorem u11311 : Upper (D 7) (R 7) [96,288,9,6,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11312 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 14 146 160 80 193 321), lower := (rows 97 290 13 14 146 160 80 128 256), losses := [] }

theorem u11312 : Upper (D 7) (R 7) [96,288,9,6,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11312 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11313 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 402, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 290 13 14 208 160 65 146 274), lower := (rows 97 290 13 14 208 160 65 128 256), losses := [] }

theorem u11313 : Upper (D 7) (R 7) [96,288,9,6,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11314 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 290 13 14 208 160 66 145 273), lower := (rows 97 290 13 14 208 160 66 128 256), losses := [] }

theorem u11314 : Upper (D 7) (R 7) [96,288,9,6,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11315 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 14 208 160 80 131 259), lower := (rows 97 290 13 14 208 160 80 128 256), losses := [] }

theorem u11315 : Upper (D 7) (R 7) [96,288,9,6,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11315 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11316 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 26 84 160 65 130 386), lower := (rows 97 290 13 26 84 160 65 128 256), losses := [] }

theorem u11316 : Upper (D 7) (R 7) [96,288,9,18,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11317 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 26 84 160 66 129 385), lower := (rows 97 290 13 26 84 160 66 128 256), losses := [] }

theorem u11317 : Upper (D 7) (R 7) [96,288,9,18,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11318 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 26 84 160 192 131 259), lower := (rows 97 290 13 26 84 160 192 128 256), losses := [] }

theorem u11318 : Upper (D 7) (R 7) [96,288,9,18,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11319 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 65, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,5)], upper := (rows 97 290 13 26 145 160 66 196 324), lower := (rows 97 290 13 26 145 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 74 132 260), good := (rows 65 322 477 90 145 128 66 128 256) },{ target := 7, region := (rows 3 2 12 8 16 32 74 0 268), good := (rows 97 355 333 351 17 32 67 0 256) }] }

theorem u11319 : Upper (D 7) (R 7) [96,288,9,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11320 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 258, targets := 1 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 97 290 13 26 145 160 68 194 322), lower := (rows 97 290 13 26 145 160 68 128 256), losses := [{ target := 0, region := (rows 0 87 4 24 16 245 68 197 325), good := (rows 482 290 494 58 442 160 486 160 256) }] }

theorem u11320 : Upper (D 7) (R 7) [96,288,9,18,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11320 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11321 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 1 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 97 290 13 26 148 160 65 194 322), lower := (rows 97 290 13 26 148 160 65 128 256), losses := [] }

theorem u11321 : Upper (D 7) (R 7) [96,288,9,18,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11322 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 290 13 26 148 160 66 193 321), lower := (rows 97 290 13 26 148 160 66 128 256), losses := [{ target := 1, region := (rows 65 0 4 8 20 245 64 193 321), good := (rows 481 288 445 56 180 160 481 160 256) }] }

theorem u11322 : Upper (D 7) (R 7) [96,288,9,18,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11323 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 26 208 36 65 130 386), lower := (rows 97 290 13 26 208 36 65 128 256), losses := [] }

theorem u11323 : Upper (D 7) (R 7) [96,288,9,18,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11323 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11324 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 290 13 26 208 36 66 129 385), lower := (rows 97 290 13 26 208 36 66 128 256), losses := [] }

theorem u11324 : Upper (D 7) (R 7) [96,288,9,18,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11324 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11325 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 13 26 208 36 192 131 259), lower := (rows 97 290 13 26 208 36 192 128 256), losses := [] }

theorem u11325 : Upper (D 7) (R 7) [96,288,9,18,192,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11325 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11326 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 418, targets := 65 },{ cop := 5, region := 81, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(4,1)], upper := (rows 97 290 13 26 208 160 65 134 262), lower := (rows 97 290 13 26 208 160 65 128 256), losses := [] }

theorem u11326 : Upper (D 7) (R 7) [96,288,9,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11327 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 128 },{ cop := 2, region := 418, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 290 13 26 208 160 66 133 261), lower := (rows 97 290 13 26 208 160 66 128 256), losses := [{ target := 1, region := (rows 17 0 12 8 16 188 64 140 268), good := (rows 97 288 429 445 241 160 64 160 256) }] }

theorem u11327 : Upper (D 7) (R 7) [96,288,9,18,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11328 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 258, targets := 64 },{ cop := 0, region := 258, targets := 128 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(1,7)], upper := (rows 97 290 13 26 208 160 68 131 259), lower := (rows 97 290 13 26 208 160 68 128 256), losses := [] }

theorem u11328 : Upper (D 7) (R 7) [96,288,9,18,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11328 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11329 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 28 82 160 65 130 386), lower := (rows 97 290 13 28 82 160 65 128 256), losses := [] }

theorem u11329 : Upper (D 7) (R 7) [96,288,9,20,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11330 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 28 82 160 66 129 385), lower := (rows 97 290 13 28 82 160 66 128 256), losses := [] }

theorem u11330 : Upper (D 7) (R 7) [96,288,9,20,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11331 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 28 82 160 192 131 259), lower := (rows 97 290 13 28 82 160 192 128 256), losses := [] }

theorem u11331 : Upper (D 7) (R 7) [96,288,9,20,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11332 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 5, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 290 13 28 208 34 65 130 386), lower := (rows 97 290 13 28 208 34 65 128 256), losses := [] }

theorem u11332 : Upper (D 7) (R 7) [96,288,9,20,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11333 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 290 13 28 208 34 66 129 385), lower := (rows 97 290 13 28 208 34 66 128 256), losses := [] }

theorem u11333 : Upper (D 7) (R 7) [96,288,9,20,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11334 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 290 13 28 208 34 192 131 259), lower := (rows 97 290 13 28 208 34 192 128 256), losses := [] }

theorem u11334 : Upper (D 7) (R 7) [96,288,9,20,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11335 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 74 22 160 65 144 400), lower := (rows 97 290 13 74 22 160 65 128 256), losses := [] }

theorem u11335 : Upper (D 7) (R 7) [96,288,9,66,6,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11336 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 22 160 80 129 385), lower := (rows 97 290 13 74 22 160 80 128 256), losses := [] }

theorem u11336 : Upper (D 7) (R 7) [96,288,9,66,6,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11336 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11337 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 74 22 160 192 145 273), lower := (rows 97 290 13 74 22 160 192 128 256), losses := [] }

theorem u11337 : Upper (D 7) (R 7) [96,288,9,66,6,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11338 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 145 48 66 132 388), lower := (rows 97 290 13 74 145 48 66 128 256), losses := [] }

theorem u11338 : Upper (D 7) (R 7) [96,288,9,66,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11338 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11339 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 290 13 74 145 48 68 130 386), lower := (rows 97 290 13 74 145 48 68 128 256), losses := [] }

theorem u11339 : Upper (D 7) (R 7) [96,288,9,66,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11339 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11339
end Delivery.IrregularNine14.P07
