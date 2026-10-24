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

def b4260 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 134 292 104 21 33 66 208 336), lower := (rows 11 134 292 104 21 33 66 128 256), losses := [] }

theorem u4260 : Upper (D 6) (R 6) [10,132,288,96,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4261 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 390, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 292 104 21 33 80 194 322), lower := (rows 11 134 292 104 21 33 80 128 256), losses := [] }

theorem u4261 : Upper (D 6) (R 6) [10,132,288,96,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4261 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4262 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 11 134 292 104 21 34 65 208 336), lower := (rows 11 134 292 104 21 34 65 128 256), losses := [] }

theorem u4262 : Upper (D 6) (R 6) [10,132,288,96,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4263 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,0)], upper := (rows 11 134 292 104 21 34 80 193 321), lower := (rows 11 134 292 104 21 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 80 128 256), good := (rows 42 166 292 104 124 34 88 128 256) }] }

theorem u4263 : Upper (D 6) (R 6) [10,132,288,96,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4263 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4264 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 292 104 82 33 65 148 276), lower := (rows 11 134 292 104 82 33 65 128 256), losses := [] }

theorem u4264 : Upper (D 6) (R 6) [10,132,288,96,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4265 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 2, region := 72, targets := 1 }], pairs := [(3,0),(4,0),(4,5)], upper := (rows 11 134 292 104 82 33 68 145 273), lower := (rows 11 134 292 104 82 33 68 128 256), losses := [] }

theorem u4265 : Upper (D 6) (R 6) [10,132,288,96,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4266 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 292 104 82 33 80 133 261), lower := (rows 11 134 292 104 82 33 80 128 256), losses := [] }

theorem u4266 : Upper (D 6) (R 6) [10,132,288,96,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4266 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4267 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 104 84 33 65 146 274), lower := (rows 11 134 292 104 84 33 65 128 256), losses := [] }

theorem u4267 : Upper (D 6) (R 6) [10,132,288,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4268 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 134 292 104 84 33 66 145 273), lower := (rows 11 134 292 104 84 33 66 128 256), losses := [] }

theorem u4268 : Upper (D 6) (R 6) [10,132,288,96,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4269 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 292 104 84 33 80 131 259), lower := (rows 11 134 292 104 84 33 80 128 256), losses := [] }

theorem u4269 : Upper (D 6) (R 6) [10,132,288,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4269 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4270 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 292 104 84 34 65 145 273), lower := (rows 11 134 292 104 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 16 35 64 128 256), good := (rows 42 166 292 104 92 34 104 128 256) }] }

theorem u4270 : Upper (D 6) (R 6) [10,132,288,96,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 292 104 84 34 80 129 257), lower := (rows 11 134 292 104 84 34 80 128 256), losses := [] }

theorem u4271 : Upper (D 6) (R 6) [10,132,288,96,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4271 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 88, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 11 146 37 76 112 288 65 134 262), lower := (rows 11 146 37 76 112 288 65 128 256), losses := [] }

theorem u4272 : Upper (D 6) (R 6) [10,144,33,68,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4272 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4273 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 146 37 76 112 288 66 133 261), lower := (rows 11 146 37 76 112 288 66 128 256), losses := [] }

theorem u4273 : Upper (D 6) (R 6) [10,144,33,68,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4273 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4274 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 146 37 76 112 288 68 131 259), lower := (rows 11 146 37 76 112 288 68 128 256), losses := [] }

theorem u4274 : Upper (D 6) (R 6) [10,144,33,68,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4274 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4275 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 2, region := 264, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 37 265 84 96 66 164 292), lower := (rows 11 146 37 265 84 96 66 128 256), losses := [] }

theorem u4275 : Upper (D 6) (R 6) [10,144,33,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4276 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 146 37 265 84 96 68 162 290), lower := (rows 11 146 37 265 84 96 68 128 256), losses := [] }

theorem u4276 : Upper (D 6) (R 6) [10,144,33,257,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 37 265 84 96 96 134 262), lower := (rows 11 146 37 265 84 96 96 128 256), losses := [] }

theorem u4277 : Upper (D 6) (R 6) [10,144,33,257,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 264, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 37 268 81 96 66 164 292), lower := (rows 11 146 37 268 81 96 66 128 256), losses := [] }

theorem u4278 : Upper (D 6) (R 6) [10,144,33,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 146 37 268 81 96 68 162 290), lower := (rows 11 146 37 268 81 96 68 128 256), losses := [] }

theorem u4279 : Upper (D 6) (R 6) [10,144,33,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 11 146 37 268 81 96 96 134 262), lower := (rows 11 146 37 268 81 96 96 128 256), losses := [] }

theorem u4280 : Upper (D 6) (R 6) [10,144,33,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 146 37 268 84 96 65 162 290), lower := (rows 11 146 37 268 84 96 65 128 256), losses := [] }

theorem u4281 : Upper (D 6) (R 6) [10,144,33,260,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 264, targets := 66 }], pairs := [(3,1),(3,6),(4,0)], upper := (rows 11 146 37 268 84 96 66 161 289), lower := (rows 11 146 37 268 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 119 67 128 256), good := (rows 106 242 116 316 116 96 98 128 256) }] }

theorem u4282 : Upper (D 6) (R 6) [10,144,33,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 37 268 84 96 96 131 259), lower := (rows 11 146 37 268 84 96 96 128 256), losses := [] }

theorem u4283 : Upper (D 6) (R 6) [10,144,33,260,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 146 37 296 84 96 65 134 262), lower := (rows 11 146 37 296 84 96 65 128 256), losses := [] }

theorem u4284 : Upper (D 6) (R 6) [10,144,33,288,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 264, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6)], upper := (rows 11 146 37 296 84 96 66 133 261), lower := (rows 11 146 37 296 84 96 66 128 256), losses := [] }

theorem u4285 : Upper (D 6) (R 6) [10,144,33,288,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4286 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 146 37 296 84 96 68 131 259), lower := (rows 11 146 37 296 84 96 68 128 256), losses := [] }

theorem u4286 : Upper (D 6) (R 6) [10,144,33,288,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4287 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 146 37 328 84 36 65 162 290), lower := (rows 11 146 37 328 84 36 65 128 256), losses := [] }

theorem u4287 : Upper (D 6) (R 6) [10,144,33,320,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4288 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 11 146 37 328 84 36 66 161 289), lower := (rows 11 146 37 328 84 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 52 67 128 256), good := (rows 74 242 116 328 116 52 66 128 256) }] }

theorem u4288 : Upper (D 6) (R 6) [10,144,33,320,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4289 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 146 37 328 84 36 96 131 259), lower := (rows 11 146 37 328 84 36 96 128 256), losses := [] }

theorem u4289 : Upper (D 6) (R 6) [10,144,33,320,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4290 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 146 37 328 112 36 65 134 262), lower := (rows 11 146 37 328 112 36 65 128 256), losses := [] }

theorem u4290 : Upper (D 6) (R 6) [10,144,33,320,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4291 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 11 146 37 328 112 36 66 133 261), lower := (rows 11 146 37 328 112 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 36 67 128 256), good := (rows 74 210 116 328 112 52 66 128 256) }] }

theorem u4291 : Upper (D 6) (R 6) [10,144,33,320,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4292 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 146 37 328 112 36 68 131 259), lower := (rows 11 146 37 328 112 36 68 128 256), losses := [] }

theorem u4292 : Upper (D 6) (R 6) [10,144,33,320,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 146 38 73 84 288 65 164 292), lower := (rows 11 146 38 73 84 288 65 128 256), losses := [] }

theorem u4293 : Upper (D 6) (R 6) [10,144,34,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4293 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4294 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 146 38 73 84 288 68 161 289), lower := (rows 11 146 38 73 84 288 68 128 256), losses := [] }

theorem u4294 : Upper (D 6) (R 6) [10,144,34,65,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4294 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4295 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 146 38 73 84 288 96 133 261), lower := (rows 11 146 38 73 84 288 96 128 256), losses := [] }

theorem u4295 : Upper (D 6) (R 6) [10,144,34,65,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4295 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4296 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 146 38 73 273 96 68 164 292), lower := (rows 11 146 38 73 273 96 68 128 256), losses := [] }

theorem u4296 : Upper (D 6) (R 6) [10,144,34,65,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4297 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 146 38 73 273 96 96 132 260), lower := (rows 11 146 38 73 273 96 96 128 256), losses := [] }

theorem u4297 : Upper (D 6) (R 6) [10,144,34,65,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4298 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 146 38 73 276 96 65 164 292), lower := (rows 11 146 38 73 276 96 65 128 256), losses := [] }

theorem u4298 : Upper (D 6) (R 6) [10,144,34,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4299 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 0, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 146 38 73 276 96 68 161 289), lower := (rows 11 146 38 73 276 96 68 128 256), losses := [] }

theorem u4299 : Upper (D 6) (R 6) [10,144,34,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4300 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,1),(3,2)], upper := (rows 11 146 38 73 276 96 96 133 261), lower := (rows 11 146 38 73 276 96 96 128 256), losses := [] }

theorem u4300 : Upper (D 6) (R 6) [10,144,34,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4301 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 146 38 73 336 36 65 164 292), lower := (rows 11 146 38 73 336 36 65 128 256), losses := [] }

theorem u4301 : Upper (D 6) (R 6) [10,144,34,65,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4302 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 0, region := 36, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 146 38 73 336 36 68 161 289), lower := (rows 11 146 38 73 336 36 68 128 256), losses := [] }

theorem u4302 : Upper (D 6) (R 6) [10,144,34,65,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 4 },{ cop := 0, region := 36, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 146 38 73 336 36 96 133 261), lower := (rows 11 146 38 73 336 36 96 128 256), losses := [] }

theorem u4303 : Upper (D 6) (R 6) [10,144,34,65,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4304 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 146 38 76 273 96 65 164 292), lower := (rows 11 146 38 76 273 96 65 128 256), losses := [{ target := 0, region := (rows 0 18 5 72 16 104 64 205 333), good := (rows 430 146 422 492 406 488 492 128 256) }] }

theorem u4304 : Upper (D 6) (R 6) [10,144,34,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4305 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 146 38 76 273 96 68 161 289), lower := (rows 11 146 38 76 273 96 68 128 256), losses := [] }

theorem u4305 : Upper (D 6) (R 6) [10,144,34,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4306 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 38 76 273 96 96 133 261), lower := (rows 11 146 38 76 273 96 96 128 256), losses := [] }

theorem u4306 : Upper (D 6) (R 6) [10,144,34,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4307 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 146 38 76 276 96 65 161 289), lower := (rows 11 146 38 76 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 72 16 104 64 128 256), good := (rows 46 146 38 108 276 104 108 128 256) }] }

theorem u4307 : Upper (D 6) (R 6) [10,144,34,68,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4308 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 403, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 38 76 276 96 96 129 257), lower := (rows 11 146 38 76 276 96 96 128 256), losses := [] }

theorem u4308 : Upper (D 6) (R 6) [10,144,34,68,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4309 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 146 38 76 336 33 65 164 292), lower := (rows 11 146 38 76 336 33 65 128 256), losses := [] }

theorem u4309 : Upper (D 6) (R 6) [10,144,34,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4310 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 146 38 76 336 33 68 161 289), lower := (rows 11 146 38 76 336 33 68 128 256), losses := [] }

theorem u4310 : Upper (D 6) (R 6) [10,144,34,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4311 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 38 76 336 33 96 133 261), lower := (rows 11 146 38 76 336 33 96 128 256), losses := [] }

theorem u4311 : Upper (D 6) (R 6) [10,144,34,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4312 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 146 38 104 84 288 65 133 261), lower := (rows 11 146 38 104 84 288 65 128 256), losses := [] }

theorem u4312 : Upper (D 6) (R 6) [10,144,34,96,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4312 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4313 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 146 38 104 84 288 68 129 257), lower := (rows 11 146 38 104 84 288 68 128 256), losses := [] }

theorem u4313 : Upper (D 6) (R 6) [10,144,34,96,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4313 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4314 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 104 273 36 65 196 324), lower := (rows 11 146 38 104 273 36 65 128 256), losses := [] }

theorem u4314 : Upper (D 6) (R 6) [10,144,34,96,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 403, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 146 38 104 273 36 68 193 321), lower := (rows 11 146 38 104 273 36 68 128 256), losses := [] }

theorem u4315 : Upper (D 6) (R 6) [10,144,34,96,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 104 276 33 65 196 324), lower := (rows 11 146 38 104 276 33 65 128 256), losses := [] }

theorem u4316 : Upper (D 6) (R 6) [10,144,34,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 146 38 104 276 33 68 193 321), lower := (rows 11 146 38 104 276 33 68 128 256), losses := [] }

theorem u4317 : Upper (D 6) (R 6) [10,144,34,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4318 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 104 336 33 65 132 260), lower := (rows 11 146 38 104 336 33 65 128 256), losses := [] }

theorem u4318 : Upper (D 6) (R 6) [10,144,34,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4319 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 146 38 104 336 33 68 133 261), lower := (rows 11 146 38 104 336 33 68 128 256), losses := [] }

theorem u4319 : Upper (D 6) (R 6) [10,144,34,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4319
end Delivery.IrregularNine14.P06
