import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4260 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 13 259 38 88 176 96 192 131 259), lower := (rows 13 259 38 88 176 96 192 128 256), losses := [] }

theorem u4260 : Upper (D 7) (R 7) [12,257,34,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4261 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 89, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(3,7),(4,7)], upper := (rows 13 259 38 104 82 160 65 144 400), lower := (rows 13 259 38 104 82 160 65 128 256), losses := [] }

theorem u4261 : Upper (D 7) (R 7) [12,257,34,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4262 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 89, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 13 259 38 104 82 160 80 129 385), lower := (rows 13 259 38 104 82 160 80 128 256), losses := [] }

theorem u4262 : Upper (D 7) (R 7) [12,257,34,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4262 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4263 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 259 38 104 82 160 192 145 273), lower := (rows 13 259 38 104 82 160 192 128 256), losses := [] }

theorem u4263 : Upper (D 7) (R 7) [12,257,34,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4264 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,7),(1,5),(3,7),(4,5)], upper := (rows 13 259 38 104 145 160 66 208 336), lower := (rows 13 259 38 104 145 160 66 128 256), losses := [] }

theorem u4264 : Upper (D 7) (R 7) [12,257,34,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4265 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 259 38 104 145 160 80 194 322), lower := (rows 13 259 38 104 145 160 80 128 256), losses := [] }

theorem u4265 : Upper (D 7) (R 7) [12,257,34,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4265 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4266 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 80, targets := 160 },{ cop := 4, region := 168, targets := 3 }], pairs := [(3,0),(3,1),(4,5),(4,7)], upper := (rows 13 259 38 200 81 160 66 176 304), lower := (rows 13 259 38 200 81 160 66 128 256), losses := [] }

theorem u4266 : Upper (D 7) (R 7) [12,257,34,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4267 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 13 259 38 200 81 160 80 162 290), lower := (rows 13 259 38 200 81 160 80 128 256), losses := [] }

theorem u4267 : Upper (D 7) (R 7) [12,257,34,192,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4267 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4268 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 394, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(3,5)], upper := (rows 13 259 38 200 81 160 96 146 274), lower := (rows 13 259 38 200 81 160 96 128 256), losses := [] }

theorem u4268 : Upper (D 7) (R 7) [12,257,34,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4269 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 80, targets := 160 },{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0),(3,0),(4,5),(4,7)], upper := (rows 13 259 38 200 82 160 65 176 304), lower := (rows 13 259 38 200 82 160 65 128 256), losses := [] }

theorem u4269 : Upper (D 7) (R 7) [12,257,34,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4270 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 13 259 38 200 82 160 80 161 289), lower := (rows 13 259 38 200 82 160 80 128 256), losses := [] }

theorem u4270 : Upper (D 7) (R 7) [12,257,34,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4270 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 129 },{ cop := 5, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,7)], upper := (rows 13 259 38 200 82 160 96 145 273), lower := (rows 13 259 38 200 82 160 96 128 256), losses := [] }

theorem u4271 : Upper (D 7) (R 7) [12,257,34,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(1,7),(2,7),(4,0),(4,1)], upper := (rows 13 259 38 200 112 160 65 146 274), lower := (rows 13 259 38 200 112 160 65 128 256), losses := [{ target := 7, region := (rows 1 67 20 8 20 32 67 0 277), good := (rows 351 323 374 74 374 32 323 0 256) }] }

theorem u4272 : Upper (D 7) (R 7) [12,257,34,192,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4273 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 129 },{ cop := 3, region := 48, targets := 2 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 13 259 38 200 112 160 66 145 273), lower := (rows 13 259 38 200 112 160 66 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 20 32 71 0 257), good := (rows 351 323 118 72 112 32 66 0 256) }] }

theorem u4273 : Upper (D 7) (R 7) [12,257,34,192,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4274 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 13 259 38 200 112 160 80 131 259), lower := (rows 13 259 38 200 112 160 80 128 256), losses := [] }

theorem u4274 : Upper (D 7) (R 7) [12,257,34,192,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4274 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4275 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 149, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 13 259 52 104 145 34 66 192 448), lower := (rows 13 259 52 104 145 34 66 128 256), losses := [] }

theorem u4275 : Upper (D 7) (R 7) [12,257,48,96,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4276 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,1),(1,5),(3,0),(4,5)], upper := (rows 13 259 52 104 145 34 192 194 322), lower := (rows 13 259 52 104 145 34 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 32 208 128 256), good := (rows 13 257 125 104 209 32 192 192 256) }] }

theorem u4276 : Upper (D 7) (R 7) [12,257,48,96,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 259 52 104 208 34 65 130 386), lower := (rows 13 259 52 104 208 34 65 128 256), losses := [] }

theorem u4277 : Upper (D 7) (R 7) [12,257,48,96,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 2 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 13 259 52 104 208 34 66 129 385), lower := (rows 13 259 52 104 208 34 66 128 256), losses := [] }

theorem u4278 : Upper (D 7) (R 7) [12,257,48,96,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 52 104 208 34 192 131 259), lower := (rows 13 259 52 104 208 34 192 128 256), losses := [] }

theorem u4279 : Upper (D 7) (R 7) [12,257,48,96,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 116, targets := 128 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(2,7),(4,7)], upper := (rows 13 259 52 200 81 34 66 160 416), lower := (rows 13 259 52 200 81 34 66 128 256), losses := [] }

theorem u4280 : Upper (D 7) (R 7) [12,257,48,192,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 116, targets := 128 },{ cop := 4, region := 394, targets := 32 }], pairs := [(1,5),(2,7),(3,5),(4,7)], upper := (rows 13 259 52 200 81 34 96 130 386), lower := (rows 13 259 52 200 81 34 96 128 256), losses := [] }

theorem u4281 : Upper (D 7) (R 7) [12,257,48,192,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 259 52 200 81 34 192 162 290), lower := (rows 13 259 52 200 81 34 192 128 256), losses := [] }

theorem u4282 : Upper (D 7) (R 7) [12,257,48,192,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 80, targets := 160 },{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0),(3,0),(4,5),(4,7)], upper := (rows 13 259 52 200 82 160 65 162 290), lower := (rows 13 259 52 200 82 160 65 128 256), losses := [] }

theorem u4283 : Upper (D 7) (R 7) [12,257,48,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 13 259 52 200 82 160 66 161 289), lower := (rows 13 259 52 200 82 160 66 128 256), losses := [] }

theorem u4284 : Upper (D 7) (R 7) [12,257,48,192,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 72, targets := 3 },{ cop := 0, region := 258, targets := 32 },{ cop := 0, region := 258, targets := 64 }], pairs := [(1,5),(1,6),(3,0),(3,1)], upper := (rows 13 259 52 200 82 160 96 131 259), lower := (rows 13 259 52 200 82 160 96 128 256), losses := [] }

theorem u4285 : Upper (D 7) (R 7) [12,257,48,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4286 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 13 259 100 168 208 34 65 146 274), lower := (rows 13 259 100 168 208 34 65 128 256), losses := [] }

theorem u4286 : Upper (D 7) (R 7) [12,257,96,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4287 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(3,1),(4,1)], upper := (rows 13 259 100 168 208 34 66 145 273), lower := (rows 13 259 100 168 208 34 66 128 256), losses := [] }

theorem u4287 : Upper (D 7) (R 7) [12,257,96,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4288 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 259 100 168 208 34 80 131 259), lower := (rows 13 259 100 168 208 34 80 128 256), losses := [] }

theorem u4288 : Upper (D 7) (R 7) [12,257,96,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4288 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4289 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 386, targets := 32 },{ cop := 6, region := 176, targets := 2 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 13 274 7 41 112 160 66 192 448), lower := (rows 13 274 7 41 112 160 66 128 256), losses := [] }

theorem u4289 : Upper (D 7) (R 7) [12,272,3,33,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4290 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 7 41 112 160 192 194 322), lower := (rows 13 274 7 41 112 160 192 128 256), losses := [] }

theorem u4290 : Upper (D 7) (R 7) [12,272,3,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4291 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 274 7 104 50 160 65 192 448), lower := (rows 13 274 7 104 50 160 65 128 256), losses := [] }

theorem u4291 : Upper (D 7) (R 7) [12,272,3,96,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4292 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 7 104 50 160 192 193 321), lower := (rows 13 274 7 104 50 160 192 128 256), losses := [] }

theorem u4292 : Upper (D 7) (R 7) [12,272,3,96,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 5, region := 200, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,1)], upper := (rows 13 274 7 104 145 34 192 224 352), lower := (rows 13 274 7 104 145 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 40 17 32 249 168 296), good := (rows 477 336 85 488 209 488 192 192 256) }] }

theorem u4293 : Upper (D 7) (R 7) [12,272,3,96,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4294 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 7 104 145 96 192 162 290), lower := (rows 13 274 7 104 145 96 192 128 256), losses := [] }

theorem u4294 : Upper (D 7) (R 7) [12,272,3,96,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4295 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 274 7 104 146 33 192 224 352), lower := (rows 13 274 7 104 146 33 192 128 256), losses := [] }

theorem u4295 : Upper (D 7) (R 7) [12,272,3,96,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4296 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 7 104 146 96 192 161 289), lower := (rows 13 274 7 104 146 96 192 128 256), losses := [] }

theorem u4296 : Upper (D 7) (R 7) [12,272,3,96,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4297 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 109, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 274 7 104 176 34 65 192 448), lower := (rows 13 274 7 104 176 34 65 128 256), losses := [] }

theorem u4297 : Upper (D 7) (R 7) [12,272,3,96,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4298 : Route 9 := (fun mask => (mask,id))

def c4298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4298 : Upper (D 7) (R 7) [12,272,3,96,160,2,128] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,160,2,128] 13 (by decide) (choices 1) [1,64] r4298 c4298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u336
  · exact u337

def b4299 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 6, region := 173, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 13 274 37 73 50 160 66 192 448), lower := (rows 13 274 37 73 50 160 66 128 256), losses := [] }

theorem u4299 : Upper (D 7) (R 7) [12,272,33,65,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4300 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 77, targets := 2 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 274 37 73 50 160 192 194 322), lower := (rows 13 274 37 73 50 160 192 128 256), losses := [] }

theorem u4300 : Upper (D 7) (R 7) [12,272,33,65,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4301 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 274 37 73 146 34 192 224 352), lower := (rows 13 274 37 73 146 34 192 128 256), losses := [] }

theorem u4301 : Upper (D 7) (R 7) [12,272,33,65,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4302 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 73 146 96 192 162 290), lower := (rows 13 274 37 73 146 96 192 128 256), losses := [] }

theorem u4302 : Upper (D 7) (R 7) [12,272,33,65,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 274 37 74 50 160 65 192 448), lower := (rows 13 274 37 74 50 160 65 128 256), losses := [] }

theorem u4303 : Upper (D 7) (R 7) [12,272,33,66,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4304 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 13 274 37 74 50 160 192 193 321), lower := (rows 13 274 37 74 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 224 224 128 256), good := (rows 28 282 100 122 122 224 224 224 256) }] }

theorem u4304 : Upper (D 7) (R 7) [12,272,33,66,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4305 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 274 37 74 112 160 65 130 386), lower := (rows 13 274 37 74 112 160 65 128 256), losses := [] }

theorem u4305 : Upper (D 7) (R 7) [12,272,33,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4306 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 161 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 13 274 37 74 112 160 66 129 385), lower := (rows 13 274 37 74 112 160 66 128 256), losses := [] }

theorem u4306 : Upper (D 7) (R 7) [12,272,33,66,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4307 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 37 74 112 160 192 131 259), lower := (rows 13 274 37 74 112 160 192 128 256), losses := [] }

theorem u4307 : Upper (D 7) (R 7) [12,272,33,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4308 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 274 37 74 146 160 65 224 352), lower := (rows 13 274 37 74 146 160 65 128 256), losses := [] }

theorem u4308 : Upper (D 7) (R 7) [12,272,33,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4309 : Route 9 := (fun mask => (mask,id))

def c4309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4309 : Upper (D 7) (R 7) [12,272,33,66,130,128,32] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,130,128,32] 13 (by decide) (choices 1) [1,64] r4309 c4309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u338
  · exact u339

def b4310 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 13 274 37 74 208 160 65 162 290), lower := (rows 13 274 37 74 208 160 65 128 256), losses := [] }

theorem u4310 : Upper (D 7) (R 7) [12,272,33,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4311 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 72, targets := 161 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 13 274 37 74 208 160 66 161 289), lower := (rows 13 274 37 74 208 160 66 128 256), losses := [] }

theorem u4311 : Upper (D 7) (R 7) [12,272,33,66,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4312 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 13 274 37 74 208 160 96 131 259), lower := (rows 13 274 37 74 208 160 96 128 256), losses := [] }

theorem u4312 : Upper (D 7) (R 7) [12,272,33,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4313 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 274 37 200 82 34 65 160 416), lower := (rows 13 274 37 200 82 34 65 128 256), losses := [] }

theorem u4313 : Upper (D 7) (R 7) [12,272,33,192,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4314 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 274 37 200 82 34 96 129 385), lower := (rows 13 274 37 200 82 34 96 128 256), losses := [] }

theorem u4314 : Upper (D 7) (R 7) [12,272,33,192,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 37 200 82 34 192 161 289), lower := (rows 13 274 37 200 82 34 192 128 256), losses := [] }

theorem u4315 : Upper (D 7) (R 7) [12,272,33,192,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 274 37 200 112 34 65 130 386), lower := (rows 13 274 37 200 112 34 65 128 256), losses := [] }

theorem u4316 : Upper (D 7) (R 7) [12,272,33,192,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 274 37 200 112 34 66 129 385), lower := (rows 13 274 37 200 112 34 66 128 256), losses := [] }

theorem u4317 : Upper (D 7) (R 7) [12,272,33,192,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4318 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 37 200 112 34 192 131 259), lower := (rows 13 274 37 200 112 34 192 128 256), losses := [] }

theorem u4318 : Upper (D 7) (R 7) [12,272,33,192,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4319 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 274 38 104 208 33 65 130 386), lower := (rows 13 274 38 104 208 33 65 128 256), losses := [] }

theorem u4319 : Upper (D 7) (R 7) [12,272,34,96,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4319
end Delivery.IrregularNine14.P07
