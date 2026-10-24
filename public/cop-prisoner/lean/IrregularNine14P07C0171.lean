import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10260 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 3, region := 133, targets := 64 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 134 42 81 48 192 137 265), lower := (rows 37 322 134 42 81 48 192 128 256), losses := [] }

theorem u10260 : Upper (D 7) (R 7) [36,320,130,34,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10260 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10261 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 121, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 37 322 134 56 208 33 65 138 266), lower := (rows 37 322 134 56 208 33 65 128 256), losses := [] }

theorem u10261 : Upper (D 7) (R 7) [36,320,130,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10262 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 322 134 56 208 33 66 137 265), lower := (rows 37 322 134 56 208 33 66 128 256), losses := [] }

theorem u10262 : Upper (D 7) (R 7) [36,320,130,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10263 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 56 208 33 72 131 259), lower := (rows 37 322 134 56 208 33 72 128 256), losses := [] }

theorem u10263 : Upper (D 7) (R 7) [36,320,130,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10263 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10264 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 134 73 145 40 66 176 304), lower := (rows 37 322 134 73 145 40 66 128 256), losses := [] }

theorem u10264 : Upper (D 7) (R 7) [36,320,130,65,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10264 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10265 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 37 322 134 73 145 40 80 162 290), lower := (rows 37 322 134 73 145 40 80 128 256), losses := [] }

theorem u10265 : Upper (D 7) (R 7) [36,320,130,65,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10265 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10266 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 73 145 40 96 146 274), lower := (rows 37 322 134 73 145 40 96 128 256), losses := [] }

theorem u10266 : Upper (D 7) (R 7) [36,320,130,65,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10266 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10267 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 73 152 48 65 162 290), lower := (rows 37 322 134 73 152 48 65 128 256), losses := [] }

theorem u10267 : Upper (D 7) (R 7) [36,320,130,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10267 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10268 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 134 73 152 48 66 161 289), lower := (rows 37 322 134 73 152 48 66 128 256), losses := [] }

theorem u10268 : Upper (D 7) (R 7) [36,320,130,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10268 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10269 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 73 152 48 96 131 259), lower := (rows 37 322 134 73 152 48 96 128 256), losses := [] }

theorem u10269 : Upper (D 7) (R 7) [36,320,130,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10269 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10270 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 73 176 40 65 146 274), lower := (rows 37 322 134 73 176 40 65 128 256), losses := [] }

theorem u10270 : Upper (D 7) (R 7) [36,320,130,65,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10270 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10271 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 134 73 176 40 66 145 273), lower := (rows 37 322 134 73 176 40 66 128 256), losses := [] }

theorem u10271 : Upper (D 7) (R 7) [36,320,130,65,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10271 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10272 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 37 322 134 73 176 40 80 131 259), lower := (rows 37 322 134 73 176 40 80 128 256), losses := [] }

theorem u10272 : Upper (D 7) (R 7) [36,320,130,65,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10272 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10273 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 88 145 40 65 162 290), lower := (rows 37 322 134 88 145 40 65 128 256), losses := [] }

theorem u10273 : Upper (D 7) (R 7) [36,320,130,80,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10273 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10274 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 134 88 145 40 66 161 289), lower := (rows 37 322 134 88 145 40 66 128 256), losses := [] }

theorem u10274 : Upper (D 7) (R 7) [36,320,130,80,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10274 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10275 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 88 145 40 96 131 259), lower := (rows 37 322 134 88 145 40 96 128 256), losses := [] }

theorem u10275 : Upper (D 7) (R 7) [36,320,130,80,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10275 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10276 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 134 104 152 33 65 146 274), lower := (rows 37 322 134 104 152 33 65 128 256), losses := [] }

theorem u10276 : Upper (D 7) (R 7) [36,320,130,96,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10277 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 322 134 104 152 33 66 145 273), lower := (rows 37 322 134 104 152 33 66 128 256), losses := [] }

theorem u10277 : Upper (D 7) (R 7) [36,320,130,96,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10278 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 121, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 322 134 104 152 33 80 131 259), lower := (rows 37 322 134 104 152 33 80 128 256), losses := [] }

theorem u10278 : Upper (D 7) (R 7) [36,320,130,96,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10278 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10279 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 140 11 81 48 66 160 416), lower := (rows 37 322 140 11 81 48 66 128 256), losses := [] }

theorem u10279 : Upper (D 7) (R 7) [36,320,136,3,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10279 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10280 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 322 140 11 81 48 96 130 386), lower := (rows 37 322 140 11 81 48 96 128 256), losses := [] }

theorem u10280 : Upper (D 7) (R 7) [36,320,136,3,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10280 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10281 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 290, targets := 128 }], pairs := [(0,1),(1,7),(4,1)], upper := (rows 37 322 140 11 81 48 192 162 290), lower := (rows 37 322 140 11 81 48 192 128 256), losses := [] }

theorem u10281 : Upper (D 7) (R 7) [36,320,136,3,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10281 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10282 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 322 140 11 145 96 66 176 304), lower := (rows 37 322 140 11 145 96 66 128 256), losses := [] }

theorem u10282 : Upper (D 7) (R 7) [36,320,136,3,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10283 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,1),(1,7),(4,1)], upper := (rows 37 322 140 11 145 96 80 162 290), lower := (rows 37 322 140 11 145 96 80 128 256), losses := [] }

theorem u10283 : Upper (D 7) (R 7) [36,320,136,3,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10283 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10284 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 37 322 140 11 145 96 96 146 274), lower := (rows 37 322 140 11 145 96 96 128 256), losses := [] }

theorem u10284 : Upper (D 7) (R 7) [36,320,136,3,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10285 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 402, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 322 140 11 146 96 65 176 304), lower := (rows 37 322 140 11 146 96 65 128 256), losses := [] }

theorem u10285 : Upper (D 7) (R 7) [36,320,136,3,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10286 : PairBound 9 := { available := 33, camps := [], pairs := [(0,1),(2,1),(2,6)], upper := (rows 37 322 140 11 146 96 80 161 289), lower := (rows 37 322 140 11 146 96 80 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 114 80 137 265), good := (rows 421 352 397 429 240 96 112 128 256) },{ target := 6, region := (rows 1 2 12 8 24 32 0 129 257), good := (rows 421 258 156 415 146 32 16 128 256) }] }

theorem u10286 : Upper (D 7) (R 7) [36,320,136,3,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10286 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10287 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 37 322 140 11 146 96 96 145 273), lower := (rows 37 322 140 11 146 96 96 128 256), losses := [] }

theorem u10287 : Upper (D 7) (R 7) [36,320,136,3,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10288 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 5, region := 402, targets := 1 }], pairs := [(0,1),(1,0),(4,0),(4,1)], upper := (rows 37 322 140 11 176 96 65 146 274), lower := (rows 37 322 140 11 176 96 65 128 256), losses := [] }

theorem u10288 : Upper (D 7) (R 7) [36,320,136,3,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10289 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 8, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 37 322 140 11 176 96 66 145 273), lower := (rows 37 322 140 11 176 96 66 128 256), losses := [] }

theorem u10289 : Upper (D 7) (R 7) [36,320,136,3,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10290 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 3, region := 132, targets := 32 }], pairs := [(0,1),(2,5),(4,1)], upper := (rows 37 322 140 11 176 96 80 131 259), lower := (rows 37 322 140 11 176 96 80 128 256), losses := [] }

theorem u10290 : Upper (D 7) (R 7) [36,320,136,3,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10290 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10291 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 113, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 322 140 11 208 48 65 162 290), lower := (rows 37 322 140 11 208 48 65 128 256), losses := [] }

theorem u10291 : Upper (D 7) (R 7) [36,320,136,3,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10291 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10292 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 140 11 208 48 66 161 289), lower := (rows 37 322 140 11 208 48 66 128 256), losses := [] }

theorem u10292 : Upper (D 7) (R 7) [36,320,136,3,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10293 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 113, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 322 140 11 208 48 96 131 259), lower := (rows 37 322 140 11 208 48 96 128 256), losses := [] }

theorem u10293 : Upper (D 7) (R 7) [36,320,136,3,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10293 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10294 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 322 140 25 208 34 65 162 290), lower := (rows 37 322 140 25 208 34 65 128 256), losses := [] }

theorem u10294 : Upper (D 7) (R 7) [36,320,136,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10295 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 8, region := 66, targets := 1 },{ cop := 8, region := 66, targets := 32 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 37 322 140 25 208 34 66 161 289), lower := (rows 37 322 140 25 208 34 66 128 256), losses := [] }

theorem u10295 : Upper (D 7) (R 7) [36,320,136,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10296 : Route 9 := (fun mask => (mask,id))

def c10296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10296 : Upper (D 7) (R 7) [36,320,136,17,192,2,32] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17,192,2,32] 13 (by decide) (choices 1) [1,2] r10296 c10296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u781
  · exact u782

def b10297 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 37 322 140 26 145 96 65 162 290), lower := (rows 37 322 140 26 145 96 65 128 256), losses := [] }

theorem u10297 : Upper (D 7) (R 7) [36,320,136,18,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10298 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,6)], upper := (rows 37 322 140 26 145 96 66 161 289), lower := (rows 37 322 140 26 145 96 66 128 256), losses := [] }

theorem u10298 : Upper (D 7) (R 7) [36,320,136,18,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10299 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 37 322 140 26 145 96 96 131 259), lower := (rows 37 322 140 26 145 96 96 128 256), losses := [] }

theorem u10299 : Upper (D 7) (R 7) [36,320,136,18,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10300 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 37 322 140 26 176 96 65 131 259), lower := (rows 37 322 140 26 176 96 65 128 256), losses := [] }

theorem u10300 : Upper (D 7) (R 7) [36,320,136,18,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10301 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,6)], upper := (rows 37 322 140 26 176 96 66 129 257), lower := (rows 37 322 140 26 176 96 66 128 256), losses := [] }

theorem u10301 : Upper (D 7) (R 7) [36,320,136,18,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10302 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 322 140 56 81 34 65 130 386), lower := (rows 37 322 140 56 81 34 65 128 256), losses := [] }

theorem u10302 : Upper (D 7) (R 7) [36,320,136,48,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10303 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 140 56 81 34 66 129 385), lower := (rows 37 322 140 56 81 34 66 128 256), losses := [] }

theorem u10303 : Upper (D 7) (R 7) [36,320,136,48,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10304 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 298, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 140 56 81 34 192 131 259), lower := (rows 37 322 140 56 81 34 192 128 256), losses := [] }

theorem u10304 : Upper (D 7) (R 7) [36,320,136,48,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10305 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 37 322 140 73 19 34 80 160 416), lower := (rows 37 322 140 73 19 34 80 128 256), losses := [] }

theorem u10305 : Upper (D 7) (R 7) [36,320,136,65,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10305 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10306 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 140 73 19 34 96 144 400), lower := (rows 37 322 140 73 19 34 96 128 256), losses := [] }

theorem u10306 : Upper (D 7) (R 7) [36,320,136,65,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10307 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 306, targets := 128 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(1,7),(3,1),(4,7)], upper := (rows 37 322 140 73 19 34 192 176 304), lower := (rows 37 322 140 73 19 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 32 196 128 256), good := (rows 109 320 204 73 25 32 192 192 256) }] }

theorem u10307 : Upper (D 7) (R 7) [36,320,136,65,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10308 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 140 73 19 48 66 160 416), lower := (rows 37 322 140 73 19 48 66 128 256), losses := [] }

theorem u10308 : Upper (D 7) (R 7) [36,320,136,65,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10308 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10309 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 140 73 19 48 96 130 386), lower := (rows 37 322 140 73 19 48 96 128 256), losses := [] }

theorem u10309 : Upper (D 7) (R 7) [36,320,136,65,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10309 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10310 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 306, targets := 128 },{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 322 140 73 19 48 192 162 290), lower := (rows 37 322 140 73 19 48 192 128 256), losses := [] }

theorem u10310 : Upper (D 7) (R 7) [36,320,136,65,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10310 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10311 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 322 140 73 145 34 66 176 304), lower := (rows 37 322 140 73 145 34 66 128 256), losses := [] }

theorem u10311 : Upper (D 7) (R 7) [36,320,136,65,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10312 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 322 140 73 145 34 80 162 290), lower := (rows 37 322 140 73 145 34 80 128 256), losses := [] }

theorem u10312 : Upper (D 7) (R 7) [36,320,136,65,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10312 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10313 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 140 73 145 34 96 146 274), lower := (rows 37 322 140 73 145 34 96 128 256), losses := [] }

theorem u10313 : Upper (D 7) (R 7) [36,320,136,65,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10314 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 322 140 73 146 34 65 176 304), lower := (rows 37 322 140 73 146 34 65 128 256), losses := [] }

theorem u10314 : Upper (D 7) (R 7) [36,320,136,65,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10315 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 290, targets := 128 }], pairs := [(1,7),(2,1),(2,6)], upper := (rows 37 322 140 73 146 34 80 161 289), lower := (rows 37 322 140 73 146 34 80 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 32 80 129 257), good := (rows 421 320 140 461 208 32 80 128 256) },{ target := 6, region := (rows 1 2 12 8 16 50 0 129 257), good := (rows 421 290 140 397 178 34 48 128 256) }] }

theorem u10315 : Upper (D 7) (R 7) [36,320,136,65,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10315 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10316 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 140 73 146 34 96 145 273), lower := (rows 37 322 140 73 146 34 96 128 256), losses := [] }

theorem u10316 : Upper (D 7) (R 7) [36,320,136,65,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10317 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 322 140 73 146 48 65 162 290), lower := (rows 37 322 140 73 146 48 65 128 256), losses := [] }

theorem u10317 : Upper (D 7) (R 7) [36,320,136,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10317 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10318 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 140 73 146 48 66 161 289), lower := (rows 37 322 140 73 146 48 66 128 256), losses := [] }

theorem u10318 : Upper (D 7) (R 7) [36,320,136,65,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10318 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10319 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 140 73 146 48 96 131 259), lower := (rows 37 322 140 73 146 48 96 128 256), losses := [] }

theorem u10319 : Upper (D 7) (R 7) [36,320,136,65,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10319 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10319
end Delivery.IrregularNine14.P07
