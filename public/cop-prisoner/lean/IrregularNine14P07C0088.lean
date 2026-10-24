import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 104 152 288 80 131 259), lower := (rows 35 70 133 104 152 288 80 128 256), losses := [] }

theorem u5280 : Upper (D 7) (R 7) [34,68,129,96,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5280 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5281 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 104 273 48 66 136 392), lower := (rows 35 70 133 104 273 48 66 128 256), losses := [] }

theorem u5281 : Upper (D 7) (R 7) [34,68,129,96,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5281 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5282 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 104 273 48 72 130 386), lower := (rows 35 70 133 104 273 48 72 128 256), losses := [] }

theorem u5282 : Upper (D 7) (R 7) [34,68,129,96,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5282 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5283 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 104 273 48 192 138 266), lower := (rows 35 70 133 104 273 48 192 128 256), losses := [] }

theorem u5283 : Upper (D 7) (R 7) [34,68,129,96,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5283 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5284 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 133 104 400 48 65 138 266), lower := (rows 35 70 133 104 400 48 65 128 256), losses := [] }

theorem u5284 : Upper (D 7) (R 7) [34,68,129,96,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5284 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5285 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 104 400 48 66 137 265), lower := (rows 35 70 133 104 400 48 66 128 256), losses := [] }

theorem u5285 : Upper (D 7) (R 7) [34,68,129,96,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5285 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5286 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 104 400 48 72 131 259), lower := (rows 35 70 133 104 400 48 72 128 256), losses := [] }

theorem u5286 : Upper (D 7) (R 7) [34,68,129,96,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5286 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5287 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 168 273 48 66 200 328), lower := (rows 35 70 133 168 273 48 66 128 256), losses := [] }

theorem u5287 : Upper (D 7) (R 7) [34,68,129,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5287 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5288 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 35 70 133 168 273 48 72 194 322), lower := (rows 35 70 133 168 273 48 72 128 256), losses := [] }

theorem u5288 : Upper (D 7) (R 7) [34,68,129,160,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5288 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5289 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 440, targets := 1 }], pairs := [(2,6),(3,0),(3,6)], upper := (rows 35 70 133 168 336 48 65 138 266), lower := (rows 35 70 133 168 336 48 65 128 256), losses := [] }

theorem u5289 : Upper (D 7) (R 7) [34,68,129,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5289 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 140, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 70 133 168 336 48 66 137 265), lower := (rows 35 70 133 168 336 48 66 128 256), losses := [] }

theorem u5290 : Upper (D 7) (R 7) [34,68,129,160,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5290 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5291 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 168 336 48 72 131 259), lower := (rows 35 70 133 168 336 48 72 128 256), losses := [] }

theorem u5291 : Upper (D 7) (R 7) [34,68,129,160,320,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5291 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5292 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 133 200 273 48 66 168 296), lower := (rows 35 70 133 200 273 48 66 128 256), losses := [] }

theorem u5292 : Upper (D 7) (R 7) [34,68,129,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5293 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 200 273 48 72 162 290), lower := (rows 35 70 133 200 273 48 72 128 256), losses := [] }

theorem u5293 : Upper (D 7) (R 7) [34,68,129,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5293 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5294 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 136, targets := 33 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 133 200 273 48 96 138 266), lower := (rows 35 70 133 200 273 48 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 31 16 48 113 135 263), good := (rows 490 462 462 200 504 120 96 128 256) }] }

theorem u5294 : Upper (D 7) (R 7) [34,68,129,192,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5294 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5295 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 133 200 280 48 65 162 290), lower := (rows 35 70 133 200 280 48 65 128 256), losses := [] }

theorem u5295 : Upper (D 7) (R 7) [34,68,129,192,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5295 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5296 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 133 200 280 48 66 161 289), lower := (rows 35 70 133 200 280 48 66 128 256), losses := [] }

theorem u5296 : Upper (D 7) (R 7) [34,68,129,192,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5296 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5297 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 132, targets := 96 }], pairs := [(1,0),(2,5),(2,6)], upper := (rows 35 70 133 200 280 48 96 131 259), lower := (rows 35 70 133 200 280 48 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 48 113 128 256), good := (rows 98 78 206 200 376 112 96 128 256) }] }

theorem u5297 : Upper (D 7) (R 7) [34,68,129,192,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5297 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5298 : Route 9 := (fun mask => (mask,id))

def c5298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5298 : Upper (D 7) (R 7) [34,68,130,17,384,8,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,384,8,1] 13 (by decide) (choices 1) [32,64] r5298 c5298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u396
  · exact u397

def r5299 : Route 9 := (fun mask => (mask,id))

def c5299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5299 : Upper (D 7) (R 7) [34,68,130,17,384,8,32] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,384,8,32] 13 (by decide) (choices 1) [1,64] r5299 c5299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u398
  · exact u399

def r5300 : Route 9 := (fun mask => (mask,id))

def c5300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5300 : Upper (D 7) (R 7) [34,68,130,80,160,256,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,160,256,1] 13 (by decide) (choices 1) [1,8] r5300 c5300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u400
  · exact u401

def b5301 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 88 176 288 72 129 257), lower := (rows 35 70 134 88 176 288 72 128 256), losses := [] }

theorem u5301 : Upper (D 7) (R 7) [34,68,130,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5301 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5302 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 72, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 152 288 65 145 273), lower := (rows 35 70 134 104 152 288 65 128 256), losses := [] }

theorem u5302 : Upper (D 7) (R 7) [34,68,130,96,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5302 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5303 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 104 152 288 80 129 257), lower := (rows 35 70 134 104 152 288 80 128 256), losses := [] }

theorem u5303 : Upper (D 7) (R 7) [34,68,130,96,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5303 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5304 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 104 273 48 65 136 392), lower := (rows 35 70 134 104 273 48 65 128 256), losses := [] }

theorem u5304 : Upper (D 7) (R 7) [34,68,130,96,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5305 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 134 104 273 48 72 129 385), lower := (rows 35 70 134 104 273 48 72 128 256), losses := [] }

theorem u5305 : Upper (D 7) (R 7) [34,68,130,96,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5305 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 104 273 48 192 137 265), lower := (rows 35 70 134 104 273 48 192 128 256), losses := [] }

theorem u5306 : Upper (D 7) (R 7) [34,68,130,96,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5306 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5307 : Route 9 := (fun mask => (mask,id))

def c5307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5307 : Upper (D 7) (R 7) [34,68,130,160,257,16,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,160,257,16,1] 13 (by decide) (choices 1) [8,64] r5307 c5307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u402
  · exact u403

def b5308 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 168 273 48 72 193 321), lower := (rows 35 70 134 168 273 48 72 128 256), losses := [] }

theorem u5308 : Upper (D 7) (R 7) [34,68,130,160,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5308 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5309 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 400, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 35 70 140 56 336 33 65 130 386), lower := (rows 35 70 140 56 336 33 65 128 256), losses := [] }

theorem u5309 : Upper (D 7) (R 7) [34,68,136,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5310 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 70 140 56 336 33 66 129 385), lower := (rows 35 70 140 56 336 33 66 128 256), losses := [] }

theorem u5310 : Upper (D 7) (R 7) [34,68,136,48,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5311 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 140 56 336 33 192 131 259), lower := (rows 35 70 140 56 336 33 192 128 256), losses := [] }

theorem u5311 : Upper (D 7) (R 7) [34,68,136,48,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5312 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 88 304 33 65 130 386), lower := (rows 35 70 140 88 304 33 65 128 256), losses := [] }

theorem u5312 : Upper (D 7) (R 7) [34,68,136,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 70 140 88 304 33 66 129 385), lower := (rows 35 70 140 88 304 33 66 128 256), losses := [] }

theorem u5313 : Upper (D 7) (R 7) [34,68,136,80,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5314 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,7)], upper := (rows 35 70 140 88 304 33 192 131 259), lower := (rows 35 70 140 88 304 33 192 128 256), losses := [] }

theorem u5314 : Upper (D 7) (R 7) [34,68,136,80,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5315 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 70 140 265 81 160 66 176 304), lower := (rows 35 70 140 265 81 160 66 128 256), losses := [] }

theorem u5315 : Upper (D 7) (R 7) [34,68,136,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 140 265 81 160 80 162 290), lower := (rows 35 70 140 265 81 160 80 128 256), losses := [] }

theorem u5316 : Upper (D 7) (R 7) [34,68,136,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5316 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5317 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 344, targets := 128 }], pairs := [(1,5),(2,5),(3,5),(3,7)], upper := (rows 35 70 140 265 81 160 96 146 274), lower := (rows 35 70 140 265 81 160 96 128 256), losses := [] }

theorem u5317 : Upper (D 7) (R 7) [34,68,136,257,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5318 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 140 266 208 33 65 176 304), lower := (rows 35 70 140 266 208 33 65 128 256), losses := [] }

theorem u5318 : Upper (D 7) (R 7) [34,68,136,258,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 140 266 208 33 80 161 289), lower := (rows 35 70 140 266 208 33 80 128 256), losses := [] }

theorem u5319 : Upper (D 7) (R 7) [34,68,136,258,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5319 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 140 266 208 33 96 145 273), lower := (rows 35 70 140 266 208 33 96 128 256), losses := [] }

theorem u5320 : Upper (D 7) (R 7) [34,68,136,258,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 280 112 33 65 130 386), lower := (rows 35 70 140 280 112 33 65 128 256), losses := [] }

theorem u5321 : Upper (D 7) (R 7) [34,68,136,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 35 70 140 280 112 33 66 129 385), lower := (rows 35 70 140 280 112 33 66 128 256), losses := [] }

theorem u5322 : Upper (D 7) (R 7) [34,68,136,272,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 140 280 112 33 192 131 259), lower := (rows 35 70 140 280 112 33 192 128 256), losses := [] }

theorem u5323 : Upper (D 7) (R 7) [34,68,136,272,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5324 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 140 280 176 33 65 194 322), lower := (rows 35 70 140 280 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 71 73 17 32 64 194 322), good := (rows 446 462 140 280 176 60 478 128 256) }] }

theorem u5324 : Upper (D 7) (R 7) [34,68,136,272,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5325 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 70 140 280 176 33 66 193 321), lower := (rows 35 70 140 280 176 33 66 128 256), losses := [] }

theorem u5325 : Upper (D 7) (R 7) [34,68,136,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5326 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 140 280 208 33 65 162 290), lower := (rows 35 70 140 280 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 84 72 80 32 64 129 257), good := (rows 418 94 140 286 222 416 478 128 256) }] }

theorem u5326 : Upper (D 7) (R 7) [34,68,136,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 140 280 208 33 66 161 289), lower := (rows 35 70 140 280 208 33 66 128 256), losses := [] }

theorem u5327 : Upper (D 7) (R 7) [34,68,136,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5328 : Route 9 := (fun mask => (mask,id))

def c5328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5328 : Upper (D 7) (R 7) [34,68,136,272,192,1,32] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,192,1,32] 13 (by decide) (choices 1) [1,2] r5328 c5328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u404
  · exact u405

def b5329 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,0),(3,7),(4,5)], upper := (rows 35 70 140 296 145 48 65 194 322), lower := (rows 35 70 140 296 145 48 65 128 256), losses := [{ target := 0, region := (rows 0 66 85 9 16 48 64 194 322), good := (rows 430 454 140 296 188 52 462 128 256) }] }

theorem u5329 : Upper (D 7) (R 7) [34,68,136,288,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5329 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5330 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 140 296 145 48 66 193 321), lower := (rows 35 70 140 296 145 48 66 128 256), losses := [] }

theorem u5330 : Upper (D 7) (R 7) [34,68,136,288,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5330 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5331 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 35 70 140 296 208 33 65 146 274), lower := (rows 35 70 140 296 208 33 65 128 256), losses := [] }

theorem u5331 : Upper (D 7) (R 7) [34,68,136,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 140 296 208 33 66 145 273), lower := (rows 35 70 140 296 208 33 66 128 256), losses := [] }

theorem u5332 : Upper (D 7) (R 7) [34,68,136,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5333 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 140 296 208 33 80 131 259), lower := (rows 35 70 140 296 208 33 80 128 256), losses := [] }

theorem u5333 : Upper (D 7) (R 7) [34,68,136,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5333 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5334 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 70 140 328 145 33 66 176 304), lower := (rows 35 70 140 328 145 33 66 128 256), losses := [] }

theorem u5334 : Upper (D 7) (R 7) [34,68,136,320,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5335 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 70 140 328 145 33 80 162 290), lower := (rows 35 70 140 328 145 33 80 128 256), losses := [] }

theorem u5335 : Upper (D 7) (R 7) [34,68,136,320,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5335 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5336 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 140 328 145 33 96 146 274), lower := (rows 35 70 140 328 145 33 96 128 256), losses := [] }

theorem u5336 : Upper (D 7) (R 7) [34,68,136,320,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5337 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 140 328 176 33 65 146 274), lower := (rows 35 70 140 328 176 33 65 128 256), losses := [] }

theorem u5337 : Upper (D 7) (R 7) [34,68,136,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5338 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 70 140 328 176 33 66 145 273), lower := (rows 35 70 140 328 176 33 66 128 256), losses := [] }

theorem u5338 : Upper (D 7) (R 7) [34,68,136,320,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5339 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 70 140 328 176 33 80 131 259), lower := (rows 35 70 140 328 176 33 80 128 256), losses := [] }

theorem u5339 : Upper (D 7) (R 7) [34,68,136,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5339 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5339
end Delivery.IrregularNine14.P07
