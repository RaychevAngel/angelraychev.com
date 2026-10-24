import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0167

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r27360 : Route 9 := (fun mask => (mask,id))

def c27360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27360 : Upper (D 7) (R 7) [36,320,10,129,192,16] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,192,16] 13 (by decide) (choices 1) [1,2,32] r27360 c27360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10051
  · exact u10052
  · exact u10053

def b27361 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 322 14 152 19 33 224 224 480), lower := (rows 37 322 14 152 19 33 64 128 256), losses := [] }

theorem u27361 : Upper (D 7) (R 7) [36,320,10,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27362 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(2,6),(3,1),(3,6)], upper := (rows 37 322 14 152 19 96 225 161 417), lower := (rows 37 322 14 152 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 32 0 129 257), good := (rows 421 258 14 156 415 32 0 128 256) }] }

theorem u27362 : Upper (D 7) (R 7) [36,320,10,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27363 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 225, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(1,7),(3,1),(4,7)], upper := (rows 37 322 14 152 19 160 97 225 353), lower := (rows 37 322 14 152 19 160 64 128 256), losses := [] }

theorem u27363 : Upper (D 7) (R 7) [36,320,10,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27364 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 322 14 152 50 33 193 193 449), lower := (rows 37 322 14 152 50 33 64 128 256), losses := [] }

theorem u27364 : Upper (D 7) (R 7) [36,320,10,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27365 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 14 152 50 96 193 129 385), lower := (rows 37 322 14 152 50 96 64 128 256), losses := [] }

theorem u27365 : Upper (D 7) (R 7) [36,320,10,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27366 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 0, region := 322, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(1,7),(4,7)], upper := (rows 37 322 14 152 50 160 65 193 321), lower := (rows 37 322 14 152 50 160 64 128 256), losses := [] }

theorem u27366 : Upper (D 7) (R 7) [36,320,10,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27367 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 450, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 14 152 81 33 226 162 418), lower := (rows 37 322 14 152 81 33 64 128 256), losses := [] }

theorem u27367 : Upper (D 7) (R 7) [36,320,10,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27368 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 14 152 81 34 225 161 417), lower := (rows 37 322 14 152 81 34 64 128 256), losses := [] }

theorem u27368 : Upper (D 7) (R 7) [36,320,10,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27369 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 322 14 152 81 160 99 163 291), lower := (rows 37 322 14 152 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 45 184 81 160 64 160 256) }] }

theorem u27369 : Upper (D 7) (R 7) [36,320,10,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27370 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 450, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 14 152 112 33 195 131 387), lower := (rows 37 322 14 152 112 33 64 128 256), losses := [] }

theorem u27370 : Upper (D 7) (R 7) [36,320,10,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27371 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 322 14 152 112 34 193 129 385), lower := (rows 37 322 14 152 112 34 64 128 256), losses := [] }

theorem u27371 : Upper (D 7) (R 7) [36,320,10,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27372 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 0, region := 322, targets := 32 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(1,7),(4,7)], upper := (rows 37 322 14 152 112 160 67 131 259), lower := (rows 37 322 14 152 112 160 64 128 256), losses := [] }

theorem u27372 : Upper (D 7) (R 7) [36,320,10,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27373 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 322 14 168 19 33 208 208 464), lower := (rows 37 322 14 168 19 33 64 128 256), losses := [] }

theorem u27373 : Upper (D 7) (R 7) [36,320,10,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27374 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 322 14 168 19 48 193 193 449), lower := (rows 37 322 14 168 19 48 64 128 256), losses := [] }

theorem u27374 : Upper (D 7) (R 7) [36,320,10,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27374 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27375 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 37 322 14 168 19 96 209 145 401), lower := (rows 37 322 14 168 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 352 45 168 505 96 96 128 256) }] }

theorem u27375 : Upper (D 7) (R 7) [36,320,10,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27376 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 322 14 168 19 160 81 209 337), lower := (rows 37 322 14 168 19 160 64 128 256), losses := [] }

theorem u27376 : Upper (D 7) (R 7) [36,320,10,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27377 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 14 168 81 33 210 146 402), lower := (rows 37 322 14 168 81 33 64 128 256), losses := [] }

theorem u27377 : Upper (D 7) (R 7) [36,320,10,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27378 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 322 14 168 81 34 209 145 401), lower := (rows 37 322 14 168 81 34 64 128 256), losses := [] }

theorem u27378 : Upper (D 7) (R 7) [36,320,10,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27379 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 14 168 81 48 195 131 387), lower := (rows 37 322 14 168 81 48 64 128 256), losses := [{ target := 5, region := (rows 1 51 12 8 17 0 81 145 273), good := (rows 471 322 14 142 467 466 64 128 256) }] }

theorem u27379 : Upper (D 7) (R 7) [36,320,10,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27379 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27380 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 322 14 168 81 160 83 147 275), lower := (rows 37 322 14 168 81 160 64 128 256), losses := [] }

theorem u27380 : Upper (D 7) (R 7) [36,320,10,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27381 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 14 168 145 33 82 210 338), lower := (rows 37 322 14 168 145 33 64 128 256), losses := [] }

theorem u27381 : Upper (D 7) (R 7) [36,320,10,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27382 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 322 14 168 145 34 81 209 337), lower := (rows 37 322 14 168 145 34 64 128 256), losses := [] }

theorem u27382 : Upper (D 7) (R 7) [36,320,10,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27383 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 14 168 145 48 67 195 323), lower := (rows 37 322 14 168 145 48 64 128 256), losses := [] }

theorem u27383 : Upper (D 7) (R 7) [36,320,10,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27383 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27384 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 322, targets := 128 }], pairs := [(0,1),(1,5),(1,7),(4,5)], upper := (rows 37 322 14 168 145 96 83 147 275), lower := (rows 37 322 14 168 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 352 45 168 145 96 96 128 256) }] }

theorem u27384 : Upper (D 7) (R 7) [36,320,10,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27385 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 14 168 146 33 81 209 337), lower := (rows 37 322 14 168 146 33 64 128 256), losses := [] }

theorem u27385 : Upper (D 7) (R 7) [36,320,10,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27386 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 14 168 146 48 65 193 321), lower := (rows 37 322 14 168 146 48 64 128 256), losses := [] }

theorem u27386 : Upper (D 7) (R 7) [36,320,10,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27386 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27387 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 37 322 14 168 146 96 81 145 273), lower := (rows 37 322 14 168 146 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 98 64 128 256), good := (rows 36 354 46 168 190 96 96 128 256) }] }

theorem u27387 : Upper (D 7) (R 7) [36,320,10,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27388 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 14 168 208 33 83 147 275), lower := (rows 37 322 14 168 208 33 64 128 256), losses := [] }

theorem u27388 : Upper (D 7) (R 7) [36,320,10,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27389 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 322 14 168 208 34 81 145 273), lower := (rows 37 322 14 168 208 34 64 128 256), losses := [] }

theorem u27389 : Upper (D 7) (R 7) [36,320,10,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27390 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 14 168 208 48 67 131 259), lower := (rows 37 322 14 168 208 48 64 128 256), losses := [] }

theorem u27390 : Upper (D 7) (R 7) [36,320,10,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27390 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27391 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 322 14 200 19 33 240 176 432), lower := (rows 37 322 14 200 19 33 64 128 256), losses := [] }

theorem u27391 : Upper (D 7) (R 7) [36,320,10,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27392 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 322 14 200 19 48 225 161 417), lower := (rows 37 322 14 200 19 48 64 128 256), losses := [] }

theorem u27392 : Upper (D 7) (R 7) [36,320,10,192,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27393 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 37 322 14 200 19 160 113 177 305), lower := (rows 37 322 14 200 19 160 64 128 256), losses := [] }

theorem u27393 : Upper (D 7) (R 7) [36,320,10,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27394 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 322 14 200 50 33 209 145 401), lower := (rows 37 322 14 200 50 33 64 128 256), losses := [] }

theorem u27394 : Upper (D 7) (R 7) [36,320,10,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27395 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 14 200 50 48 193 129 385), lower := (rows 37 322 14 200 50 48 64 128 256), losses := [] }

theorem u27395 : Upper (D 7) (R 7) [36,320,10,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27395 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27396 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 37 322 14 200 50 160 81 145 273), lower := (rows 37 322 14 200 50 160 64 128 256), losses := [] }

theorem u27396 : Upper (D 7) (R 7) [36,320,10,192,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27397 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 14 200 145 33 114 178 306), lower := (rows 37 322 14 200 145 33 64 128 256), losses := [] }

theorem u27397 : Upper (D 7) (R 7) [36,320,10,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27398 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 14 200 145 34 113 177 305), lower := (rows 37 322 14 200 145 34 64 128 256), losses := [] }

theorem u27398 : Upper (D 7) (R 7) [36,320,10,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27399 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(4,6)], upper := (rows 37 322 14 200 145 48 99 163 291), lower := (rows 37 322 14 200 145 48 64 128 256), losses := [] }

theorem u27399 : Upper (D 7) (R 7) [36,320,10,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27399 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27400 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 14 200 146 33 113 177 305), lower := (rows 37 322 14 200 146 33 64 128 256), losses := [] }

theorem u27400 : Upper (D 7) (R 7) [36,320,10,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27401 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 37 322 14 200 146 48 97 161 289), lower := (rows 37 322 14 200 146 48 64 128 256), losses := [] }

theorem u27401 : Upper (D 7) (R 7) [36,320,10,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27401 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27402 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 14 200 176 33 83 147 275), lower := (rows 37 322 14 200 176 33 64 128 256), losses := [] }

theorem u27402 : Upper (D 7) (R 7) [36,320,10,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27403 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 14 200 176 34 81 145 273), lower := (rows 37 322 14 200 176 34 64 128 256), losses := [] }

theorem u27403 : Upper (D 7) (R 7) [36,320,10,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27404 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 14 200 176 48 67 131 259), lower := (rows 37 322 14 200 176 48 64 128 256), losses := [] }

theorem u27404 : Upper (D 7) (R 7) [36,320,10,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27404 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27405 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 28 11 81 34 224 160 416), lower := (rows 37 322 28 11 81 34 64 128 256), losses := [] }

theorem u27405 : Upper (D 7) (R 7) [36,320,24,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27406 : Route 9 := (fun mask => (mask,id))

def c27406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27406 : Upper (D 7) (R 7) [36,320,24,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,65,128] 13 (by decide) (choices 1) [2,32,128] r27406 c27406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10054
  · exact u10055
  · exact u10056

def b27407 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 28 11 112 33 194 130 386), lower := (rows 37 322 28 11 112 33 64 128 256), losses := [] }

theorem u27407 : Upper (D 7) (R 7) [36,320,24,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27408 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 28 11 112 34 193 129 385), lower := (rows 37 322 28 11 112 34 64 128 256), losses := [] }

theorem u27408 : Upper (D 7) (R 7) [36,320,24,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27409 : Route 9 := (fun mask => (mask,id))

def c27409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27409 : Upper (D 7) (R 7) [36,320,24,3,96,128] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,96,128] 13 (by decide) (choices 1) [1,2,128] r27409 c27409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10057
  · exact u10058
  · exact u10059

def b27410 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,0),(2,1),(4,1)], upper := (rows 37 322 28 11 145 34 224 224 480), lower := (rows 37 322 28 11 145 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 97 161 289), good := (rows 501 320 28 477 465 480 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 290 61 43 145 34 0 128 256) }] }

theorem u27410 : Upper (D 7) (R 7) [36,320,24,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27411 : Route 9 := (fun mask => (mask,id))

def c27411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27411 : Upper (D 7) (R 7) [36,320,24,3,129,64] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,129,64] 13 (by decide) (choices 1) [2,32,128] r27411 c27411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10060
  · exact u10061
  · exact u10062

def b27412 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 0, region := 322, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 322 28 11 145 160 98 226 354), lower := (rows 37 322 28 11 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 320 61 9 177 160 64 160 256) }] }

theorem u27412 : Upper (D 7) (R 7) [36,320,24,3,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27413 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 28 11 146 33 224 224 480), lower := (rows 37 322 28 11 146 33 64 128 256), losses := [] }

theorem u27413 : Upper (D 7) (R 7) [36,320,24,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27414 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,6),(4,6)], upper := (rows 37 322 28 11 146 96 225 161 417), lower := (rows 37 322 28 11 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 24 32 0 129 257), good := (rows 421 258 28 415 146 32 0 128 256) },{ target := 7, region := (rows 17 2 20 24 16 98 64 0 256), good := (rows 37 354 29 43 63 96 96 0 256) }] }

theorem u27414 : Upper (D 7) (R 7) [36,320,24,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27415 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(3,6)], upper := (rows 37 322 28 11 146 160 97 225 353), lower := (rows 37 322 28 11 146 160 64 128 256), losses := [] }

theorem u27415 : Upper (D 7) (R 7) [36,320,24,3,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27416 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 28 11 176 33 194 194 450), lower := (rows 37 322 28 11 176 33 64 128 256), losses := [] }

theorem u27416 : Upper (D 7) (R 7) [36,320,24,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27417 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 37 322 28 11 176 34 193 193 449), lower := (rows 37 322 28 11 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 32 73 137 265), good := (rows 501 320 476 477 176 32 64 128 256) }] }

theorem u27417 : Upper (D 7) (R 7) [36,320,24,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27418 : Route 9 := (fun mask => (mask,id))

def c27418 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27418 : Upper (D 7) (R 7) [36,320,24,3,160,64] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,160,64] 13 (by decide) (choices 1) [1,2,128] r27418 c27418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10063
  · exact u10064
  · exact u10065

def b27419 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 28 11 176 160 67 195 323), lower := (rows 37 322 28 11 176 160 64 128 256), losses := [] }

theorem u27419 : Upper (D 7) (R 7) [36,320,24,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27419
end Delivery.IrregularNine14.P07
