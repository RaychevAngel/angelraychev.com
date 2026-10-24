import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0021

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12420 : Route 9 := (fun mask => (mask,id))

def c12420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12420 : Upper (D 7) (R 7) [6,33,72,384,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,66,128] 13 (by decide) (choices 1) [1,16,32] r12420 c12420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1266
  · exact u1267
  · exact u1268

def b12421 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 392 112 33 210 146 402), lower := (rows 7 35 76 392 112 33 64 128 256), losses := [] }

theorem u12421 : Upper (D 7) (R 7) [6,33,72,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12422 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 392 112 34 209 145 401), lower := (rows 7 35 76 392 112 34 64 128 256), losses := [] }

theorem u12422 : Upper (D 7) (R 7) [6,33,72,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12423 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 392 112 48 195 131 387), lower := (rows 7 35 76 392 112 48 64 128 256), losses := [] }

theorem u12423 : Upper (D 7) (R 7) [6,33,72,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12423 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12424 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 80, targets := 128 }], pairs := [(0,6),(4,0),(4,1),(4,7)], upper := (rows 7 35 76 392 112 160 83 147 275), lower := (rows 7 35 76 392 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 22 34 124 424 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 21 33 124 424 112 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 424 48 160 0 160 256) }] }

theorem u12424 : Upper (D 7) (R 7) [6,33,72,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12425 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 392 145 34 112 240 368), lower := (rows 7 35 76 392 145 34 64 128 256), losses := [] }

theorem u12425 : Upper (D 7) (R 7) [6,33,72,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12426 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 76 392 145 48 98 226 354), lower := (rows 7 35 76 392 145 48 64 128 256), losses := [] }

theorem u12426 : Upper (D 7) (R 7) [6,33,72,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12426 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12427 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 392 145 96 114 178 306), lower := (rows 7 35 76 392 145 96 64 128 256), losses := [] }

theorem u12427 : Upper (D 7) (R 7) [6,33,72,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12428 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 392 146 33 112 240 368), lower := (rows 7 35 76 392 146 33 64 128 256), losses := [] }

theorem u12428 : Upper (D 7) (R 7) [6,33,72,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12429 : Route 9 := (fun mask => (mask,id))

def c12429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12429 : Upper (D 7) (R 7) [6,33,72,384,130,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,130,16] 13 (by decide) (choices 1) [1,32] r12429 c12429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1269
  · exact u1270

def b12430 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 392 146 96 113 177 305), lower := (rows 7 35 76 392 146 96 64 128 256), losses := [] }

theorem u12430 : Upper (D 7) (R 7) [6,33,72,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12431 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 392 176 33 82 210 338), lower := (rows 7 35 76 392 176 33 64 128 256), losses := [] }

theorem u12431 : Upper (D 7) (R 7) [6,33,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12432 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 392 176 34 81 209 337), lower := (rows 7 35 76 392 176 34 64 128 256), losses := [] }

theorem u12432 : Upper (D 7) (R 7) [6,33,72,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12433 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 392 176 48 67 195 323), lower := (rows 7 35 76 392 176 48 64 128 256), losses := [] }

theorem u12433 : Upper (D 7) (R 7) [6,33,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12433 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12434 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 392 176 96 83 147 275), lower := (rows 7 35 76 392 176 96 64 128 256), losses := [] }

theorem u12434 : Upper (D 7) (R 7) [6,33,72,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12435 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 392 208 33 114 178 306), lower := (rows 7 35 76 392 208 33 64 128 256), losses := [] }

theorem u12435 : Upper (D 7) (R 7) [6,33,72,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12436 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 392 208 34 113 177 305), lower := (rows 7 35 76 392 208 34 64 128 256), losses := [] }

theorem u12436 : Upper (D 7) (R 7) [6,33,72,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12437 : Route 9 := (fun mask => (mask,id))

def c12437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12437 : Upper (D 7) (R 7) [6,33,72,384,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192,16] 13 (by decide) (choices 1) [1,2,32] r12437 c12437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1271
  · exact u1272
  · exact u1273

def b12438 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 25 82 40 480 416 416), lower := (rows 7 35 196 25 82 40 64 128 256), losses := [] }

theorem u12438 : Upper (D 7) (R 7) [6,33,192,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12438 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12439 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 25 82 160 360 424 296), lower := (rows 7 35 196 25 82 160 64 128 256), losses := [] }

theorem u12439 : Upper (D 7) (R 7) [6,33,192,17,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12440 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 7 35 196 25 82 288 232 168 424), lower := (rows 7 35 196 25 82 288 64 128 256), losses := [] }

theorem u12440 : Upper (D 7) (R 7) [6,33,192,17,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12440 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12441 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 25 112 34 456 392 392), lower := (rows 7 35 196 25 112 34 64 128 256), losses := [] }

theorem u12441 : Upper (D 7) (R 7) [6,33,192,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12442 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 25 112 40 450 386 386), lower := (rows 7 35 196 25 112 40 64 128 256), losses := [] }

theorem u12442 : Upper (D 7) (R 7) [6,33,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12442 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12443 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 48, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 7 35 196 25 112 160 330 394 266), lower := (rows 7 35 196 25 112 160 64 128 256), losses := [] }

theorem u12443 : Upper (D 7) (R 7) [6,33,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12444 : Route 9 := (fun mask => (mask,id))

def c12444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12444 : Upper (D 7) (R 7) [6,33,192,17,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,96,256] 13 (by decide) (choices 1) [2,8,128] r12444 c12444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1274
  · exact u1275
  · exact u1276

def b12445 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 35 196 25 274 40 224 224 480), lower := (rows 7 35 196 25 274 40 64 128 256), losses := [] }

theorem u12445 : Upper (D 7) (R 7) [6,33,192,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12445 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12446 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 25 274 96 232 168 424), lower := (rows 7 35 196 25 274 96 64 128 256), losses := [] }

theorem u12446 : Upper (D 7) (R 7) [6,33,192,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12447 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 25 280 34 224 224 480), lower := (rows 7 35 196 25 280 34 64 128 256), losses := [] }

theorem u12447 : Upper (D 7) (R 7) [6,33,192,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12448 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 25 280 96 226 162 418), lower := (rows 7 35 196 25 280 96 64 128 256), losses := [] }

theorem u12448 : Upper (D 7) (R 7) [6,33,192,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12449 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 25 304 34 200 200 456), lower := (rows 7 35 196 25 304 34 64 128 256), losses := [] }

theorem u12449 : Upper (D 7) (R 7) [6,33,192,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12450 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 7 35 196 25 304 40 194 194 450), lower := (rows 7 35 196 25 304 40 64 128 256), losses := [] }

theorem u12450 : Upper (D 7) (R 7) [6,33,192,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12450 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12451 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 25 304 96 202 138 394), lower := (rows 7 35 196 25 304 96 64 128 256), losses := [] }

theorem u12451 : Upper (D 7) (R 7) [6,33,192,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12452 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 25 336 34 232 168 424), lower := (rows 7 35 196 25 336 34 64 128 256), losses := [] }

theorem u12452 : Upper (D 7) (R 7) [6,33,192,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12453 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 35 196 25 336 40 226 162 418), lower := (rows 7 35 196 25 336 40 64 128 256), losses := [] }

theorem u12453 : Upper (D 7) (R 7) [6,33,192,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12453 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12454 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 25 336 160 106 170 298), lower := (rows 7 35 196 25 336 160 64 128 256), losses := [] }

theorem u12454 : Upper (D 7) (R 7) [6,33,192,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12455 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 26 112 33 456 392 392), lower := (rows 7 35 196 26 112 33 64 128 256), losses := [] }

theorem u12455 : Upper (D 7) (R 7) [6,33,192,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12456 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 26 112 40 449 385 385), lower := (rows 7 35 196 26 112 40 64 128 256), losses := [] }

theorem u12456 : Upper (D 7) (R 7) [6,33,192,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12456 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12457 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 48, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 7 35 196 26 112 160 329 393 265), lower := (rows 7 35 196 26 112 160 64 128 256), losses := [] }

theorem u12457 : Upper (D 7) (R 7) [6,33,192,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12458 : Route 9 := (fun mask => (mask,id))

def c12458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12458 : Upper (D 7) (R 7) [6,33,192,18,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,96,256] 13 (by decide) (choices 1) [1,8,128] r12458 c12458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1277
  · exact u1278
  · exact u1279

def b12459 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 7 35 196 26 273 40 224 224 480), lower := (rows 7 35 196 26 273 40 64 128 256), losses := [] }

theorem u12459 : Upper (D 7) (R 7) [6,33,192,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12459 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12460 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 26 273 96 232 168 424), lower := (rows 7 35 196 26 273 96 64 128 256), losses := [] }

theorem u12460 : Upper (D 7) (R 7) [6,33,192,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12461 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 26 280 33 224 224 480), lower := (rows 7 35 196 26 280 33 64 128 256), losses := [] }

theorem u12461 : Upper (D 7) (R 7) [6,33,192,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12462 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 26 280 96 225 161 417), lower := (rows 7 35 196 26 280 96 64 128 256), losses := [] }

theorem u12462 : Upper (D 7) (R 7) [6,33,192,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12463 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 26 304 33 200 200 456), lower := (rows 7 35 196 26 304 33 64 128 256), losses := [] }

theorem u12463 : Upper (D 7) (R 7) [6,33,192,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12464 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 464, targets := 2 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 35 196 26 304 40 193 193 449), lower := (rows 7 35 196 26 304 40 64 128 256), losses := [] }

theorem u12464 : Upper (D 7) (R 7) [6,33,192,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12464 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12465 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 26 304 96 201 137 393), lower := (rows 7 35 196 26 304 96 64 128 256), losses := [] }

theorem u12465 : Upper (D 7) (R 7) [6,33,192,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12466 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 26 336 33 232 168 424), lower := (rows 7 35 196 26 336 33 64 128 256), losses := [] }

theorem u12466 : Upper (D 7) (R 7) [6,33,192,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12467 : Route 9 := (fun mask => (mask,id))

def c12467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12467 : Upper (D 7) (R 7) [6,33,192,18,320,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,320,8] 13 (by decide) (choices 1) [1,32,128] r12467 c12467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1280
  · exact u1281
  · exact u1282

def b12468 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 26 336 160 105 169 297), lower := (rows 7 35 196 26 336 160 64 128 256), losses := [] }

theorem u12468 : Upper (D 7) (R 7) [6,33,192,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12469 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 56 81 34 456 392 392), lower := (rows 7 35 196 56 81 34 64 128 256), losses := [] }

theorem u12469 : Upper (D 7) (R 7) [6,33,192,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12470 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 56 81 40 450 386 386), lower := (rows 7 35 196 56 81 40 64 128 256), losses := [] }

theorem u12470 : Upper (D 7) (R 7) [6,33,192,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12470 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12471 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 56 81 160 330 394 266), lower := (rows 7 35 196 56 81 160 64 128 256), losses := [] }

theorem u12471 : Upper (D 7) (R 7) [6,33,192,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12472 : Route 9 := (fun mask => (mask,id))

def c12472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12472 : Upper (D 7) (R 7) [6,33,192,48,65,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,65,256] 13 (by decide) (choices 1) [2,8,128] r12472 c12472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1283
  · exact u1284
  · exact u1285

def b12473 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 56 82 33 456 392 392), lower := (rows 7 35 196 56 82 33 64 128 256), losses := [] }

theorem u12473 : Upper (D 7) (R 7) [6,33,192,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12474 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 56 82 40 449 385 385), lower := (rows 7 35 196 56 82 40 64 128 256), losses := [] }

theorem u12474 : Upper (D 7) (R 7) [6,33,192,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12474 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12475 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 56 82 160 329 393 265), lower := (rows 7 35 196 56 82 160 64 128 256), losses := [] }

theorem u12475 : Upper (D 7) (R 7) [6,33,192,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12476 : Route 9 := (fun mask => (mask,id))

def c12476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12476 : Upper (D 7) (R 7) [6,33,192,48,66,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,66,256] 13 (by decide) (choices 1) [1,8,128] r12476 c12476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1286
  · exact u1287
  · exact u1288

def b12477 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 56 273 34 200 200 456), lower := (rows 7 35 196 56 273 34 64 128 256), losses := [] }

theorem u12477 : Upper (D 7) (R 7) [6,33,192,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12478 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 7 35 196 56 273 40 194 194 450), lower := (rows 7 35 196 56 273 40 64 128 256), losses := [] }

theorem u12478 : Upper (D 7) (R 7) [6,33,192,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12478 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12479 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 56 273 96 202 138 394), lower := (rows 7 35 196 56 273 96 64 128 256), losses := [] }

theorem u12479 : Upper (D 7) (R 7) [6,33,192,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12479
end Delivery.IrregularNine14.P07
