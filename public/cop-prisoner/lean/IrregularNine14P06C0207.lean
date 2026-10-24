import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0039
import IrregularNine14P06C0040

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12420 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 28 112 34 324 452 324), lower := (rows 11 35 133 28 112 34 64 128 256), losses := [] }

theorem u12420 : Upper (D 6) (R 6) [10,33,129,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12421 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 28 112 36 322 450 322), lower := (rows 11 35 133 28 112 36 64 128 256), losses := [] }

theorem u12421 : Upper (D 6) (R 6) [10,33,129,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12422 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 133 28 112 96 326 390 262), lower := (rows 11 35 133 28 112 96 64 128 256), losses := [] }

theorem u12422 : Upper (D 6) (R 6) [10,33,129,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12423 : Route 9 := (fun mask => (mask,id))

def c12423 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12423 : Upper (D 6) (R 6) [10,33,129,20,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,129,20,96,256] 13 (by decide) (choices 1) [2,4] r12423 c12423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2387
  · exact u2388

def b12424 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 28 304 34 68 196 324), lower := (rows 11 35 133 28 304 34 64 128 256), losses := [] }

theorem u12424 : Upper (D 6) (R 6) [10,33,129,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12425 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 28 304 36 66 194 322), lower := (rows 11 35 133 28 304 36 64 128 256), losses := [] }

theorem u12425 : Upper (D 6) (R 6) [10,33,129,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12426 : Route 9 := (fun mask => (mask,id))

def c12426 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12426 : Upper (D 6) (R 6) [10,33,129,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,129,20,288,64] 13 (by decide) (choices 1) [2,4] r12426 c12426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2389
  · exact u2390

def b12427 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 28 336 34 100 228 356), lower := (rows 11 35 133 28 336 34 64 128 256), losses := [] }

theorem u12427 : Upper (D 6) (R 6) [10,33,129,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12428 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 28 336 36 98 226 354), lower := (rows 11 35 133 28 336 36 64 128 256), losses := [] }

theorem u12428 : Upper (D 6) (R 6) [10,33,129,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12429 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 132, targets := 64 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 11 35 133 28 336 96 102 166 294), lower := (rows 11 35 133 28 336 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 128 256), good := (rows 11 35 129 59 368 96 96 128 256) }] }

theorem u12429 : Upper (D 6) (R 6) [10,33,129,20,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12430 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 133 76 22 48 352 480 352), lower := (rows 11 35 133 76 22 48 64 128 256), losses := [] }

theorem u12430 : Upper (D 6) (R 6) [10,33,129,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12430 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12431 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 76 22 96 368 432 304), lower := (rows 11 35 133 76 22 96 64 128 256), losses := [] }

theorem u12431 : Upper (D 6) (R 6) [10,33,129,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12432 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 76 22 288 112 240 368), lower := (rows 11 35 133 76 22 288 64 128 256), losses := [] }

theorem u12432 : Upper (D 6) (R 6) [10,33,129,68,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12432 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12433 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 133 76 52 34 336 464 336), lower := (rows 11 35 133 76 52 34 64 128 256), losses := [] }

theorem u12433 : Upper (D 6) (R 6) [10,33,129,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12434 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 76 52 48 322 450 322), lower := (rows 11 35 133 76 52 48 64 128 256), losses := [] }

theorem u12434 : Upper (D 6) (R 6) [10,33,129,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12434 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12435 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 11 35 133 76 52 96 338 402 274), lower := (rows 11 35 133 76 52 96 64 128 256), losses := [] }

theorem u12435 : Upper (D 6) (R 6) [10,33,129,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12436 : PairBound 9 := { available := 82, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 35 133 76 52 288 82 210 338), lower := (rows 11 35 133 76 52 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 295 65 129 257), good := (rows 506 482 508 124 60 288 64 128 288) }] }

theorem u12436 : Upper (D 6) (R 6) [10,33,129,68,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12436 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12437 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 76 82 36 368 432 304), lower := (rows 11 35 133 76 82 36 64 128 256), losses := [] }

theorem u12437 : Upper (D 6) (R 6) [10,33,129,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12438 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 133 76 82 48 356 420 292), lower := (rows 11 35 133 76 82 48 64 128 256), losses := [] }

theorem u12438 : Upper (D 6) (R 6) [10,33,129,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12438 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12439 : Route 9 := (fun mask => (mask,id))

def c12439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12439 : Upper (D 6) (R 6) [10,33,129,68,66,256] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,66,256] 13 (by decide) (choices 1) [4,16,32] r12439 c12439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2391
  · exact u2392
  · exact u2393

def b12440 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 133 76 112 34 340 404 276), lower := (rows 11 35 133 76 112 34 64 128 256), losses := [] }

theorem u12440 : Upper (D 6) (R 6) [10,33,129,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12441 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 76 112 36 338 402 274), lower := (rows 11 35 133 76 112 36 64 128 256), losses := [] }

theorem u12441 : Upper (D 6) (R 6) [10,33,129,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12442 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 76 112 48 326 390 262), lower := (rows 11 35 133 76 112 48 64 128 256), losses := [] }

theorem u12442 : Upper (D 6) (R 6) [10,33,129,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12442 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12443 : Route 9 := (fun mask => (mask,id))

def c12443 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12443 : Upper (D 6) (R 6) [10,33,129,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,96,256] 13 (by decide) (choices 1) [2,4,16] r12443 c12443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2394
  · exact u2395
  · exact u2396

def b12444 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 76 274 36 112 240 368), lower := (rows 11 35 133 76 274 36 64 128 256), losses := [] }

theorem u12444 : Upper (D 6) (R 6) [10,33,129,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12445 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 133 76 274 48 100 228 356), lower := (rows 11 35 133 76 274 48 64 128 256), losses := [] }

theorem u12445 : Upper (D 6) (R 6) [10,33,129,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12445 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12446 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 76 274 96 116 180 308), lower := (rows 11 35 133 76 274 96 64 128 256), losses := [] }

theorem u12446 : Upper (D 6) (R 6) [10,33,129,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12447 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 76 276 34 112 240 368), lower := (rows 11 35 133 76 276 34 64 128 256), losses := [] }

theorem u12447 : Upper (D 6) (R 6) [10,33,129,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12448 : PairBound 9 := { available := 98, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 35 133 76 276 48 98 226 354), lower := (rows 11 35 133 76 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 67 131 259), good := (rows 490 482 508 124 316 48 64 128 256) }] }

theorem u12448 : Upper (D 6) (R 6) [10,33,129,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12448 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12449 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 76 276 96 114 178 306), lower := (rows 11 35 133 76 276 96 64 128 256), losses := [] }

theorem u12449 : Upper (D 6) (R 6) [10,33,129,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12450 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 76 304 34 84 212 340), lower := (rows 11 35 133 76 304 34 64 128 256), losses := [] }

theorem u12450 : Upper (D 6) (R 6) [10,33,129,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12451 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 76 304 36 82 210 338), lower := (rows 11 35 133 76 304 36 64 128 256), losses := [] }

theorem u12451 : Upper (D 6) (R 6) [10,33,129,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12452 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 133 76 304 48 70 198 326), lower := (rows 11 35 133 76 304 48 64 128 256), losses := [] }

theorem u12452 : Upper (D 6) (R 6) [10,33,129,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12452 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12453 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 76 304 96 86 150 278), lower := (rows 11 35 133 76 304 96 64 128 256), losses := [] }

theorem u12453 : Upper (D 6) (R 6) [10,33,129,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12454 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 76 336 34 116 180 308), lower := (rows 11 35 133 76 336 34 64 128 256), losses := [] }

theorem u12454 : Upper (D 6) (R 6) [10,33,129,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12455 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 76 336 36 114 178 306), lower := (rows 11 35 133 76 336 36 64 128 256), losses := [] }

theorem u12455 : Upper (D 6) (R 6) [10,33,129,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12456 : Route 9 := (fun mask => (mask,id))

def c12456 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12456 : Upper (D 6) (R 6) [10,33,129,68,320,16] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,320,16] 13 (by decide) (choices 1) [2,4,32] r12456 c12456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2397
  · exact u2398
  · exact u2399

def b12457 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 88 52 34 324 452 324), lower := (rows 11 35 133 88 52 34 64 128 256), losses := [] }

theorem u12457 : Upper (D 6) (R 6) [10,33,129,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12458 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 133 88 52 36 322 450 322), lower := (rows 11 35 133 88 52 36 64 128 256), losses := [] }

theorem u12458 : Upper (D 6) (R 6) [10,33,129,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12459 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 88 52 96 326 390 262), lower := (rows 11 35 133 88 52 96 64 128 256), losses := [] }

theorem u12459 : Upper (D 6) (R 6) [10,33,129,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12460 : Route 9 := (fun mask => (mask,id))

def c12460 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12460 : Upper (D 6) (R 6) [10,33,129,80,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,36,256] 13 (by decide) (choices 1) [2,4] r12460 c12460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2400
  · exact u2401

def b12461 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 11 35 133 88 274 36 100 228 356), lower := (rows 11 35 133 88 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 100 164 292), good := (rows 26 506 484 88 282 484 64 128 256) }] }

theorem u12461 : Upper (D 6) (R 6) [10,33,129,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12462 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 88 274 96 100 164 292), lower := (rows 11 35 133 88 274 96 64 128 256), losses := [] }

theorem u12462 : Upper (D 6) (R 6) [10,33,129,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12463 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 88 276 34 100 228 356), lower := (rows 11 35 133 88 276 34 64 128 256), losses := [] }

theorem u12463 : Upper (D 6) (R 6) [10,33,129,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12464 : Route 9 := (fun mask => (mask,id))

def c12464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12464 : Upper (D 6) (R 6) [10,33,129,80,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,260,4] 13 (by decide) (choices 1) [2,32] r12464 c12464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2402
  · exact u2403

def b12465 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 88 276 96 102 166 294), lower := (rows 11 35 133 88 276 96 64 128 256), losses := [] }

theorem u12465 : Upper (D 6) (R 6) [10,33,129,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12466 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 88 304 34 68 196 324), lower := (rows 11 35 133 88 304 34 64 128 256), losses := [] }

theorem u12466 : Upper (D 6) (R 6) [10,33,129,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12467 : Route 9 := (fun mask => (mask,id))

def c12467 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12467 : Upper (D 6) (R 6) [10,33,129,80,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,288,4] 13 (by decide) (choices 1) [2,4] r12467 c12467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2404
  · exact u2405

def b12468 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 88 304 96 70 134 262), lower := (rows 11 35 133 88 304 96 64 128 256), losses := [] }

theorem u12468 : Upper (D 6) (R 6) [10,33,129,80,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12469 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 133 268 22 48 96 224 352), lower := (rows 11 35 133 268 22 48 64 128 256), losses := [] }

theorem u12469 : Upper (D 6) (R 6) [10,33,129,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12469 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12470 : Route 9 := (fun mask => (mask,id))

def c12470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12470 : Upper (D 6) (R 6) [10,33,129,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,6,64] 13 (by decide) (choices 1) [16,32] r12470 c12470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2406
  · exact u2407

def b12471 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 133 268 52 34 80 208 336), lower := (rows 11 35 133 268 52 34 64 128 256), losses := [] }

theorem u12471 : Upper (D 6) (R 6) [10,33,129,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12472 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 268 52 48 66 194 322), lower := (rows 11 35 133 268 52 48 64 128 256), losses := [] }

theorem u12472 : Upper (D 6) (R 6) [10,33,129,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12472 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12473 : Route 9 := (fun mask => (mask,id))

def c12473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12473 : Upper (D 6) (R 6) [10,33,129,260,36,64] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,36,64] 13 (by decide) (choices 1) [2,16] r12473 c12473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2408
  · exact u2409

def b12474 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 268 82 36 112 240 368), lower := (rows 11 35 133 268 82 36 64 128 256), losses := [] }

theorem u12474 : Upper (D 6) (R 6) [10,33,129,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12475 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 133 268 82 48 100 228 356), lower := (rows 11 35 133 268 82 48 64 128 256), losses := [] }

theorem u12475 : Upper (D 6) (R 6) [10,33,129,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12475 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12476 : Route 9 := (fun mask => (mask,id))

def c12476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12476 : Upper (D 6) (R 6) [10,33,129,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,66,64] 13 (by decide) (choices 1) [4,16,32] r12476 c12476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2410
  · exact u2411
  · exact u2412

def b12477 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 268 84 34 112 240 368), lower := (rows 11 35 133 268 84 34 64 128 256), losses := [] }

theorem u12477 : Upper (D 6) (R 6) [10,33,129,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12478 : PairBound 9 := { available := 98, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 35 133 268 84 48 98 226 354), lower := (rows 11 35 133 268 84 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 67 131 259), good := (rows 490 482 508 316 124 48 64 128 256) }] }

theorem u12478 : Upper (D 6) (R 6) [10,33,129,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12478 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12479 : Route 9 := (fun mask => (mask,id))

def c12479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12479 : Upper (D 6) (R 6) [10,33,129,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,68,64] 13 (by decide) (choices 1) [2,16,32] r12479 c12479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2413
  · exact u2414
  · exact u2415

#print axioms u12479
end Delivery.IrregularNine14.P06
