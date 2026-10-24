import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0144

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27360 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 25 84 36 74 138 266), lower := (rows 97 131 292 25 84 36 64 128 256), losses := [] }

theorem u27360 : Upper (D 6) (R 6) [96,129,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27361 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 131 292 25 84 40 70 134 262), lower := (rows 97 131 292 25 84 40 64 128 256), losses := [] }

theorem u27361 : Upper (D 6) (R 6) [96,129,288,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27361 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27362 : Route 9 := (fun mask => (mask,id))

def c27362 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27362 : Upper (D 6) (R 6) [96,129,288,18,12,1] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18,12,1] 13 (by decide) (choices 1) [2,4] r27362 c27362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8641
  · exact u8642

def r27363 : Route 9 := (fun mask => (mask,id))

def c27363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27363 : Upper (D 6) (R 6) [96,129,288,18,12,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18,12,2] 13 (by decide) (choices 1) [1,4] r27363 c27363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8643
  · exact u8644

def b27364 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 26 28 36 67 195 323), lower := (rows 97 131 292 26 28 36 64 128 256), losses := [] }

theorem u27364 : Upper (D 6) (R 6) [96,129,288,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27365 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 292 26 28 96 71 135 263), lower := (rows 97 131 292 26 28 96 64 128 256), losses := [] }

theorem u27365 : Upper (D 6) (R 6) [96,129,288,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27366 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(2,6)], upper := (rows 97 131 292 26 84 33 78 142 270), lower := (rows 97 131 292 26 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 136 264), good := (rows 33 163 292 446 20 33 0 128 256) }] }

theorem u27366 : Upper (D 6) (R 6) [96,129,288,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27367 : Route 9 := (fun mask => (mask,id))

def c27367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27367 : Upper (D 6) (R 6) [96,129,288,18,68,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18,68,2] 13 (by decide) (choices 1) [1,4,8] r27367 c27367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8645
  · exact u8646
  · exact u8647

def b27368 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 26 84 36 75 139 267), lower := (rows 97 131 292 26 84 36 64 128 256), losses := [] }

theorem u27368 : Upper (D 6) (R 6) [96,129,288,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27369 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 26 84 40 71 135 263), lower := (rows 97 131 292 26 84 40 64 128 256), losses := [] }

theorem u27369 : Upper (D 6) (R 6) [96,129,288,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27369 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27370 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 131 292 26 88 33 70 134 262), lower := (rows 97 131 292 26 88 33 64 128 256), losses := [] }

theorem u27370 : Upper (D 6) (R 6) [96,129,288,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27371 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 5, region := 325, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 131 292 26 88 34 69 133 261), lower := (rows 97 131 292 26 88 34 64 128 256), losses := [] }

theorem u27371 : Upper (D 6) (R 6) [96,129,288,18,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27372 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 26 88 36 71 135 263), lower := (rows 97 131 292 26 88 36 64 128 256), losses := [] }

theorem u27372 : Upper (D 6) (R 6) [96,129,288,18,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27373 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(2,6)], upper := (rows 97 131 292 28 82 33 78 142 270), lower := (rows 97 131 292 28 82 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 144 272), good := (rows 33 163 292 412 446 33 0 128 256) }] }

theorem u27373 : Upper (D 6) (R 6) [96,129,288,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27374 : Route 9 := (fun mask => (mask,id))

def c27374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27374 : Upper (D 6) (R 6) [96,129,288,20,66,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,20,66,2] 13 (by decide) (choices 1) [1,4,8] r27374 c27374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8648
  · exact u8649
  · exact u8650

def b27375 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 28 82 36 75 139 267), lower := (rows 97 131 292 28 82 36 64 128 256), losses := [] }

theorem u27375 : Upper (D 6) (R 6) [96,129,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27376 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 28 82 40 71 135 263), lower := (rows 97 131 292 28 82 40 64 128 256), losses := [] }

theorem u27376 : Upper (D 6) (R 6) [96,129,288,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27376 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27377 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 131 292 28 88 33 70 134 262), lower := (rows 97 131 292 28 88 33 64 128 256), losses := [] }

theorem u27377 : Upper (D 6) (R 6) [96,129,288,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27378 : Route 9 := (fun mask => (mask,id))

def c27378 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27378 : Upper (D 6) (R 6) [96,129,288,20,72,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,20,72,2] 13 (by decide) (choices 1) [1,2,4] r27378 c27378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8651
  · exact u8652
  · exact u8653

def b27379 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 28 88 36 67 131 259), lower := (rows 97 131 292 28 88 36 64 128 256), losses := [] }

theorem u27379 : Upper (D 6) (R 6) [96,129,288,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27380 : Route 9 := (fun mask => (mask,id))

def c27380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27380 : Upper (D 6) (R 6) [96,132,258,3,5,8] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,5,8] 13 (by decide) (choices 1) [16,32] r27380 c27380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8654
  · exact u8655

def b27381 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 11 21 96 120 184 312), lower := (rows 97 134 262 11 21 96 64 128 256), losses := [] }

theorem u27381 : Upper (D 6) (R 6) [96,132,258,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27382 : Route 9 := (fun mask => (mask,id))

def c27382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27382 : Upper (D 6) (R 6) [96,132,258,3,12,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,12,1] 13 (by decide) (choices 1) [16,32] r27382 c27382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8656
  · exact u8657

def b27383 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 134 262 11 28 48 97 225 353), lower := (rows 97 134 262 11 28 48 64 128 256), losses := [] }

theorem u27383 : Upper (D 6) (R 6) [96,132,258,3,12,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27383 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27384 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 11 28 96 113 177 305), lower := (rows 97 134 262 11 28 96 64 128 256), losses := [] }

theorem u27384 : Upper (D 6) (R 6) [96,132,258,3,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27385 : Route 9 := (fun mask => (mask,id))

def c27385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27385 : Upper (D 6) (R 6) [96,132,258,3,36,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,36,1] 13 (by decide) (choices 1) [8,16] r27385 c27385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8658
  · exact u8659

def b27386 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 134 262 11 52 40 81 209 337), lower := (rows 97 134 262 11 52 40 64 128 256), losses := [] }

theorem u27386 : Upper (D 6) (R 6) [96,132,258,3,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27386 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27387 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 11 52 48 73 201 329), lower := (rows 97 134 262 11 52 48 64 128 256), losses := [] }

theorem u27387 : Upper (D 6) (R 6) [96,132,258,3,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27387 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27388 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 11 52 96 89 153 281), lower := (rows 97 134 262 11 52 96 64 128 256), losses := [] }

theorem u27388 : Upper (D 6) (R 6) [96,132,258,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27389 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 134 262 11 56 33 84 212 340), lower := (rows 97 134 262 11 56 33 64 128 256), losses := [] }

theorem u27389 : Upper (D 6) (R 6) [96,132,258,3,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27390 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 6 }], pairs := [(0,1),(0,2),(4,0)], upper := (rows 97 134 262 11 56 36 81 209 337), lower := (rows 97 134 262 11 56 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 38 64 128 256), good := (rows 96 166 294 58 56 36 64 128 256) }] }

theorem u27390 : Upper (D 6) (R 6) [96,132,258,3,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27391 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 97 134 262 11 56 48 69 197 325), lower := (rows 97 134 262 11 56 48 64 128 256), losses := [] }

theorem u27391 : Upper (D 6) (R 6) [96,132,258,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27391 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27392 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 11 56 96 85 149 277), lower := (rows 97 134 262 11 56 96 64 128 256), losses := [] }

theorem u27392 : Upper (D 6) (R 6) [96,132,258,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27393 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 134 262 25 26 33 100 228 356), lower := (rows 97 134 262 25 26 33 64 128 256), losses := [] }

theorem u27393 : Upper (D 6) (R 6) [96,132,258,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27394 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 262 25 26 36 97 225 353), lower := (rows 97 134 262 25 26 36 64 128 256), losses := [{ target := 1, region := (rows 55 0 4 24 16 38 119 183 311), good := (rows 481 485 485 473 505 485 64 128 256) }] }

theorem u27394 : Upper (D 6) (R 6) [96,132,258,17,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27395 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 25 26 96 101 165 293), lower := (rows 97 134 262 25 26 96 64 128 256), losses := [] }

theorem u27395 : Upper (D 6) (R 6) [96,132,258,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27396 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 134 262 25 50 33 76 204 332), lower := (rows 97 134 262 25 50 33 64 128 256), losses := [] }

theorem u27396 : Upper (D 6) (R 6) [96,132,258,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27397 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 262 25 50 36 73 201 329), lower := (rows 97 134 262 25 50 36 64 128 256), losses := [] }

theorem u27397 : Upper (D 6) (R 6) [96,132,258,17,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27398 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 25 50 40 69 197 325), lower := (rows 97 134 262 25 50 40 64 128 256), losses := [] }

theorem u27398 : Upper (D 6) (R 6) [96,132,258,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27398 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27399 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 25 50 96 77 141 269), lower := (rows 97 134 262 25 50 96 64 128 256), losses := [] }

theorem u27399 : Upper (D 6) (R 6) [96,132,258,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27400 : Route 9 := (fun mask => (mask,id))

def c27400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27400 : Upper (D 6) (R 6) [96,132,258,18,36,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,18,36,1] 13 (by decide) (choices 1) [1,8] r27400 c27400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8660
  · exact u8661

def b27401 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6)], upper := (rows 97 134 262 26 52 40 65 193 321), lower := (rows 97 134 262 26 52 40 64 128 256), losses := [] }

theorem u27401 : Upper (D 6) (R 6) [96,132,258,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27401 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27402 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 262 26 52 96 73 137 265), lower := (rows 97 134 262 26 52 96 64 128 256), losses := [] }

theorem u27402 : Upper (D 6) (R 6) [96,132,258,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27403 : Route 9 := (fun mask => (mask,id))

def c27403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27403 : Upper (D 6) (R 6) [96,132,258,34,68,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,34,68,1] 13 (by decide) (choices 1) [1,8,16] r27403 c27403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8662
  · exact u8663
  · exact u8664

def b27404 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 42 84 40 81 145 273), lower := (rows 97 134 262 42 84 40 64 128 256), losses := [] }

theorem u27404 : Upper (D 6) (R 6) [96,132,258,34,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27404 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27405 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 262 42 84 48 73 137 265), lower := (rows 97 134 262 42 84 48 64 128 256), losses := [] }

theorem u27405 : Upper (D 6) (R 6) [96,132,258,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27405 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27406 : Route 9 := (fun mask => (mask,id))

def c27406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27406 : Upper (D 6) (R 6) [96,132,258,34,72,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,34,72,1] 13 (by decide) (choices 1) [1,4,16] r27406 c27406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8665
  · exact u8666
  · exact u8667

def b27407 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 134 262 42 88 36 81 145 273), lower := (rows 97 134 262 42 88 36 64 128 256), losses := [] }

theorem u27407 : Upper (D 6) (R 6) [96,132,258,34,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27408 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 262 42 88 48 69 133 261), lower := (rows 97 134 262 42 88 48 64 128 256), losses := [] }

theorem u27408 : Upper (D 6) (R 6) [96,132,258,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27408 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27409 : Route 9 := (fun mask => (mask,id))

def c27409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27409 : Upper (D 6) (R 6) [96,132,264,3,5,2] 13 := by
  apply FastRouting.sound _ _ [96,132,264,3,5,2] 13 (by decide) (choices 1) [16,32] r27409 c27409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8668
  · exact u8669

theorem m27410_2 : Upper (D 6) (R 6) [96,132,264,3,5,16,2] 13 :=
  permutation_upper _ _ _ [96,132,264,3,5,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8668

def r27410 : Route 9 := (fun mask => (mask,id))

def c27410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27410 : Upper (D 6) (R 6) [96,132,264,3,5,16] 13 := by
  apply FastRouting.sound _ _ [96,132,264,3,5,16] 13 (by decide) (choices 1) [2,32] r27410 c27410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m27410_2
  · exact u8670

def b27411 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 11 21 96 114 178 306), lower := (rows 97 134 268 11 21 96 64 128 256), losses := [] }

theorem u27411 : Upper (D 6) (R 6) [96,132,264,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27412 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 48, targets := 68 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(4,2),(4,6)], upper := (rows 97 134 268 11 50 33 84 212 340), lower := (rows 97 134 268 11 50 33 64 128 256), losses := [] }

theorem u27412 : Upper (D 6) (R 6) [96,132,264,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27413 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 65, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 97 134 268 11 50 36 81 209 337), lower := (rows 97 134 268 11 50 36 64 128 256), losses := [] }

theorem u27413 : Upper (D 6) (R 6) [96,132,264,3,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27414 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 268 11 50 48 69 197 325), lower := (rows 97 134 268 11 50 48 64 128 256), losses := [] }

theorem u27414 : Upper (D 6) (R 6) [96,132,264,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27414 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27415 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 11 50 96 85 149 277), lower := (rows 97 134 268 11 50 96 64 128 256), losses := [] }

theorem u27415 : Upper (D 6) (R 6) [96,132,264,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27416 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 194, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5)], upper := (rows 97 134 268 11 52 33 82 210 338), lower := (rows 97 134 268 11 52 33 64 128 256), losses := [] }

theorem u27416 : Upper (D 6) (R 6) [96,132,264,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27417 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(4,0),(4,6)], upper := (rows 97 134 268 11 52 34 81 209 337), lower := (rows 97 134 268 11 52 34 64 128 256), losses := [] }

theorem u27417 : Upper (D 6) (R 6) [96,132,264,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27418 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 268 11 52 48 67 195 323), lower := (rows 97 134 268 11 52 48 64 128 256), losses := [] }

theorem u27418 : Upper (D 6) (R 6) [96,132,264,3,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27418 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27419 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 11 52 96 83 147 275), lower := (rows 97 134 268 11 52 96 64 128 256), losses := [] }

theorem u27419 : Upper (D 6) (R 6) [96,132,264,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27419
end Delivery.IrregularNine14.P06
