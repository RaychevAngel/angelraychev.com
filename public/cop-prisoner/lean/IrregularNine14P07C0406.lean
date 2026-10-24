import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0133
import IrregularNine14P07C0134

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24360 : Route 9 := (fun mask => (mask,id))

def c24360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24360 : Upper (D 7) (R 7) [36,96,136,258,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,130,16] 13 (by decide) (choices 1) [1] r24360 c24360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u8023

def b24361 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 266 146 96 81 145 273), lower := (rows 37 98 140 266 146 96 64 128 256), losses := [] }

theorem u24361 : Upper (D 7) (R 7) [36,96,136,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24362 : Route 9 := (fun mask => (mask,id))

def c24362 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24362 : Upper (D 7) (R 7) [36,96,136,258,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,192,1] 13 (by decide) (choices 1) [1,2,16] r24362 c24362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8024
  · exact u8025
  · exact u8026

def b24363 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 140 266 208 34 81 145 273), lower := (rows 37 98 140 266 208 34 64 128 256), losses := [] }

theorem u24363 : Upper (D 7) (R 7) [36,96,136,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24364 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 266 208 48 67 131 259), lower := (rows 37 98 140 266 208 48 64 128 256), losses := [] }

theorem u24364 : Upper (D 7) (R 7) [36,96,136,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24364 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24365 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 280 19 33 194 194 450), lower := (rows 37 98 140 280 19 33 64 128 256), losses := [] }

theorem u24365 : Upper (D 7) (R 7) [36,96,136,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24366 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 140 280 19 34 193 193 449), lower := (rows 37 98 140 280 19 34 64 128 256), losses := [] }

theorem u24366 : Upper (D 7) (R 7) [36,96,136,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24367 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 280 19 96 195 131 387), lower := (rows 37 98 140 280 19 96 64 128 256), losses := [] }

theorem u24367 : Upper (D 7) (R 7) [36,96,136,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24368 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 280 19 160 67 195 323), lower := (rows 37 98 140 280 19 160 64 128 256), losses := [] }

theorem u24368 : Upper (D 7) (R 7) [36,96,136,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24369 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 280 81 33 194 130 386), lower := (rows 37 98 140 280 81 33 64 128 256), losses := [] }

theorem u24369 : Upper (D 7) (R 7) [36,96,136,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24370 : Route 9 := (fun mask => (mask,id))

def c24370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24370 : Upper (D 7) (R 7) [36,96,136,272,65,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,65,2] 13 (by decide) (choices 1) [1,2,128] r24370 c24370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8027
  · exact u8028
  · exact u8029

def b24371 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 280 81 160 67 131 259), lower := (rows 37 98 140 280 81 160 64 128 256), losses := [] }

theorem u24371 : Upper (D 7) (R 7) [36,96,136,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24372 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 140 280 145 33 66 194 322), lower := (rows 37 98 140 280 145 33 64 128 256), losses := [] }

theorem u24372 : Upper (D 7) (R 7) [36,96,136,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24373 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 362, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 280 145 34 67 195 323), lower := (rows 37 98 140 280 145 34 64 128 256), losses := [] }

theorem u24373 : Upper (D 7) (R 7) [36,96,136,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24374 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 280 145 96 67 131 259), lower := (rows 37 98 140 280 145 96 64 128 256), losses := [] }

theorem u24374 : Upper (D 7) (R 7) [36,96,136,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24375 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 280 146 33 67 195 323), lower := (rows 37 98 140 280 146 33 64 128 256), losses := [] }

theorem u24375 : Upper (D 7) (R 7) [36,96,136,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24376 : Route 9 := (fun mask => (mask,id))

def c24376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24376 : Upper (D 7) (R 7) [36,96,136,272,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,130,2] 13 (by decide) (choices 1) [1] r24376 c24376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u8030

def b24377 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 280 146 96 67 131 259), lower := (rows 37 98 140 280 146 96 64 128 256), losses := [] }

theorem u24377 : Upper (D 7) (R 7) [36,96,136,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24378 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 280 208 33 67 131 259), lower := (rows 37 98 140 280 208 33 64 128 256), losses := [] }

theorem u24378 : Upper (D 7) (R 7) [36,96,136,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24379 : Route 9 := (fun mask => (mask,id))

def c24379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24379 : Upper (D 7) (R 7) [36,96,136,272,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,192,2] 13 (by decide) (choices 1) [1,2] r24379 c24379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8031
  · exact u8032

def b24380 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 328 19 33 210 146 402), lower := (rows 37 98 140 328 19 33 64 128 256), losses := [] }

theorem u24380 : Upper (D 7) (R 7) [36,96,136,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24381 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 140 328 19 34 209 145 401), lower := (rows 37 98 140 328 19 34 64 128 256), losses := [] }

theorem u24381 : Upper (D 7) (R 7) [36,96,136,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24382 : Route 9 := (fun mask => (mask,id))

def c24382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24382 : Upper (D 7) (R 7) [36,96,136,320,3,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,3,16] 13 (by decide) (choices 1) [1,2,128] r24382 c24382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8033
  · exact u8034
  · exact u8035

def b24383 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 328 19 160 83 147 275), lower := (rows 37 98 140 328 19 160 64 128 256), losses := [] }

theorem u24383 : Upper (D 7) (R 7) [36,96,136,320,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24384 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 140 328 145 33 82 146 274), lower := (rows 37 98 140 328 145 33 64 128 256), losses := [] }

theorem u24384 : Upper (D 7) (R 7) [36,96,136,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24385 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 328 145 34 83 147 275), lower := (rows 37 98 140 328 145 34 64 128 256), losses := [{ target := 7, region := (rows 5 90 4 24 16 126 80 0 272), good := (rows 37 98 47 362 379 34 98 0 256) }] }

theorem u24385 : Upper (D 7) (R 7) [36,96,136,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24386 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 140 328 145 48 67 131 259), lower := (rows 37 98 140 328 145 48 64 128 256), losses := [] }

theorem u24386 : Upper (D 7) (R 7) [36,96,136,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24386 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24387 : Route 9 := (fun mask => (mask,id))

def c24387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24387 : Upper (D 7) (R 7) [36,96,136,320,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,130,1] 13 (by decide) (choices 1) [1,2,16] r24387 c24387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8036
  · exact u8037
  · exact u8038

def b24388 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 328 146 34 81 145 273), lower := (rows 37 98 140 328 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 4 8 20 126 64 128 256), good := (rows 52 98 190 362 178 34 98 128 256) },{ target := 7, region := (rows 5 74 4 8 16 126 64 0 256), good := (rows 37 98 47 362 50 34 98 0 256) }] }

theorem u24388 : Upper (D 7) (R 7) [36,96,136,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24389 : Route 9 := (fun mask => (mask,id))

def c24389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24389 : Upper (D 7) (R 7) [36,96,136,320,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,130,16] 13 (by decide) (choices 1) [1,2] r24389 c24389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8039
  · exact u8040

def b24390 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 196 11 146 33 344 408 280), lower := (rows 37 98 196 11 146 33 64 128 256), losses := [] }

theorem u24390 : Upper (D 7) (R 7) [36,96,192,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24391 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 11 146 40 337 401 273), lower := (rows 37 98 196 11 146 40 64 128 256), losses := [] }

theorem u24391 : Upper (D 7) (R 7) [36,96,192,3,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24391 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24392 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 196 11 146 48 329 393 265), lower := (rows 37 98 196 11 146 48 64 128 256), losses := [] }

theorem u24392 : Upper (D 7) (R 7) [36,96,192,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24393 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 144, targets := 64 }], pairs := [(2,5),(4,5),(4,6)], upper := (rows 37 98 196 11 146 288 89 153 281), lower := (rows 37 98 196 11 146 288 64 128 256), losses := [] }

theorem u24393 : Upper (D 7) (R 7) [36,96,192,3,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24393 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24394 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 196 11 152 33 338 402 274), lower := (rows 37 98 196 11 152 33 64 128 256), losses := [] }

theorem u24394 : Upper (D 7) (R 7) [36,96,192,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24395 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 196 11 152 34 337 401 273), lower := (rows 37 98 196 11 152 34 64 128 256), losses := [] }

theorem u24395 : Upper (D 7) (R 7) [36,96,192,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24396 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 196 11 152 48 323 387 259), lower := (rows 37 98 196 11 152 48 64 128 256), losses := [] }

theorem u24396 : Upper (D 7) (R 7) [36,96,192,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24396 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24397 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 144, targets := 64 }], pairs := [(2,5),(4,5),(4,6)], upper := (rows 37 98 196 11 152 288 83 147 275), lower := (rows 37 98 196 11 152 288 64 128 256), losses := [] }

theorem u24397 : Upper (D 7) (R 7) [36,96,192,3,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24397 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24398 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 196 11 273 34 216 152 408), lower := (rows 37 98 196 11 273 34 64 128 256), losses := [] }

theorem u24398 : Upper (D 7) (R 7) [36,96,192,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24399 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 11 273 40 210 146 402), lower := (rows 37 98 196 11 273 40 64 128 256), losses := [] }

theorem u24399 : Upper (D 7) (R 7) [36,96,192,3,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24399 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24400 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 37 98 196 11 273 48 202 138 394), lower := (rows 37 98 196 11 273 48 64 128 256), losses := [] }

theorem u24400 : Upper (D 7) (R 7) [36,96,192,3,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24400 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24401 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 11 273 160 90 154 282), lower := (rows 37 98 196 11 273 160 64 128 256), losses := [] }

theorem u24401 : Upper (D 7) (R 7) [36,96,192,3,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24402 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 196 11 274 33 216 152 408), lower := (rows 37 98 196 11 274 33 64 128 256), losses := [] }

theorem u24402 : Upper (D 7) (R 7) [36,96,192,3,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24403 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 11 274 40 209 145 401), lower := (rows 37 98 196 11 274 40 64 128 256), losses := [] }

theorem u24403 : Upper (D 7) (R 7) [36,96,192,3,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24403 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24404 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 37 98 196 11 274 48 201 137 393), lower := (rows 37 98 196 11 274 48 64 128 256), losses := [] }

theorem u24404 : Upper (D 7) (R 7) [36,96,192,3,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24404 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24405 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 11 274 160 89 153 281), lower := (rows 37 98 196 11 274 160 64 128 256), losses := [] }

theorem u24405 : Upper (D 7) (R 7) [36,96,192,3,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24406 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 196 11 280 33 210 146 402), lower := (rows 37 98 196 11 280 33 64 128 256), losses := [] }

theorem u24406 : Upper (D 7) (R 7) [36,96,192,3,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24407 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 196 11 280 34 209 145 401), lower := (rows 37 98 196 11 280 34 64 128 256), losses := [] }

theorem u24407 : Upper (D 7) (R 7) [36,96,192,3,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24408 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 400, targets := 64 }], pairs := [(2,5),(4,5),(4,6)], upper := (rows 37 98 196 11 280 48 195 131 387), lower := (rows 37 98 196 11 280 48 64 128 256), losses := [] }

theorem u24408 : Upper (D 7) (R 7) [36,96,192,3,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24409 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 11 280 160 83 147 275), lower := (rows 37 98 196 11 280 160 64 128 256), losses := [] }

theorem u24409 : Upper (D 7) (R 7) [36,96,192,3,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24410 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 196 11 400 33 90 154 282), lower := (rows 37 98 196 11 400 33 64 128 256), losses := [] }

theorem u24410 : Upper (D 7) (R 7) [36,96,192,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24411 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 196 11 400 34 89 153 281), lower := (rows 37 98 196 11 400 34 64 128 256), losses := [] }

theorem u24411 : Upper (D 7) (R 7) [36,96,192,3,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24412 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 11 400 40 83 147 275), lower := (rows 37 98 196 11 400 40 64 128 256), losses := [] }

theorem u24412 : Upper (D 7) (R 7) [36,96,192,3,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24412 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24413 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 196 11 400 48 75 139 267), lower := (rows 37 98 196 11 400 48 64 128 256), losses := [] }

theorem u24413 : Upper (D 7) (R 7) [36,96,192,3,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24413 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24414 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 26 33 450 386 386), lower := (rows 37 98 196 25 26 33 64 128 256), losses := [] }

theorem u24414 : Upper (D 7) (R 7) [36,96,192,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24415 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 26 34 449 385 385), lower := (rows 37 98 196 25 26 34 64 128 256), losses := [] }

theorem u24415 : Upper (D 7) (R 7) [36,96,192,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24416 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 26 160 323 387 259), lower := (rows 37 98 196 25 26 160 64 128 256), losses := [] }

theorem u24416 : Upper (D 7) (R 7) [36,96,192,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24417 : Route 9 := (fun mask => (mask,id))

def c24417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24417 : Upper (D 7) (R 7) [36,96,192,17,10,256] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,10,256] 13 (by decide) (choices 1) [1,2,128] r24417 c24417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8041
  · exact u8042
  · exact u8043

def b24418 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 25 146 33 330 394 266), lower := (rows 37 98 196 25 146 33 64 128 256), losses := [] }

theorem u24418 : Upper (D 7) (R 7) [36,96,192,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24419 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 196 25 146 34 329 393 265), lower := (rows 37 98 196 25 146 34 64 128 256), losses := [] }

theorem u24419 : Upper (D 7) (R 7) [36,96,192,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24419
end Delivery.IrregularNine14.P07
