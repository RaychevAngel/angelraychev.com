import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0039
import IrregularNine14P07C0040

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14340 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 200 280 48 67 131 259), lower := (rows 7 98 164 200 280 48 64 128 256), losses := [] }

theorem u14340 : Upper (D 7) (R 7) [6,96,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14341 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 261 25 146 40 224 224 480), lower := (rows 7 98 261 25 146 40 64 128 256), losses := [] }

theorem u14341 : Upper (D 7) (R 7) [6,96,257,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14341 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14342 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 25 146 96 232 168 424), lower := (rows 7 98 261 25 146 96 64 128 256), losses := [] }

theorem u14342 : Upper (D 7) (R 7) [6,96,257,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14343_8 : Upper (D 7) (R 7) [6,96,257,17,130,128,8] 13 :=
  permutation_upper _ _ _ [6,96,257,17,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2397

theorem m14343_32 : Upper (D 7) (R 7) [6,96,257,17,130,128,32] 13 :=
  permutation_upper _ _ _ [6,96,257,17,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2398

def r14343 : Route 9 := (fun mask => (mask,id))

def c14343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14343 : Upper (D 7) (R 7) [6,96,257,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,17,130,128] 13 (by decide) (choices 1) [8,32] r14343 c14343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14343_8
  · exact m14343_32

def b14344 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(4,0)], upper := (rows 7 98 261 25 152 34 224 224 480), lower := (rows 7 98 261 25 152 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 13 17 32 98 162 290), good := (rows 477 480 285 29 152 480 64 128 256) }] }

theorem u14344 : Upper (D 7) (R 7) [6,96,257,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14345 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 25 152 96 226 162 418), lower := (rows 7 98 261 25 152 96 64 128 256), losses := [] }

theorem u14345 : Upper (D 7) (R 7) [6,96,257,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14346 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 261 25 152 160 98 226 354), lower := (rows 7 98 261 25 152 160 64 128 256), losses := [] }

theorem u14346 : Upper (D 7) (R 7) [6,96,257,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14347 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 452, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 7 98 261 25 176 34 200 200 456), lower := (rows 7 98 261 25 176 34 64 128 256), losses := [] }

theorem u14347 : Upper (D 7) (R 7) [6,96,257,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14348 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 261 25 176 40 194 194 450), lower := (rows 7 98 261 25 176 40 64 128 256), losses := [] }

theorem u14348 : Upper (D 7) (R 7) [6,96,257,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14348 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14349 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 25 176 96 202 138 394), lower := (rows 7 98 261 25 176 96 64 128 256), losses := [] }

theorem u14349 : Upper (D 7) (R 7) [6,96,257,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14350 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 261 25 176 160 74 202 330), lower := (rows 7 98 261 25 176 160 64 128 256), losses := [] }

theorem u14350 : Upper (D 7) (R 7) [6,96,257,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14351 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 98 261 26 145 40 224 224 480), lower := (rows 7 98 261 26 145 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 40 106 170 298), good := (rows 469 480 277 504 149 488 64 128 256) }] }

theorem u14351 : Upper (D 7) (R 7) [6,96,257,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14351 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14352 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 26 145 96 232 168 424), lower := (rows 7 98 261 26 145 96 64 128 256), losses := [] }

theorem u14352 : Upper (D 7) (R 7) [6,96,257,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14353_8 : Upper (D 7) (R 7) [6,96,257,18,129,128,8] 13 :=
  permutation_upper _ _ _ [6,96,257,18,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2399

theorem m14353_32 : Upper (D 7) (R 7) [6,96,257,18,129,128,32] 13 :=
  permutation_upper _ _ _ [6,96,257,18,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2400

def r14353 : Route 9 := (fun mask => (mask,id))

def c14353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14353 : Upper (D 7) (R 7) [6,96,257,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,18,129,128] 13 (by decide) (choices 1) [8,32] r14353 c14353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14353_8
  · exact m14353_32

def b14354 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 98 261 26 152 33 224 224 480), lower := (rows 7 98 261 26 152 33 64 128 256), losses := [] }

theorem u14354 : Upper (D 7) (R 7) [6,96,257,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14355 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 26 152 96 225 161 417), lower := (rows 7 98 261 26 152 96 64 128 256), losses := [] }

theorem u14355 : Upper (D 7) (R 7) [6,96,257,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14356 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 98 261 26 152 160 97 225 353), lower := (rows 7 98 261 26 152 160 64 128 256), losses := [] }

theorem u14356 : Upper (D 7) (R 7) [6,96,257,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14357 : PairBound 9 := { available := 200, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 98 261 26 176 33 200 200 456), lower := (rows 7 98 261 26 176 33 64 128 256), losses := [] }

theorem u14357 : Upper (D 7) (R 7) [6,96,257,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14358 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 98 261 26 176 40 193 193 449), lower := (rows 7 98 261 26 176 40 64 128 256), losses := [] }

theorem u14358 : Upper (D 7) (R 7) [6,96,257,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14358 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14359 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 26 176 96 201 137 393), lower := (rows 7 98 261 26 176 96 64 128 256), losses := [] }

theorem u14359 : Upper (D 7) (R 7) [6,96,257,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14360 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 261 26 176 160 73 201 329), lower := (rows 7 98 261 26 176 160 64 128 256), losses := [] }

theorem u14360 : Upper (D 7) (R 7) [6,96,257,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14361 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 261 41 88 34 208 144 400), lower := (rows 7 98 261 41 88 34 64 128 256), losses := [] }

theorem u14361 : Upper (D 7) (R 7) [6,96,257,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14362 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 41 88 48 194 130 386), lower := (rows 7 98 261 41 88 48 64 128 256), losses := [] }

theorem u14362 : Upper (D 7) (R 7) [6,96,257,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14362 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14363 : Route 9 := (fun mask => (mask,id))

def c14363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14363 : Upper (D 7) (R 7) [6,96,257,33,72,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,72,128] 13 (by decide) (choices 1) [2,16,128] r14363 c14363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2401
  · exact u2402
  · exact u2403

def b14364 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 261 41 146 40 208 208 464), lower := (rows 7 98 261 41 146 40 64 128 256), losses := [] }

theorem u14364 : Upper (D 7) (R 7) [6,96,257,33,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14364 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14365 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 3, region := 452, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 261 41 146 48 200 200 456), lower := (rows 7 98 261 41 146 48 64 128 256), losses := [] }

theorem u14365 : Upper (D 7) (R 7) [6,96,257,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14365 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14366 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 41 146 96 216 152 408), lower := (rows 7 98 261 41 146 96 64 128 256), losses := [] }

theorem u14366 : Upper (D 7) (R 7) [6,96,257,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14367 : Route 9 := (fun mask => (mask,id))

def c14367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14367 : Upper (D 7) (R 7) [6,96,257,33,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,130,128] 13 (by decide) (choices 1) [8,16] r14367 c14367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2404
  · exact u2405

def b14368 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 261 41 152 34 208 208 464), lower := (rows 7 98 261 41 152 34 64 128 256), losses := [] }

theorem u14368 : Upper (D 7) (R 7) [6,96,257,33,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14369 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 261 41 152 48 194 194 450), lower := (rows 7 98 261 41 152 48 64 128 256), losses := [] }

theorem u14369 : Upper (D 7) (R 7) [6,96,257,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14369 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14370 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 41 152 96 210 146 402), lower := (rows 7 98 261 41 152 96 64 128 256), losses := [] }

theorem u14370 : Upper (D 7) (R 7) [6,96,257,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14371 : Route 9 := (fun mask => (mask,id))

def c14371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14371 : Upper (D 7) (R 7) [6,96,257,33,136,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,136,128] 13 (by decide) (choices 1) [2,16] r14371 c14371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2406
  · exact u2407

def b14372 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 261 41 208 34 216 152 408), lower := (rows 7 98 261 41 208 34 64 128 256), losses := [] }

theorem u14372 : Upper (D 7) (R 7) [6,96,257,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14373 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 261 41 208 40 210 146 402), lower := (rows 7 98 261 41 208 40 64 128 256), losses := [] }

theorem u14373 : Upper (D 7) (R 7) [6,96,257,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14373 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14374 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 41 208 48 202 138 394), lower := (rows 7 98 261 41 208 48 64 128 256), losses := [] }

theorem u14374 : Upper (D 7) (R 7) [6,96,257,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14374 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14375 : Route 9 := (fun mask => (mask,id))

def c14375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14375 : Upper (D 7) (R 7) [6,96,257,33,192,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,192,128] 13 (by decide) (choices 1) [2,8,16] r14375 c14375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2408
  · exact u2409
  · exact u2410

def b14376 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,6)], upper := (rows 7 98 261 56 145 34 200 200 456), lower := (rows 7 98 261 56 145 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 39 34 293 56 185 34 0 128 256) }] }

theorem u14376 : Upper (D 7) (R 7) [6,96,257,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14377 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 56 145 40 194 194 450), lower := (rows 7 98 261 56 145 40 64 128 256), losses := [] }

theorem u14377 : Upper (D 7) (R 7) [6,96,257,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14377 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14378 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 56 145 96 202 138 394), lower := (rows 7 98 261 56 145 96 64 128 256), losses := [] }

theorem u14378 : Upper (D 7) (R 7) [6,96,257,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14379 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 261 56 145 160 74 202 330), lower := (rows 7 98 261 56 145 160 64 128 256), losses := [] }

theorem u14379 : Upper (D 7) (R 7) [6,96,257,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14380 : Route 9 := (fun mask => (mask,id))

def c14380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14380 : Upper (D 7) (R 7) [6,96,257,48,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,130,1] 13 (by decide) (choices 1) [8,128] r14380 c14380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2411
  · exact u2412

def b14381 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 98 261 56 146 40 193 193 449), lower := (rows 7 98 261 56 146 40 64 128 256), losses := [] }

theorem u14381 : Upper (D 7) (R 7) [6,96,257,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14381 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14382 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 56 146 96 201 137 393), lower := (rows 7 98 261 56 146 96 64 128 256), losses := [] }

theorem u14382 : Upper (D 7) (R 7) [6,96,257,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14383 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 98 261 56 146 160 73 201 329), lower := (rows 7 98 261 56 146 160 64 128 256), losses := [] }

theorem u14383 : Upper (D 7) (R 7) [6,96,257,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14384 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 98 261 56 152 33 194 194 450), lower := (rows 7 98 261 56 152 33 64 128 256), losses := [] }

theorem u14384 : Upper (D 7) (R 7) [6,96,257,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14385 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 7 98 261 56 152 34 193 193 449), lower := (rows 7 98 261 56 152 34 64 128 256), losses := [] }

theorem u14385 : Upper (D 7) (R 7) [6,96,257,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14386 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 56 152 96 195 131 387), lower := (rows 7 98 261 56 152 96 64 128 256), losses := [] }

theorem u14386 : Upper (D 7) (R 7) [6,96,257,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14387 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 7 98 261 56 152 160 67 195 323), lower := (rows 7 98 261 56 152 160 64 128 256), losses := [] }

theorem u14387 : Upper (D 7) (R 7) [6,96,257,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14388 : Route 9 := (fun mask => (mask,id))

def c14388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14388 : Upper (D 7) (R 7) [6,96,257,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,192,1] 13 (by decide) (choices 1) [2,8,128] r14388 c14388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2413
  · exact u2414
  · exact u2415

def b14389 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 261 56 208 34 201 137 393), lower := (rows 7 98 261 56 208 34 64 128 256), losses := [] }

theorem u14389 : Upper (D 7) (R 7) [6,96,257,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14390 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 261 56 208 40 195 131 387), lower := (rows 7 98 261 56 208 40 64 128 256), losses := [] }

theorem u14390 : Upper (D 7) (R 7) [6,96,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14390 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14391 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 261 56 208 160 75 139 267), lower := (rows 7 98 261 56 208 160 64 128 256), losses := [] }

theorem u14391 : Upper (D 7) (R 7) [6,96,257,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14392 : Route 9 := (fun mask => (mask,id))

def c14392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14392 : Upper (D 7) (R 7) [6,96,257,129,130,8] 13 := by
  apply FastRouting.sound _ _ [6,96,257,129,130,8] 13 (by decide) (choices 1) [16,32] r14392 c14392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2416
  · exact u2417

theorem m14393_8 : Upper (D 7) (R 7) [6,96,257,129,130,16,8] 13 :=
  permutation_upper _ _ _ [6,96,257,129,130,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2416

def r14393 : Route 9 := (fun mask => (mask,id))

def c14393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14393 : Upper (D 7) (R 7) [6,96,257,129,130,16] 13 := by
  apply FastRouting.sound _ _ [6,96,257,129,130,16] 13 (by decide) (choices 1) [8,32] r14393 c14393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14393_8
  · exact u2418

def b14394 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 137 146 96 120 184 312), lower := (rows 7 98 261 137 146 96 64 128 256), losses := [] }

theorem u14394 : Upper (D 7) (R 7) [6,96,257,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14395 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,6)], upper := (rows 7 98 261 137 176 34 88 216 344), lower := (rows 7 98 261 137 176 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 24 35 0 128 256), good := (rows 39 34 293 185 176 34 0 128 256) }] }

theorem u14395 : Upper (D 7) (R 7) [6,96,257,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14396 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 261 137 176 40 82 210 338), lower := (rows 7 98 261 137 176 40 64 128 256), losses := [] }

theorem u14396 : Upper (D 7) (R 7) [6,96,257,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14396 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14397 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 261 137 176 48 74 202 330), lower := (rows 7 98 261 137 176 48 64 128 256), losses := [] }

theorem u14397 : Upper (D 7) (R 7) [6,96,257,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14397 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14398 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 137 176 96 90 154 282), lower := (rows 7 98 261 137 176 96 64 128 256), losses := [] }

theorem u14398 : Upper (D 7) (R 7) [6,96,257,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14399 : Route 9 := (fun mask => (mask,id))

def c14399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14399 : Upper (D 7) (R 7) [6,96,257,130,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,257,130,160,1] 13 (by decide) (choices 1) [8,16] r14399 c14399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2419
  · exact u2420

#print axioms u14399
end Delivery.IrregularNine14.P07
