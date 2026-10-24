import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0123
import IrregularNine14P07C0124

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23400 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 296 19 160 67 195 323), lower := (rows 37 74 148 296 19 160 64 128 256), losses := [] }

theorem u23400 : Upper (D 7) (R 7) [36,72,144,288,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23401 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 148 296 81 33 194 130 386), lower := (rows 37 74 148 296 81 33 64 128 256), losses := [] }

theorem u23401 : Upper (D 7) (R 7) [36,72,144,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23402 : Route 9 := (fun mask => (mask,id))

def c23402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23402 : Upper (D 7) (R 7) [36,72,144,288,65,2] 13 := by
  apply FastRouting.sound _ _ [36,72,144,288,65,2] 13 (by decide) (choices 1) [1,2,128] r23402 c23402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7423
  · exact u7424
  · exact u7425

def b23403 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 296 81 160 67 131 259), lower := (rows 37 74 148 296 81 160 64 128 256), losses := [] }

theorem u23403 : Upper (D 7) (R 7) [36,72,144,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23404 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 148 392 19 33 98 226 354), lower := (rows 37 74 148 392 19 33 64 128 256), losses := [] }

theorem u23404 : Upper (D 7) (R 7) [36,72,144,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23405 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(0,6),(0,7),(2,1),(3,1)], upper := (rows 37 74 148 392 19 34 97 225 353), lower := (rows 37 74 148 392 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 32 65 129 257), good := (rows 493 72 156 392 477 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 50 0 128 256), good := (rows 37 42 181 392 51 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 50 85 0 277), good := (rows 357 106 373 264 371 34 64 0 256) }] }

theorem u23405 : Upper (D 7) (R 7) [36,72,144,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23406 : Route 9 := (fun mask => (mask,id))

def c23406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23406 : Upper (D 7) (R 7) [36,72,144,384,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384,3,64] 13 (by decide) (choices 1) [1,2,32] r23406 c23406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7426
  · exact u7427
  · exact u7428

def b23407 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 148 392 50 33 67 195 323), lower := (rows 37 74 148 392 50 33 64 128 256), losses := [] }

theorem u23407 : Upper (D 7) (R 7) [36,72,144,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23408 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 148 392 50 34 65 193 321), lower := (rows 37 74 148 392 50 34 64 128 256), losses := [] }

theorem u23408 : Upper (D 7) (R 7) [36,72,144,384,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23409 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(3,6)], upper := (rows 37 74 148 392 50 96 67 131 259), lower := (rows 37 74 148 392 50 96 64 128 256), losses := [] }

theorem u23409 : Upper (D 7) (R 7) [36,72,144,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23410 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 148 392 81 33 98 162 290), lower := (rows 37 74 148 392 81 33 64 128 256), losses := [] }

theorem u23410 : Upper (D 7) (R 7) [36,72,144,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23411 : Route 9 := (fun mask => (mask,id))

def c23411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23411 : Upper (D 7) (R 7) [36,72,144,384,65,2] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384,65,2] 13 (by decide) (choices 1) [1,2,32] r23411 c23411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7429
  · exact u7430
  · exact u7431

def b23412 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 148 392 112 33 67 131 259), lower := (rows 37 74 148 392 112 33 64 128 256), losses := [] }

theorem u23412 : Upper (D 7) (R 7) [36,72,144,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23413 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 48, targets := 129 }], pairs := [(1,5),(3,5),(4,0),(4,7)], upper := (rows 37 74 148 392 112 34 67 131 259), lower := (rows 37 74 148 392 112 34 64 128 256), losses := [] }

theorem u23413 : Upper (D 7) (R 7) [36,72,144,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23414 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 196 168 19 33 338 402 274), lower := (rows 37 74 196 168 19 33 64 128 256), losses := [] }

theorem u23414 : Upper (D 7) (R 7) [36,72,192,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23415 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 4, region := 452, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 37 74 196 168 19 34 337 401 273), lower := (rows 37 74 196 168 19 34 64 128 256), losses := [] }

theorem u23415 : Upper (D 7) (R 7) [36,72,192,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m23416_1 : Upper (D 7) (R 7) [36,72,192,160,3,16,1] 13 :=
  permutation_upper _ _ _ [36,72,192,160,3,2,16] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7434

theorem m23416_2 : Upper (D 7) (R 7) [36,72,192,160,3,16,2] 13 :=
  permutation_upper _ _ _ [36,72,192,160,3,1,16] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7432

def r23416 : Route 9 := (fun mask => (mask,id))

def c23416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23416 : Upper (D 7) (R 7) [36,72,192,160,3,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,3,16] 13 (by decide) (choices 1) [1,2,256] r23416 c23416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m23416_1
  · exact m23416_2
  · exact u7436

theorem m23417_1 : Upper (D 7) (R 7) [36,72,192,160,3,256,1] 13 :=
  permutation_upper _ _ _ [36,72,192,160,3,2,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7435

theorem m23417_2 : Upper (D 7) (R 7) [36,72,192,160,3,256,2] 13 :=
  permutation_upper _ _ _ [36,72,192,160,3,1,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7433

theorem m23417_16 : Upper (D 7) (R 7) [36,72,192,160,3,256,16] 13 :=
  permutation_upper _ _ _ [36,72,192,160,3,16,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7436

def r23417 : Route 9 := (fun mask => (mask,id))

def c23417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23417 : Upper (D 7) (R 7) [36,72,192,160,3,256] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,3,256] 13 (by decide) (choices 1) [1,2,16] r23417 c23417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m23417_1
  · exact m23417_2
  · exact m23417_16

def b23418 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 196 168 273 33 82 146 274), lower := (rows 37 74 196 168 273 33 64 128 256), losses := [] }

theorem u23418 : Upper (D 7) (R 7) [36,72,192,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23419 : Route 9 := (fun mask => (mask,id))

def c23419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23419 : Upper (D 7) (R 7) [36,72,192,160,257,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,257,2] 13 (by decide) (choices 1) [1,2,16] r23419 c23419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7437
  · exact u7438
  · exact u7439

def r23420 : Route 9 := (fun mask => (mask,id))

def c23420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23420 : Upper (D 7) (R 7) [36,72,192,160,257,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,257,16] 13 (by decide) (choices 1) [1,2] r23420 c23420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7440
  · exact u7441

def r23421 : Route 9 := (fun mask => (mask,id))

def c23421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u23421 : Upper (D 7) (R 7) [36,72,192,257,3,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,3,2] 13 (by decide) (choices 1) [16,32,128] r23421 c23421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7442
  · exact u7443
  · exact u7444

def r23422 : Route 9 := (fun mask => (mask,id))

def c23422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23422 : Upper (D 7) (R 7) [36,72,192,257,3,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,3,16] 13 (by decide) (choices 1) [2,32,128] r23422 c23422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7445
  · exact u7446
  · exact u7447

def b23423 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 265 19 160 114 178 306), lower := (rows 37 74 196 265 19 160 64 128 256), losses := [] }

theorem u23423 : Upper (D 7) (R 7) [36,72,192,257,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23424 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 74 196 265 50 33 210 146 402), lower := (rows 37 74 196 265 50 33 64 128 256), losses := [] }

theorem u23424 : Upper (D 7) (R 7) [36,72,192,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23425 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 196 265 50 34 209 145 401), lower := (rows 37 74 196 265 50 34 64 128 256), losses := [] }

theorem u23425 : Upper (D 7) (R 7) [36,72,192,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23426 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 196 265 50 48 195 131 387), lower := (rows 37 74 196 265 50 48 64 128 256), losses := [] }

theorem u23426 : Upper (D 7) (R 7) [36,72,192,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23426 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23427 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 265 50 160 83 147 275), lower := (rows 37 74 196 265 50 160 64 128 256), losses := [] }

theorem u23427 : Upper (D 7) (R 7) [36,72,192,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23428 : Route 9 := (fun mask => (mask,id))

def c23428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23428 : Upper (D 7) (R 7) [36,72,192,257,129,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,129,2] 13 (by decide) (choices 1) [2,16,32] r23428 c23428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7448
  · exact u7449
  · exact u7450

def b23429 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 196 265 145 48 98 162 290), lower := (rows 37 74 196 265 145 48 64 128 256), losses := [] }

theorem u23429 : Upper (D 7) (R 7) [36,72,192,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23429 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23430 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 74 196 265 146 33 114 178 306), lower := (rows 37 74 196 265 146 33 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 18 45 0 130 258), good := (rows 37 442 165 297 402 33 0 128 256) }] }

theorem u23430 : Upper (D 7) (R 7) [36,72,192,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23431 : Route 9 := (fun mask => (mask,id))

def c23431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23431 : Upper (D 7) (R 7) [36,72,192,257,130,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,130,2] 13 (by decide) (choices 1) [1,16,32] r23431 c23431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7451
  · exact u7452
  · exact u7453

def r23432 : Route 9 := (fun mask => (mask,id))

def c23432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23432 : Upper (D 7) (R 7) [36,72,192,257,130,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,130,16] 13 (by decide) (choices 1) [1,2,32] r23432 c23432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7454
  · exact u7455
  · exact u7456

def b23433 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 196 265 176 33 82 146 274), lower := (rows 37 74 196 265 176 33 64 128 256), losses := [] }

theorem u23433 : Upper (D 7) (R 7) [36,72,192,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23434 : Route 9 := (fun mask => (mask,id))

def c23434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23434 : Upper (D 7) (R 7) [36,72,192,257,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,160,2] 13 (by decide) (choices 1) [1,2,16] r23434 c23434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7457
  · exact u7458
  · exact u7459

def b23435 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 196 265 176 48 67 131 259), lower := (rows 37 74 196 265 176 48 64 128 256), losses := [] }

theorem u23435 : Upper (D 7) (R 7) [36,72,192,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23435 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23436 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 228, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 196 266 19 33 240 176 432), lower := (rows 37 74 196 266 19 33 64 128 256), losses := [] }

theorem u23436 : Upper (D 7) (R 7) [36,72,192,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23437 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(2,1),(3,6)], upper := (rows 37 74 196 266 19 48 225 161 417), lower := (rows 37 74 196 266 19 48 64 128 256), losses := [] }

theorem u23437 : Upper (D 7) (R 7) [36,72,192,258,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23437 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23438 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 266 19 160 113 177 305), lower := (rows 37 74 196 266 19 160 64 128 256), losses := [] }

theorem u23438 : Upper (D 7) (R 7) [36,72,192,258,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23439 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 196 266 50 33 209 145 401), lower := (rows 37 74 196 266 50 33 64 128 256), losses := [] }

theorem u23439 : Upper (D 7) (R 7) [36,72,192,258,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23440 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 196 266 50 48 193 129 385), lower := (rows 37 74 196 266 50 48 64 128 256), losses := [] }

theorem u23440 : Upper (D 7) (R 7) [36,72,192,258,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23440 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23441 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 266 50 160 81 145 273), lower := (rows 37 74 196 266 50 160 64 128 256), losses := [] }

theorem u23441 : Upper (D 7) (R 7) [36,72,192,258,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23442 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 196 266 145 33 114 178 306), lower := (rows 37 74 196 266 145 33 64 128 256), losses := [] }

theorem u23442 : Upper (D 7) (R 7) [36,72,192,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23443 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(4,1)], upper := (rows 37 74 196 266 145 34 113 177 305), lower := (rows 37 74 196 266 145 34 64 128 256), losses := [] }

theorem u23443 : Upper (D 7) (R 7) [36,72,192,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23444 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 196 266 145 48 99 163 291), lower := (rows 37 74 196 266 145 48 64 128 256), losses := [] }

theorem u23444 : Upper (D 7) (R 7) [36,72,192,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23444 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23445 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 196 266 146 33 113 177 305), lower := (rows 37 74 196 266 146 33 64 128 256), losses := [] }

theorem u23445 : Upper (D 7) (R 7) [36,72,192,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23446 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 196 266 146 48 97 161 289), lower := (rows 37 74 196 266 146 48 64 128 256), losses := [] }

theorem u23446 : Upper (D 7) (R 7) [36,72,192,258,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23446 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23447 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 196 266 176 33 83 147 275), lower := (rows 37 74 196 266 176 33 64 128 256), losses := [] }

theorem u23447 : Upper (D 7) (R 7) [36,72,192,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23448 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 74 196 266 176 34 81 145 273), lower := (rows 37 74 196 266 176 34 64 128 256), losses := [] }

theorem u23448 : Upper (D 7) (R 7) [36,72,192,258,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23449 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 196 266 176 48 67 131 259), lower := (rows 37 74 196 266 176 48 64 128 256), losses := [] }

theorem u23449 : Upper (D 7) (R 7) [36,72,192,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23449 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23450 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 196 280 19 33 226 162 418), lower := (rows 37 74 196 280 19 33 64 128 256), losses := [] }

theorem u23450 : Upper (D 7) (R 7) [36,72,192,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23451 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 197, targets := 2 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(2,1),(3,1),(3,6)], upper := (rows 37 74 196 280 19 34 225 161 417), lower := (rows 37 74 196 280 19 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 53 24 16 32 97 161 289), good := (rows 485 72 196 284 477 485 64 128 256) }] }

theorem u23451 : Upper (D 7) (R 7) [36,72,192,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23452 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 280 19 160 99 163 291), lower := (rows 37 74 196 280 19 160 64 128 256), losses := [] }

theorem u23452 : Upper (D 7) (R 7) [36,72,192,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23453 : Route 9 := (fun mask => (mask,id))

def c23453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23453 : Upper (D 7) (R 7) [36,72,192,272,34,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,34,1] 13 (by decide) (choices 1) [1,2,128] r23453 c23453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7460
  · exact u7461
  · exact u7462

def b23454 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 196 280 50 34 193 129 385), lower := (rows 37 74 196 280 50 34 64 128 256), losses := [] }

theorem u23454 : Upper (D 7) (R 7) [36,72,192,272,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23455 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 280 50 160 67 131 259), lower := (rows 37 74 196 280 50 160 64 128 256), losses := [] }

theorem u23455 : Upper (D 7) (R 7) [36,72,192,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23456 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 196 280 145 33 98 162 290), lower := (rows 37 74 196 280 145 33 64 128 256), losses := [] }

theorem u23456 : Upper (D 7) (R 7) [36,72,192,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23457 : Route 9 := (fun mask => (mask,id))

def c23457 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23457 : Upper (D 7) (R 7) [36,72,192,272,129,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,129,2] 13 (by decide) (choices 1) [1,2,32] r23457 c23457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7463
  · exact u7464
  · exact u7465

def r23458 : Route 9 := (fun mask => (mask,id))

def c23458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23458 : Upper (D 7) (R 7) [36,72,192,272,130,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,130,1] 13 (by decide) (choices 1) [1,2,32] r23458 c23458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7466
  · exact u7467
  · exact u7468

def r23459 : Route 9 := (fun mask => (mask,id))

def c23459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23459 : Upper (D 7) (R 7) [36,72,192,272,130,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,130,2] 13 (by decide) (choices 1) [1,32] r23459 c23459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7469
  · exact u7470

#print axioms u23459
end Delivery.IrregularNine14.P07
