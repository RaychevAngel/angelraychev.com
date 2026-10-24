import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0112

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22380 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 35 131 261 28 88 36 98 226 354), lower := (rows 35 131 261 28 88 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 21 44 65 129 257), good := (rows 506 466 508 60 120 60 64 128 256) }] }

theorem u22380 : Upper (D 6) (R 6) [34,129,257,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22381 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 28 88 96 102 166 294), lower := (rows 35 131 261 28 88 96 64 128 256), losses := [] }

theorem u22381 : Upper (D 6) (R 6) [34,129,257,20,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22382 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 28 112 34 76 204 332), lower := (rows 35 131 261 28 112 34 64 128 256), losses := [] }

theorem u22382 : Upper (D 6) (R 6) [34,129,257,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22383 : Route 9 := (fun mask => (mask,id))

def c22383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22383 : Upper (D 6) (R 6) [34,129,257,20,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,96,4] 13 (by decide) (choices 1) [2,8] r22383 c22383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6724
  · exact u6725

def b22384 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 28 112 40 70 198 326), lower := (rows 35 131 261 28 112 40 64 128 256), losses := [] }

theorem u22384 : Upper (D 6) (R 6) [34,129,257,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22384 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22385 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 28 112 96 78 142 270), lower := (rows 35 131 261 28 112 96 64 128 256), losses := [] }

theorem u22385 : Upper (D 6) (R 6) [34,129,257,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22386 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 261 44 82 36 88 216 344), lower := (rows 35 131 261 44 82 36 64 128 256), losses := [] }

theorem u22386 : Upper (D 6) (R 6) [34,129,257,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22387 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 44 82 40 84 212 340), lower := (rows 35 131 261 44 82 40 64 128 256), losses := [] }

theorem u22387 : Upper (D 6) (R 6) [34,129,257,36,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22387 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22388 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 261 44 82 48 76 204 332), lower := (rows 35 131 261 44 82 48 64 128 256), losses := [] }

theorem u22388 : Upper (D 6) (R 6) [34,129,257,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22388 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22389 : Route 9 := (fun mask => (mask,id))

def c22389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22389 : Upper (D 6) (R 6) [34,129,257,36,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36,66,64] 13 (by decide) (choices 1) [4,8,16] r22389 c22389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6726
  · exact u6727
  · exact u6728

def b22390 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 44 84 34 88 216 344), lower := (rows 35 131 261 44 84 34 64 128 256), losses := [] }

theorem u22390 : Upper (D 6) (R 6) [34,129,257,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22391 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 44 84 40 82 210 338), lower := (rows 35 131 261 44 84 40 64 128 256), losses := [] }

theorem u22391 : Upper (D 6) (R 6) [34,129,257,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22391 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22392 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 44 84 48 74 202 330), lower := (rows 35 131 261 44 84 48 64 128 256), losses := [] }

theorem u22392 : Upper (D 6) (R 6) [34,129,257,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22392 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22393 : Route 9 := (fun mask => (mask,id))

def c22393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22393 : Upper (D 6) (R 6) [34,129,257,36,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36,68,64] 13 (by decide) (choices 1) [2,8,16] r22393 c22393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6729
  · exact u6730
  · exact u6731

def b22394 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 44 88 34 84 212 340), lower := (rows 35 131 261 44 88 34 64 128 256), losses := [] }

theorem u22394 : Upper (D 6) (R 6) [34,129,257,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22395 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 261 44 88 36 82 210 338), lower := (rows 35 131 261 44 88 36 64 128 256), losses := [] }

theorem u22395 : Upper (D 6) (R 6) [34,129,257,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22396 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 44 88 48 70 198 326), lower := (rows 35 131 261 44 88 48 64 128 256), losses := [] }

theorem u22396 : Upper (D 6) (R 6) [34,129,257,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22396 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22397 : Route 9 := (fun mask => (mask,id))

def c22397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22397 : Upper (D 6) (R 6) [34,129,257,36,72,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36,72,64] 13 (by decide) (choices 1) [2,4,16] r22397 c22397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6732
  · exact u6733
  · exact u6734

def r22398 : Route 9 := (fun mask => (mask,id))

def c22398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22398 : Upper (D 6) (R 6) [34,129,257,48,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,48,66,4] 13 (by decide) (choices 1) [4,8] r22398 c22398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6735
  · exact u6736

def b22399 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 261 56 82 40 68 196 324), lower := (rows 35 131 261 56 82 40 64 128 256), losses := [] }

theorem u22399 : Upper (D 6) (R 6) [34,129,257,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22399 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22400 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 56 82 96 76 140 268), lower := (rows 35 131 261 56 82 96 64 128 256), losses := [] }

theorem u22400 : Upper (D 6) (R 6) [34,129,257,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22401 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 56 84 34 76 204 332), lower := (rows 35 131 261 56 84 34 64 128 256), losses := [] }

theorem u22401 : Upper (D 6) (R 6) [34,129,257,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22402 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 261 56 84 36 74 202 330), lower := (rows 35 131 261 56 84 36 64 128 256), losses := [] }

theorem u22402 : Upper (D 6) (R 6) [34,129,257,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22403 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 56 84 40 70 198 326), lower := (rows 35 131 261 56 84 40 64 128 256), losses := [] }

theorem u22403 : Upper (D 6) (R 6) [34,129,257,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22403 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22404 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 56 84 96 78 142 270), lower := (rows 35 131 261 56 84 96 64 128 256), losses := [] }

theorem u22404 : Upper (D 6) (R 6) [34,129,257,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22405 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 56 88 34 68 196 324), lower := (rows 35 131 261 56 88 34 64 128 256), losses := [] }

theorem u22405 : Upper (D 6) (R 6) [34,129,257,48,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22406 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 131 261 56 88 36 70 198 326), lower := (rows 35 131 261 56 88 36 64 128 256), losses := [{ target := 5, region := (rows 1 7 7 8 24 0 103 167 295), good := (rows 455 455 455 472 88 454 64 128 256) }] }

theorem u22406 : Upper (D 6) (R 6) [34,129,257,48,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22407 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 261 56 88 96 70 134 262), lower := (rows 35 131 261 56 88 96 64 128 256), losses := [] }

theorem u22407 : Upper (D 6) (R 6) [34,129,257,48,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22408 : Route 9 := (fun mask => (mask,id))

def c22408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22408 : Upper (D 6) (R 6) [34,129,257,66,68,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,66,68,4] 13 (by decide) (choices 1) [8,16,32] r22408 c22408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6737
  · exact u6738
  · exact u6739

def b22409 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 74 84 40 116 180 308), lower := (rows 35 131 261 74 84 40 64 128 256), losses := [] }

theorem u22409 : Upper (D 6) (R 6) [34,129,257,66,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22409 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22410 : Route 9 := (fun mask => (mask,id))

def c22410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22410 : Upper (D 6) (R 6) [34,129,257,66,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,257,66,68,16] 13 (by decide) (choices 1) [4,8,32] r22410 c22410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6740
  · exact u6741
  · exact u6742

def r22411 : Route 9 := (fun mask => (mask,id))

def c22411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22411 : Upper (D 6) (R 6) [34,129,257,66,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,66,96,4] 13 (by decide) (choices 1) [4,8,16] r22411 c22411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6743
  · exact u6744
  · exact u6745

def b22412 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 74 112 40 84 148 276), lower := (rows 35 131 261 74 112 40 64 128 256), losses := [] }

theorem u22412 : Upper (D 6) (R 6) [34,129,257,66,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22412 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22413 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 74 112 48 76 140 268), lower := (rows 35 131 261 74 112 48 64 128 256), losses := [] }

theorem u22413 : Upper (D 6) (R 6) [34,129,257,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22413 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22414 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 76 112 34 92 156 284), lower := (rows 35 131 261 76 112 34 64 128 256), losses := [] }

theorem u22414 : Upper (D 6) (R 6) [34,129,257,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22415 : Route 9 := (fun mask => (mask,id))

def c22415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22415 : Upper (D 6) (R 6) [34,129,257,68,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,68,96,4] 13 (by decide) (choices 1) [2,8,16] r22415 c22415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6746
  · exact u6747
  · exact u6748

def b22416 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 76 112 40 86 150 278), lower := (rows 35 131 261 76 112 40 64 128 256), losses := [] }

theorem u22416 : Upper (D 6) (R 6) [34,129,257,68,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22416 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22417 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 76 112 48 78 142 270), lower := (rows 35 131 261 76 112 48 64 128 256), losses := [] }

theorem u22417 : Upper (D 6) (R 6) [34,129,257,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22417 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22418 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 131 262 13 52 40 80 208 336), lower := (rows 35 131 262 13 52 40 64 128 256), losses := [] }

theorem u22418 : Upper (D 6) (R 6) [34,129,258,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22418 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22419 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 13 52 48 72 200 328), lower := (rows 35 131 262 13 52 48 64 128 256), losses := [] }

theorem u22419 : Upper (D 6) (R 6) [34,129,258,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22419 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22420 : Route 9 := (fun mask => (mask,id))

def c22420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22420 : Upper (D 6) (R 6) [34,129,258,5,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,36,64] 13 (by decide) (choices 1) [8,16] r22420 c22420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6749
  · exact u6750

def b22421 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 131 262 13 56 36 80 208 336), lower := (rows 35 131 262 13 56 36 64 128 256), losses := [] }

theorem u22421 : Upper (D 6) (R 6) [34,129,258,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22422 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 13 56 48 68 196 324), lower := (rows 35 131 262 13 56 48 64 128 256), losses := [] }

theorem u22422 : Upper (D 6) (R 6) [34,129,258,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22422 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22423 : Route 9 := (fun mask => (mask,id))

def c22423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22423 : Upper (D 6) (R 6) [34,129,258,5,40,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,40,64] 13 (by decide) (choices 1) [4,16] r22423 c22423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6751
  · exact u6752

def b22424 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 262 13 84 40 112 240 368), lower := (rows 35 131 262 13 84 40 64 128 256), losses := [] }

theorem u22424 : Upper (D 6) (R 6) [34,129,258,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22424 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22425 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 13 84 48 104 232 360), lower := (rows 35 131 262 13 84 48 64 128 256), losses := [] }

theorem u22425 : Upper (D 6) (R 6) [34,129,258,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22425 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22426 : Route 9 := (fun mask => (mask,id))

def c22426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22426 : Upper (D 6) (R 6) [34,129,258,5,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,68,64] 13 (by decide) (choices 1) [8,16,32] r22426 c22426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6753
  · exact u6754
  · exact u6755

def b22427 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 131 262 13 88 36 112 240 368), lower := (rows 35 131 262 13 88 36 64 128 256), losses := [] }

theorem u22427 : Upper (D 6) (R 6) [34,129,258,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22428 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 13 88 48 100 228 356), lower := (rows 35 131 262 13 88 48 64 128 256), losses := [] }

theorem u22428 : Upper (D 6) (R 6) [34,129,258,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22428 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22429 : Route 9 := (fun mask => (mask,id))

def c22429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22429 : Upper (D 6) (R 6) [34,129,258,5,72,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,72,64] 13 (by decide) (choices 1) [4,16,32] r22429 c22429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6756
  · exact u6757
  · exact u6758

def b22430 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 131 262 13 112 36 88 216 344), lower := (rows 35 131 262 13 112 36 64 128 256), losses := [] }

theorem u22430 : Upper (D 6) (R 6) [34,129,258,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22431 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 262 13 112 40 84 212 340), lower := (rows 35 131 262 13 112 40 64 128 256), losses := [] }

theorem u22431 : Upper (D 6) (R 6) [34,129,258,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22431 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22432 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 13 112 48 76 204 332), lower := (rows 35 131 262 13 112 48 64 128 256), losses := [] }

theorem u22432 : Upper (D 6) (R 6) [34,129,258,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22432 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22433 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 13 112 96 92 156 284), lower := (rows 35 131 262 13 112 96 64 128 256), losses := [] }

theorem u22433 : Upper (D 6) (R 6) [34,129,258,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22434 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 131 262 25 28 36 96 224 352), lower := (rows 35 131 262 25 28 36 64 128 256), losses := [] }

theorem u22434 : Upper (D 6) (R 6) [34,129,258,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22435 : Route 9 := (fun mask => (mask,id))

def c22435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22435 : Upper (D 6) (R 6) [34,129,258,17,12,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,12,64] 13 (by decide) (choices 1) [4,32] r22435 c22435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6759
  · exact u6760

def b22436 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 131 262 25 52 36 72 200 328), lower := (rows 35 131 262 25 52 36 64 128 256), losses := [] }

theorem u22436 : Upper (D 6) (R 6) [34,129,258,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22437 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 131 262 25 52 40 68 196 324), lower := (rows 35 131 262 25 52 40 64 128 256), losses := [] }

theorem u22437 : Upper (D 6) (R 6) [34,129,258,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22437 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22438 : Route 9 := (fun mask => (mask,id))

def c22438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22438 : Upper (D 6) (R 6) [34,129,258,17,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,36,64] 13 (by decide) (choices 1) [4,8] r22438 c22438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6761
  · exact u6762

def r22439 : Route 9 := (fun mask => (mask,id))

def c22439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22439 : Upper (D 6) (R 6) [34,129,258,17,68,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,68,4] 13 (by decide) (choices 1) [8,32] r22439 c22439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6763
  · exact u6764

#print axioms u22439
end Delivery.IrregularNine14.P06
