import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0083

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18480 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 392 148 34 81 209 337), lower := (rows 35 67 44 392 148 34 64 128 256), losses := [] }

theorem u18480 : Upper (D 7) (R 7) [34,65,40,384,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18481 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 392 148 48 67 195 323), lower := (rows 35 67 44 392 148 48 64 128 256), losses := [] }

theorem u18481 : Upper (D 7) (R 7) [34,65,40,384,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18481 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18482 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 392 148 96 83 147 275), lower := (rows 35 67 44 392 148 96 64 128 256), losses := [] }

theorem u18482 : Upper (D 7) (R 7) [34,65,40,384,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18483 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 392 208 33 86 150 278), lower := (rows 35 67 44 392 208 33 64 128 256), losses := [] }

theorem u18483 : Upper (D 7) (R 7) [34,65,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18484 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 392 208 34 85 149 277), lower := (rows 35 67 44 392 208 34 64 128 256), losses := [] }

theorem u18484 : Upper (D 7) (R 7) [34,65,40,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18485 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 392 208 36 83 147 275), lower := (rows 35 67 44 392 208 36 64 128 256), losses := [] }

theorem u18485 : Upper (D 7) (R 7) [34,65,40,384,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18485 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18486 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 392 208 48 71 135 263), lower := (rows 35 67 44 392 208 48 64 128 256), losses := [] }

theorem u18486 : Upper (D 7) (R 7) [34,65,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18486 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18487 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 137 146 36 344 408 280), lower := (rows 35 67 100 137 146 36 64 128 256), losses := [] }

theorem u18487 : Upper (D 7) (R 7) [34,65,96,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18487 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18488 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(4,0)], upper := (rows 35 67 100 137 146 40 340 404 276), lower := (rows 35 67 100 137 146 40 64 128 256), losses := [] }

theorem u18488 : Upper (D 7) (R 7) [34,65,96,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18488 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18489 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 67 100 137 146 48 332 396 268), lower := (rows 35 67 100 137 146 48 64 128 256), losses := [] }

theorem u18489 : Upper (D 7) (R 7) [34,65,96,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18489 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18490_4 : Upper (D 7) (R 7) [34,65,96,129,130,256,4] 13 :=
  permutation_upper _ _ _ [34,65,96,129,130,4,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4993

theorem m18490_8 : Upper (D 7) (R 7) [34,65,96,129,130,256,8] 13 :=
  permutation_upper _ _ _ [34,65,96,129,130,16,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4995

theorem m18490_16 : Upper (D 7) (R 7) [34,65,96,129,130,256,16] 13 :=
  permutation_upper _ _ _ [34,65,96,129,130,8,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4994

def r18490 : Route 9 := (fun mask => (mask,id))

def c18490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18490 : Upper (D 7) (R 7) [34,65,96,129,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,130,256] 13 (by decide) (choices 1) [4,8,16] r18490 c18490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18490_4
  · exact m18490_8
  · exact m18490_16

def b18491 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 148 34 344 408 280), lower := (rows 35 67 100 137 148 34 64 128 256), losses := [] }

theorem u18491 : Upper (D 7) (R 7) [34,65,96,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18492 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(4,0)], upper := (rows 35 67 100 137 148 40 338 402 274), lower := (rows 35 67 100 137 148 40 64 128 256), losses := [] }

theorem u18492 : Upper (D 7) (R 7) [34,65,96,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18492 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18493 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(3,5)], upper := (rows 35 67 100 137 148 48 330 394 266), lower := (rows 35 67 100 137 148 48 64 128 256), losses := [] }

theorem u18493 : Upper (D 7) (R 7) [34,65,96,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18493 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18494 : Route 9 := (fun mask => (mask,id))

def c18494 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18494 : Upper (D 7) (R 7) [34,65,96,129,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,132,256] 13 (by decide) (choices 1) [2,8,16] r18494 c18494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4996
  · exact u4997
  · exact u4998

def b18495 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 137 274 36 216 152 408), lower := (rows 35 67 100 137 274 36 64 128 256), losses := [] }

theorem u18495 : Upper (D 7) (R 7) [34,65,96,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18495 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18496 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(4,0)], upper := (rows 35 67 100 137 274 40 212 148 404), lower := (rows 35 67 100 137 274 40 64 128 256), losses := [] }

theorem u18496 : Upper (D 7) (R 7) [34,65,96,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18496 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18497 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 67 100 137 274 48 204 140 396), lower := (rows 35 67 100 137 274 48 64 128 256), losses := [] }

theorem u18497 : Upper (D 7) (R 7) [34,65,96,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18497 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18498 : Route 9 := (fun mask => (mask,id))

def c18498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18498 : Upper (D 7) (R 7) [34,65,96,129,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,258,128] 13 (by decide) (choices 1) [4,8,16] r18498 c18498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4999
  · exact u5000
  · exact u5001

def b18499 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 276 34 216 152 408), lower := (rows 35 67 100 137 276 34 64 128 256), losses := [] }

theorem u18499 : Upper (D 7) (R 7) [34,65,96,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18500 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(4,0)], upper := (rows 35 67 100 137 276 40 210 146 402), lower := (rows 35 67 100 137 276 40 64 128 256), losses := [] }

theorem u18500 : Upper (D 7) (R 7) [34,65,96,129,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18500 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18501 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(3,5)], upper := (rows 35 67 100 137 276 48 202 138 394), lower := (rows 35 67 100 137 276 48 64 128 256), losses := [] }

theorem u18501 : Upper (D 7) (R 7) [34,65,96,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18501 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18502 : Route 9 := (fun mask => (mask,id))

def c18502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18502 : Upper (D 7) (R 7) [34,65,96,129,260,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,260,128] 13 (by decide) (choices 1) [2,8,16] r18502 c18502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5002
  · exact u5003
  · exact u5004

def b18503 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 280 34 212 148 404), lower := (rows 35 67 100 137 280 34 64 128 256), losses := [] }

theorem u18503 : Upper (D 7) (R 7) [34,65,96,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18504 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 137 280 36 210 146 402), lower := (rows 35 67 100 137 280 36 64 128 256), losses := [] }

theorem u18504 : Upper (D 7) (R 7) [34,65,96,129,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18504 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18505 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 3, targets := 128 },{ cop := 0, region := 196, targets := 1 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 35 67 100 137 280 48 198 134 390), lower := (rows 35 67 100 137 280 48 64 128 256), losses := [] }

theorem u18505 : Upper (D 7) (R 7) [34,65,96,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18505 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18506 : Route 9 := (fun mask => (mask,id))

def c18506 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18506 : Upper (D 7) (R 7) [34,65,96,129,264,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,264,128] 13 (by decide) (choices 1) [2,4,16] r18506 c18506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5005
  · exact u5006
  · exact u5007

def b18507 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 400 34 92 156 284), lower := (rows 35 67 100 137 400 34 64 128 256), losses := [] }

theorem u18507 : Upper (D 7) (R 7) [34,65,96,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18508 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 137 400 36 90 154 282), lower := (rows 35 67 100 137 400 36 64 128 256), losses := [] }

theorem u18508 : Upper (D 7) (R 7) [34,65,96,129,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18508 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18509 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(4,0)], upper := (rows 35 67 100 137 400 40 86 150 278), lower := (rows 35 67 100 137 400 40 64 128 256), losses := [] }

theorem u18509 : Upper (D 7) (R 7) [34,65,96,129,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18509 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18510 : Route 9 := (fun mask => (mask,id))

def c18510 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18510 : Upper (D 7) (R 7) [34,65,96,129,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,384,16] 13 (by decide) (choices 1) [2,4,8] r18510 c18510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5008
  · exact u5009
  · exact u5010

def b18511 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 273 34 216 152 408), lower := (rows 35 67 100 140 273 34 64 128 256), losses := [] }

theorem u18511 : Upper (D 7) (R 7) [34,65,96,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18512 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 67 100 140 273 40 210 146 402), lower := (rows 35 67 100 140 273 40 64 128 256), losses := [] }

theorem u18512 : Upper (D 7) (R 7) [34,65,96,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18512 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18513 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 204, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(3,0)], upper := (rows 35 67 100 140 273 48 202 138 394), lower := (rows 35 67 100 140 273 48 64 128 256), losses := [] }

theorem u18513 : Upper (D 7) (R 7) [34,65,96,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18513 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18514 : Route 9 := (fun mask => (mask,id))

def c18514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18514 : Upper (D 7) (R 7) [34,65,96,132,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,257,128] 13 (by decide) (choices 1) [2,8,16] r18514 c18514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5011
  · exact u5012
  · exact u5013

def b18515 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 140 280 33 210 146 402), lower := (rows 35 67 100 140 280 33 64 128 256), losses := [] }

theorem u18515 : Upper (D 7) (R 7) [34,65,96,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18516 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 280 34 209 145 401), lower := (rows 35 67 100 140 280 34 64 128 256), losses := [] }

theorem u18516 : Upper (D 7) (R 7) [34,65,96,132,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18517 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 3, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(1,7)], upper := (rows 35 67 100 140 280 48 195 131 387), lower := (rows 35 67 100 140 280 48 64 128 256), losses := [] }

theorem u18517 : Upper (D 7) (R 7) [34,65,96,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18517 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18518_1 : Upper (D 7) (R 7) [34,65,96,132,264,128,1] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264,2,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5015

theorem m18518_2 : Upper (D 7) (R 7) [34,65,96,132,264,128,2] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264,1,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5014

theorem m18518_16 : Upper (D 7) (R 7) [34,65,96,132,264,128,16] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264,16,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5016

def r18518 : Route 9 := (fun mask => (mask,id))

def c18518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18518 : Upper (D 7) (R 7) [34,65,96,132,264,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,264,128] 13 (by decide) (choices 1) [1,2,16] r18518 c18518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18518_1
  · exact m18518_2
  · exact m18518_16

def b18519 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 140 400 33 90 154 282), lower := (rows 35 67 100 140 400 33 64 128 256), losses := [] }

theorem u18519 : Upper (D 7) (R 7) [34,65,96,132,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18520 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 400 34 89 153 281), lower := (rows 35 67 100 140 400 34 64 128 256), losses := [] }

theorem u18520 : Upper (D 7) (R 7) [34,65,96,132,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18521 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 67 100 140 400 40 83 147 275), lower := (rows 35 67 100 140 400 40 64 128 256), losses := [] }

theorem u18521 : Upper (D 7) (R 7) [34,65,96,132,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18521 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18522_1 : Upper (D 7) (R 7) [34,65,96,132,384,16,1] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384,2,16] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5018

theorem m18522_2 : Upper (D 7) (R 7) [34,65,96,132,384,16,2] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384,1,16] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5017

theorem m18522_8 : Upper (D 7) (R 7) [34,65,96,132,384,16,8] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384,8,16] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5019

def r18522 : Route 9 := (fun mask => (mask,id))

def c18522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18522 : Upper (D 7) (R 7) [34,65,96,132,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,384,16] 13 (by decide) (choices 1) [1,2,8] r18522 c18522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18522_1
  · exact m18522_2
  · exact m18522_8

def b18523 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 273 34 204 140 396), lower := (rows 35 67 100 152 273 34 64 128 256), losses := [] }

theorem u18523 : Upper (D 7) (R 7) [34,65,96,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18524 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 152 273 36 202 138 394), lower := (rows 35 67 100 152 273 36 64 128 256), losses := [] }

theorem u18524 : Upper (D 7) (R 7) [34,65,96,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18524 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18525 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 3, targets := 128 },{ cop := 0, region := 196, targets := 1 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 35 67 100 152 273 40 198 134 390), lower := (rows 35 67 100 152 273 40 64 128 256), losses := [] }

theorem u18525 : Upper (D 7) (R 7) [34,65,96,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18525 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18526 : Route 9 := (fun mask => (mask,id))

def c18526 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18526 : Upper (D 7) (R 7) [34,65,96,144,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,257,128] 13 (by decide) (choices 1) [2,4,8] r18526 c18526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5020
  · exact u5021
  · exact u5022

def b18527 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 152 276 33 202 138 394), lower := (rows 35 67 100 152 276 33 64 128 256), losses := [] }

theorem u18527 : Upper (D 7) (R 7) [34,65,96,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18528 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 276 34 201 137 393), lower := (rows 35 67 100 152 276 34 64 128 256), losses := [] }

theorem u18528 : Upper (D 7) (R 7) [34,65,96,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18529 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 3, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(1,7)], upper := (rows 35 67 100 152 276 40 195 131 387), lower := (rows 35 67 100 152 276 40 64 128 256), losses := [] }

theorem u18529 : Upper (D 7) (R 7) [34,65,96,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18529 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18530_1 : Upper (D 7) (R 7) [34,65,96,144,260,128,1] 13 :=
  permutation_upper _ _ _ [34,65,96,144,260,2,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5024

theorem m18530_2 : Upper (D 7) (R 7) [34,65,96,144,260,128,2] 13 :=
  permutation_upper _ _ _ [34,65,96,144,260,1,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5023

theorem m18530_8 : Upper (D 7) (R 7) [34,65,96,144,260,128,8] 13 :=
  permutation_upper _ _ _ [34,65,96,144,260,8,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5025

def r18530 : Route 9 := (fun mask => (mask,id))

def c18530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18530 : Upper (D 7) (R 7) [34,65,96,144,260,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,260,128] 13 (by decide) (choices 1) [1,2,8] r18530 c18530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18530_1
  · exact m18530_2
  · exact m18530_8

def b18531 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 152 280 33 198 134 390), lower := (rows 35 67 100 152 280 33 64 128 256), losses := [] }

theorem u18531 : Upper (D 7) (R 7) [34,65,96,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18532 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 280 34 197 133 389), lower := (rows 35 67 100 152 280 34 64 128 256), losses := [] }

theorem u18532 : Upper (D 7) (R 7) [34,65,96,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18533 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 152 280 36 195 131 387), lower := (rows 35 67 100 152 280 36 64 128 256), losses := [] }

theorem u18533 : Upper (D 7) (R 7) [34,65,96,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18533 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18534_1 : Upper (D 7) (R 7) [34,65,96,144,264,128,1] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264,2,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5027

theorem m18534_2 : Upper (D 7) (R 7) [34,65,96,144,264,128,2] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264,1,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5026

theorem m18534_4 : Upper (D 7) (R 7) [34,65,96,144,264,128,4] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264,4,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5028

def r18534 : Route 9 := (fun mask => (mask,id))

def c18534 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18534 : Upper (D 7) (R 7) [34,65,96,144,264,128] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,264,128] 13 (by decide) (choices 1) [1,2,4] r18534 c18534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18534_1
  · exact m18534_2
  · exact m18534_4

def b18535 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 67 133 138 276 40 112 240 368), lower := (rows 35 67 133 138 276 40 64 128 256), losses := [] }

theorem u18535 : Upper (D 7) (R 7) [34,65,129,130,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18535 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18536 : Route 9 := (fun mask => (mask,id))

def c18536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18536 : Upper (D 7) (R 7) [34,65,129,130,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,130,260,16] 13 (by decide) (choices 1) [8,32] r18536 c18536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5029
  · exact u5030

def b18537 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 138 276 96 120 184 312), lower := (rows 35 67 133 138 276 96 64 128 256), losses := [] }

theorem u18537 : Upper (D 7) (R 7) [34,65,129,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18538 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 133 138 304 36 88 216 344), lower := (rows 35 67 133 138 304 36 64 128 256), losses := [] }

theorem u18538 : Upper (D 7) (R 7) [34,65,129,130,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18538 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18539 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 67 133 138 304 40 84 212 340), lower := (rows 35 67 133 138 304 40 64 128 256), losses := [] }

theorem u18539 : Upper (D 7) (R 7) [34,65,129,130,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18539 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18539
end Delivery.IrregularNine14.P07
