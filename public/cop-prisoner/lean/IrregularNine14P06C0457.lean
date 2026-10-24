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

def r27420 : Route 9 := (fun mask => (mask,id))

def c27420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27420 : Upper (D 6) (R 6) [96,132,264,5,3,2] 13 := by
  apply FastRouting.sound _ _ [96,132,264,5,3,2] 13 (by decide) (choices 1) [16,32] r27420 c27420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8671
  · exact u8672

def b27421 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 97 134 268 13 19 48 98 226 354), lower := (rows 97 134 268 13 19 48 64 128 256), losses := [] }

theorem u27421 : Upper (D 6) (R 6) [96,132,264,5,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27421 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27422 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 13 19 96 114 178 306), lower := (rows 97 134 268 13 19 96 64 128 256), losses := [] }

theorem u27422 : Upper (D 6) (R 6) [96,132,264,5,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27423 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 268 13 50 33 82 210 338), lower := (rows 97 134 268 13 50 33 64 128 256), losses := [] }

theorem u27423 : Upper (D 6) (R 6) [96,132,264,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27424 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 134 268 13 50 34 81 209 337), lower := (rows 97 134 268 13 50 34 64 128 256), losses := [] }

theorem u27424 : Upper (D 6) (R 6) [96,132,264,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27425 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 268 13 50 48 67 195 323), lower := (rows 97 134 268 13 50 48 64 128 256), losses := [] }

theorem u27425 : Upper (D 6) (R 6) [96,132,264,5,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27425 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27426 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 13 50 96 83 147 275), lower := (rows 97 134 268 13 50 96 64 128 256), losses := [] }

theorem u27426 : Upper (D 6) (R 6) [96,132,264,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27427 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 134 268 25 50 33 70 198 326), lower := (rows 97 134 268 25 50 33 64 128 256), losses := [] }

theorem u27427 : Upper (D 6) (R 6) [96,132,264,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27428 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 97 134 268 25 50 34 69 197 325), lower := (rows 97 134 268 25 50 34 64 128 256), losses := [] }

theorem u27428 : Upper (D 6) (R 6) [96,132,264,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27429 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,6)], upper := (rows 97 134 268 25 50 36 67 195 323), lower := (rows 97 134 268 25 50 36 64 128 256), losses := [] }

theorem u27429 : Upper (D 6) (R 6) [96,132,264,17,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27430 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 25 50 96 71 135 263), lower := (rows 97 134 268 25 50 96 64 128 256), losses := [] }

theorem u27430 : Upper (D 6) (R 6) [96,132,264,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27431 : Route 9 := (fun mask => (mask,id))

def c27431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27431 : Upper (D 6) (R 6) [96,132,264,18,5,1] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18,5,1] 13 (by decide) (choices 1) [2,32] r27431 c27431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8673
  · exact u8674

theorem m27432_1 : Upper (D 6) (R 6) [96,132,264,18,5,2,1] 13 :=
  permutation_upper _ _ _ [96,132,264,18,5,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8673

def r27432 : Route 9 := (fun mask => (mask,id))

def c27432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27432 : Upper (D 6) (R 6) [96,132,264,18,5,2] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18,5,2] 13 (by decide) (choices 1) [1,32] r27432 c27432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m27432_1
  · exact u8675

def b27433 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 26 21 96 99 163 291), lower := (rows 97 134 268 26 21 96 64 128 256), losses := [] }

theorem u27433 : Upper (D 6) (R 6) [96,132,264,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27434 : Route 9 := (fun mask => (mask,id))

def c27434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27434 : Upper (D 6) (R 6) [96,132,264,18,36,1] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18,36,1] 13 (by decide) (choices 1) [1,2] r27434 c27434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8676
  · exact u8677

def b27435 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 134 268 26 52 34 65 193 321), lower := (rows 97 134 268 26 52 34 64 128 256), losses := [] }

theorem u27435 : Upper (D 6) (R 6) [96,132,264,18,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27436 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 26 52 96 67 131 259), lower := (rows 97 134 268 26 52 96 64 128 256), losses := [] }

theorem u27436 : Upper (D 6) (R 6) [96,132,264,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27437 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 268 28 19 33 98 226 354), lower := (rows 97 134 268 28 19 33 64 128 256), losses := [] }

theorem u27437 : Upper (D 6) (R 6) [96,132,264,20,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27438 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 5, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 268 28 19 34 97 225 353), lower := (rows 97 134 268 28 19 34 64 128 256), losses := [] }

theorem u27438 : Upper (D 6) (R 6) [96,132,264,20,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27439 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 28 19 96 99 163 291), lower := (rows 97 134 268 28 19 96 64 128 256), losses := [] }

theorem u27439 : Upper (D 6) (R 6) [96,132,264,20,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27440 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 268 28 50 33 67 195 323), lower := (rows 97 134 268 28 50 33 64 128 256), losses := [] }

theorem u27440 : Upper (D 6) (R 6) [96,132,264,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27441 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 134 268 28 50 34 65 193 321), lower := (rows 97 134 268 28 50 34 64 128 256), losses := [] }

theorem u27441 : Upper (D 6) (R 6) [96,132,264,20,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27442 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 28 50 96 67 131 259), lower := (rows 97 134 268 28 50 96 64 128 256), losses := [] }

theorem u27442 : Upper (D 6) (R 6) [96,132,264,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27443 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 40, targets := 68 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(3,2),(3,6)], upper := (rows 97 134 268 42 19 33 84 212 340), lower := (rows 97 134 268 42 19 33 64 128 256), losses := [] }

theorem u27443 : Upper (D 6) (R 6) [96,132,264,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27444 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 3, region := 81, targets := 4 }], pairs := [(0,2),(3,0),(3,6)], upper := (rows 97 134 268 42 19 36 81 209 337), lower := (rows 97 134 268 42 19 36 64 128 256), losses := [] }

theorem u27444 : Upper (D 6) (R 6) [96,132,264,34,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27445 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 97 134 268 42 19 48 69 197 325), lower := (rows 97 134 268 42 19 48 64 128 256), losses := [] }

theorem u27445 : Upper (D 6) (R 6) [96,132,264,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27445 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27446 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 42 19 96 85 149 277), lower := (rows 97 134 268 42 19 96 64 128 256), losses := [] }

theorem u27446 : Upper (D 6) (R 6) [96,132,264,34,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27447 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 194, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5)], upper := (rows 97 134 268 42 21 33 82 210 338), lower := (rows 97 134 268 42 21 33 64 128 256), losses := [] }

theorem u27447 : Upper (D 6) (R 6) [96,132,264,34,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27448 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 134 268 42 21 34 81 209 337), lower := (rows 97 134 268 42 21 34 64 128 256), losses := [] }

theorem u27448 : Upper (D 6) (R 6) [96,132,264,34,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27449 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 65, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,5)], upper := (rows 97 134 268 42 21 48 67 195 323), lower := (rows 97 134 268 42 21 48 64 128 256), losses := [] }

theorem u27449 : Upper (D 6) (R 6) [96,132,264,34,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27449 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27450 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 42 21 96 83 147 275), lower := (rows 97 134 268 42 21 96 64 128 256), losses := [] }

theorem u27450 : Upper (D 6) (R 6) [96,132,264,34,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27451 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 97 134 268 42 82 33 85 149 277), lower := (rows 97 134 268 42 82 33 64 128 256), losses := [] }

theorem u27451 : Upper (D 6) (R 6) [96,132,264,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27452 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 3, region := 81, targets := 4 }], pairs := [(0,2),(3,0),(3,6)], upper := (rows 97 134 268 42 82 36 81 145 273), lower := (rows 97 134 268 42 82 36 64 128 256), losses := [] }

theorem u27452 : Upper (D 6) (R 6) [96,132,264,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27453 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 268 42 82 48 69 133 261), lower := (rows 97 134 268 42 82 48 64 128 256), losses := [] }

theorem u27453 : Upper (D 6) (R 6) [96,132,264,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27453 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27454 : Route 9 := (fun mask => (mask,id))

def c27454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27454 : Upper (D 6) (R 6) [96,132,264,34,68,1] 13 := by
  apply FastRouting.sound _ _ [96,132,264,34,68,1] 13 (by decide) (choices 1) [1,2,16] r27454 c27454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8678
  · exact u8679
  · exact u8680

def b27455 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 134 268 42 84 34 81 145 273), lower := (rows 97 134 268 42 84 34 64 128 256), losses := [] }

theorem u27455 : Upper (D 6) (R 6) [96,132,264,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27456 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 268 42 84 48 67 131 259), lower := (rows 97 134 268 42 84 48 64 128 256), losses := [] }

theorem u27456 : Upper (D 6) (R 6) [96,132,264,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27456 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27457 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 268 44 19 33 82 210 338), lower := (rows 97 134 268 44 19 33 64 128 256), losses := [] }

theorem u27457 : Upper (D 6) (R 6) [96,132,264,36,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27458 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(3,0),(3,6)], upper := (rows 97 134 268 44 19 34 81 209 337), lower := (rows 97 134 268 44 19 34 64 128 256), losses := [] }

theorem u27458 : Upper (D 6) (R 6) [96,132,264,36,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27459 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 97 134 268 44 19 48 67 195 323), lower := (rows 97 134 268 44 19 48 64 128 256), losses := [] }

theorem u27459 : Upper (D 6) (R 6) [96,132,264,36,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27459 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27460 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 44 19 96 83 147 275), lower := (rows 97 134 268 44 19 96 64 128 256), losses := [] }

theorem u27460 : Upper (D 6) (R 6) [96,132,264,36,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27461 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 268 44 82 33 83 147 275), lower := (rows 97 134 268 44 82 33 64 128 256), losses := [] }

theorem u27461 : Upper (D 6) (R 6) [96,132,264,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27462 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(3,0),(3,6)], upper := (rows 97 134 268 44 82 34 81 145 273), lower := (rows 97 134 268 44 82 34 64 128 256), losses := [] }

theorem u27462 : Upper (D 6) (R 6) [96,132,264,36,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27463 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 268 44 82 48 67 131 259), lower := (rows 97 134 268 44 82 48 64 128 256), losses := [] }

theorem u27463 : Upper (D 6) (R 6) [96,132,264,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27463 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27464 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 134 268 56 19 33 70 198 326), lower := (rows 97 134 268 56 19 33 64 128 256), losses := [] }

theorem u27464 : Upper (D 6) (R 6) [96,132,264,48,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27465 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 134 268 56 19 34 69 197 325), lower := (rows 97 134 268 56 19 34 64 128 256), losses := [] }

theorem u27465 : Upper (D 6) (R 6) [96,132,264,48,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27466 : PairBound 9 := { available := 67, camps := [], pairs := [(0,2),(3,0),(3,1)], upper := (rows 97 134 268 56 19 36 67 195 323), lower := (rows 97 134 268 56 19 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 96 166 300 56 58 36 64 128 256) },{ target := 1, region := (rows 1 0 4 24 16 38 64 128 256), good := (rows 97 164 300 56 57 36 64 128 256) },{ target := 2, region := (rows 9 2 0 8 16 32 80 144 272), good := (rows 97 130 265 505 467 32 64 128 256) }] }

theorem u27466 : Upper (D 6) (R 6) [96,132,264,48,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27467 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 268 56 19 96 71 135 263), lower := (rows 97 134 268 56 19 96 64 128 256), losses := [] }

theorem u27467 : Upper (D 6) (R 6) [96,132,264,48,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27468 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 268 56 82 33 71 135 263), lower := (rows 97 134 268 56 82 33 64 128 256), losses := [] }

theorem u27468 : Upper (D 6) (R 6) [96,132,264,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27469 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 325, targets := 2 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 97 134 268 56 82 34 69 133 261), lower := (rows 97 134 268 56 82 34 64 128 256), losses := [] }

theorem u27469 : Upper (D 6) (R 6) [96,132,264,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27470 : PairBound 9 := { available := 3, camps := [], pairs := [(0,1),(3,0),(3,1)], upper := (rows 97 134 268 56 82 36 67 131 259), lower := (rows 97 134 268 56 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 96 166 300 56 122 36 64 128 256) },{ target := 1, region := (rows 17 0 4 24 16 38 64 128 256), good := (rows 97 164 300 57 121 36 64 128 256) }] }

theorem u27470 : Upper (D 6) (R 6) [96,132,264,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27471 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 268 56 84 33 67 131 259), lower := (rows 97 134 268 56 84 33 64 128 256), losses := [] }

theorem u27471 : Upper (D 6) (R 6) [96,132,264,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27472 : Route 9 := (fun mask => (mask,id))

def c27472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27472 : Upper (D 6) (R 6) [96,132,264,48,68,2] 13 := by
  apply FastRouting.sound _ _ [96,132,264,48,68,2] 13 (by decide) (choices 1) [1,2] r27472 c27472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8681
  · exact u8682

def r27473 : Route 9 := (fun mask => (mask,id))

def c27473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27473 : Upper (D 6) (R 6) [96,132,288,3,5,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,5,2] 13 (by decide) (choices 1) [8,16] r27473 c27473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8683
  · exact u8684

def b27474 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 134 292 11 21 40 82 210 338), lower := (rows 97 134 292 11 21 40 64 128 256), losses := [] }

theorem u27474 : Upper (D 6) (R 6) [96,132,288,3,5,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27474 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27475 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 134 292 11 21 48 74 202 330), lower := (rows 97 134 292 11 21 48 64 128 256), losses := [] }

theorem u27475 : Upper (D 6) (R 6) [96,132,288,3,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27475 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27476 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 292 11 21 96 90 154 282), lower := (rows 97 134 292 11 21 96 64 128 256), losses := [] }

theorem u27476 : Upper (D 6) (R 6) [96,132,288,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27477 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 194, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5)], upper := (rows 97 134 292 11 28 33 82 210 338), lower := (rows 97 134 292 11 28 33 64 128 256), losses := [] }

theorem u27477 : Upper (D 6) (R 6) [96,132,288,3,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27478 : Route 9 := (fun mask => (mask,id))

def c27478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27478 : Upper (D 6) (R 6) [96,132,288,3,12,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,12,2] 13 (by decide) (choices 1) [1,16] r27478 c27478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8685
  · exact u8686

def b27479 : PairBound 9 := { available := 67, camps := [], pairs := [(0,2),(1,5)], upper := (rows 97 134 292 11 28 48 67 195 323), lower := (rows 97 134 292 11 28 48 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 8 16 48 72 136 264), good := (rows 97 130 288 459 505 49 64 128 256) },{ target := 5, region := (rows 1 18 4 8 16 0 72 136 264), good := (rows 65 134 260 459 478 18 64 128 256) }] }

theorem u27479 : Upper (D 6) (R 6) [96,132,288,3,12,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27479 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27479
end Delivery.IrregularNine14.P06
