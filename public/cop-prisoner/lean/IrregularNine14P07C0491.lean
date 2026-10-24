import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0188

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29460 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 88 148 34 201 137 393), lower := (rows 97 290 7 88 148 34 64 128 256), losses := [] }

theorem u29460 : Upper (D 7) (R 7) [96,288,3,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29461 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 88 148 40 195 131 387), lower := (rows 97 290 7 88 148 40 64 128 256), losses := [] }

theorem u29461 : Upper (D 7) (R 7) [96,288,3,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29461 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29462 : Route 9 := (fun mask => (mask,id))

def c29462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29462 : Upper (D 7) (R 7) [96,288,3,80,132,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,132,128] 13 (by decide) (choices 1) [1,2,8] r29462 c29462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11288
  · exact u11289
  · exact u11290

def r29463 : Route 9 := (fun mask => (mask,id))

def c29463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29463 : Upper (D 7) (R 7) [96,288,3,129,130,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129,130,4] 13 (by decide) (choices 1) [8,16] r29463 c29463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11291
  · exact u11292

def b29464 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 208, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 97 290 7 137 146 40 84 212 340), lower := (rows 97 290 7 137 146 40 64 128 256), losses := [] }

theorem u29464 : Upper (D 7) (R 7) [96,288,3,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29464 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29465 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 97 290 7 137 146 48 76 204 332), lower := (rows 97 290 7 137 146 48 64 128 256), losses := [] }

theorem u29465 : Upper (D 7) (R 7) [96,288,3,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29465 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29466 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 137 146 96 92 156 284), lower := (rows 97 290 7 137 146 96 64 128 256), losses := [] }

theorem u29466 : Upper (D 7) (R 7) [96,288,3,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29467 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 137 148 34 88 216 344), lower := (rows 97 290 7 137 148 34 64 128 256), losses := [] }

theorem u29467 : Upper (D 7) (R 7) [96,288,3,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29468 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 208, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 97 290 7 137 148 40 82 210 338), lower := (rows 97 290 7 137 148 40 64 128 256), losses := [] }

theorem u29468 : Upper (D 7) (R 7) [96,288,3,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29468 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29469 : Route 9 := (fun mask => (mask,id))

def c29469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29469 : Upper (D 7) (R 7) [96,288,3,129,132,16] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129,132,16] 13 (by decide) (choices 1) [2,8] r29469 c29469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11293
  · exact u11294

def b29470 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 137 148 96 90 154 282), lower := (rows 97 290 7 137 148 96 64 128 256), losses := [] }

theorem u29470 : Upper (D 7) (R 7) [96,288,3,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29471 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 137 208 34 92 156 284), lower := (rows 97 290 7 137 208 34 64 128 256), losses := [] }

theorem u29471 : Upper (D 7) (R 7) [96,288,3,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29472 : Route 9 := (fun mask => (mask,id))

def c29472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29472 : Upper (D 7) (R 7) [96,288,3,129,192,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129,192,4] 13 (by decide) (choices 1) [2,8,16] r29472 c29472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11295
  · exact u11296
  · exact u11297

def b29473 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 290 7 137 208 40 86 150 278), lower := (rows 97 290 7 137 208 40 64 128 256), losses := [] }

theorem u29473 : Upper (D 7) (R 7) [96,288,3,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29473 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29474 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 7 137 208 48 78 142 270), lower := (rows 97 290 7 137 208 48 64 128 256), losses := [] }

theorem u29474 : Upper (D 7) (R 7) [96,288,3,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29474 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29475 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 138 148 33 88 216 344), lower := (rows 97 290 7 138 148 33 64 128 256), losses := [] }

theorem u29475 : Upper (D 7) (R 7) [96,288,3,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29476 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 97 290 7 138 148 40 81 209 337), lower := (rows 97 290 7 138 148 40 64 128 256), losses := [] }

theorem u29476 : Upper (D 7) (R 7) [96,288,3,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29476 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29477 : Route 9 := (fun mask => (mask,id))

def c29477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29477 : Upper (D 7) (R 7) [96,288,3,130,132,16] 13 := by
  apply FastRouting.sound _ _ [96,288,3,130,132,16] 13 (by decide) (choices 1) [1,8] r29477 c29477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11298
  · exact u11299

def b29478 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 138 148 96 89 153 281), lower := (rows 97 290 7 138 148 96 64 128 256), losses := [] }

theorem u29478 : Upper (D 7) (R 7) [96,288,3,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29479 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 138 208 33 92 156 284), lower := (rows 97 290 7 138 208 33 64 128 256), losses := [] }

theorem u29479 : Upper (D 7) (R 7) [96,288,3,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29480 : Route 9 := (fun mask => (mask,id))

def c29480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29480 : Upper (D 7) (R 7) [96,288,3,130,192,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,130,192,4] 13 (by decide) (choices 1) [1,8,16] r29480 c29480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11300
  · exact u11301
  · exact u11302

def b29481 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 97 290 7 138 208 40 85 149 277), lower := (rows 97 290 7 138 208 40 64 128 256), losses := [] }

theorem u29481 : Upper (D 7) (R 7) [96,288,3,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29481 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29482 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 7 138 208 48 77 141 269), lower := (rows 97 290 7 138 208 48 64 128 256), losses := [] }

theorem u29482 : Upper (D 7) (R 7) [96,288,3,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29482 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29483 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 140 208 33 90 154 282), lower := (rows 97 290 7 140 208 33 64 128 256), losses := [] }

theorem u29483 : Upper (D 7) (R 7) [96,288,3,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29484 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 140 208 34 89 153 281), lower := (rows 97 290 7 140 208 34 64 128 256), losses := [] }

theorem u29484 : Upper (D 7) (R 7) [96,288,3,132,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29485 : Route 9 := (fun mask => (mask,id))

def c29485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29485 : Upper (D 7) (R 7) [96,288,3,132,192,8] 13 := by
  apply FastRouting.sound _ _ [96,288,3,132,192,8] 13 (by decide) (choices 1) [1,2,16] r29485 c29485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11303
  · exact u11304
  · exact u11305

def b29486 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 7 140 208 48 75 139 267), lower := (rows 97 290 7 140 208 48 64 128 256), losses := [] }

theorem u29486 : Upper (D 7) (R 7) [96,288,3,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29486 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29487 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 402, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 290 13 14 82 33 208 144 400), lower := (rows 97 290 13 14 82 33 64 128 256), losses := [] }

theorem u29487 : Upper (D 7) (R 7) [96,288,9,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29488 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 14 82 48 193 129 385), lower := (rows 97 290 13 14 82 48 64 128 256), losses := [] }

theorem u29488 : Upper (D 7) (R 7) [96,288,9,6,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29488 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29489 : Route 9 := (fun mask => (mask,id))

def c29489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29489 : Upper (D 7) (R 7) [96,288,9,6,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,66,128] 13 (by decide) (choices 1) [1,16,128] r29489 c29489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11306
  · exact u11307
  · exact u11308

def b29490 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 14 145 34 208 208 464), lower := (rows 97 290 13 14 145 34 64 128 256), losses := [] }

theorem u29490 : Upper (D 7) (R 7) [96,288,9,6,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29491 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 386, targets := 1 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 97 290 13 14 145 48 194 194 450), lower := (rows 97 290 13 14 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 51 4 12 16 48 127 191 319), good := (rows 482 482 462 462 498 498 64 128 256) },{ target := 5, region := (rows 1 2 4 8 20 0 74 138 266), good := (rows 65 450 477 478 145 16 64 128 256) }] }

theorem u29491 : Upper (D 7) (R 7) [96,288,9,6,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29491 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29492 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 14 145 96 210 146 402), lower := (rows 97 290 13 14 145 96 64 128 256), losses := [] }

theorem u29492 : Upper (D 7) (R 7) [96,288,9,6,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29493 : Route 9 := (fun mask => (mask,id))

def c29493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29493 : Upper (D 7) (R 7) [96,288,9,6,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,129,128] 13 (by decide) (choices 1) [2,16] r29493 c29493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11309
  · exact u11310

def b29494 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 290 13 14 146 33 208 208 464), lower := (rows 97 290 13 14 146 33 64 128 256), losses := [] }

theorem u29494 : Upper (D 7) (R 7) [96,288,9,6,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29495 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(2,1),(4,5)], upper := (rows 97 290 13 14 146 48 193 193 449), lower := (rows 97 290 13 14 146 48 64 128 256), losses := [{ target := 1, region := (rows 51 0 12 8 16 48 127 191 319), good := (rows 481 481 461 461 497 497 64 128 256) },{ target := 5, region := (rows 1 2 4 8 24 0 69 133 261), good := (rows 449 258 477 478 146 16 64 128 256) }] }

theorem u29495 : Upper (D 7) (R 7) [96,288,9,6,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29495 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29496 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 14 146 96 209 145 401), lower := (rows 97 290 13 14 146 96 64 128 256), losses := [] }

theorem u29496 : Upper (D 7) (R 7) [96,288,9,6,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29497 : Route 9 := (fun mask => (mask,id))

def c29497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29497 : Upper (D 7) (R 7) [96,288,9,6,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,130,128] 13 (by decide) (choices 1) [1,16] r29497 c29497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11311
  · exact u11312

def b29498 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 290 13 14 208 33 210 146 402), lower := (rows 97 290 13 14 208 33 64 128 256), losses := [] }

theorem u29498 : Upper (D 7) (R 7) [96,288,9,6,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29499 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 14 208 34 209 145 401), lower := (rows 97 290 13 14 208 34 64 128 256), losses := [] }

theorem u29499 : Upper (D 7) (R 7) [96,288,9,6,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29500 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 14 208 48 195 131 387), lower := (rows 97 290 13 14 208 48 64 128 256), losses := [] }

theorem u29500 : Upper (D 7) (R 7) [96,288,9,6,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29500 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29501 : Route 9 := (fun mask => (mask,id))

def c29501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29501 : Upper (D 7) (R 7) [96,288,9,6,192,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,192,128] 13 (by decide) (choices 1) [1,2,16] r29501 c29501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11313
  · exact u11314
  · exact u11315

def b29502 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 290 13 26 84 33 194 130 386), lower := (rows 97 290 13 26 84 33 64 128 256), losses := [] }

theorem u29502 : Upper (D 7) (R 7) [96,288,9,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29503 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 26 84 34 193 129 385), lower := (rows 97 290 13 26 84 34 64 128 256), losses := [] }

theorem u29503 : Upper (D 7) (R 7) [96,288,9,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29504 : Route 9 := (fun mask => (mask,id))

def c29504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29504 : Upper (D 7) (R 7) [96,288,9,18,68,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,68,128] 13 (by decide) (choices 1) [1,2,128] r29504 c29504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11316
  · exact u11317
  · exact u11318

def b29505 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 26 145 34 196 196 452), lower := (rows 97 290 13 26 145 34 64 128 256), losses := [] }

theorem u29505 : Upper (D 7) (R 7) [96,288,9,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29506 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 386, targets := 1 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 97 290 13 26 145 36 194 194 450), lower := (rows 97 290 13 26 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 24 16 36 127 191 319), good := (rows 482 482 494 474 474 486 64 128 256) },{ target := 5, region := (rows 1 2 4 8 20 0 74 138 266), good := (rows 65 450 477 474 145 20 64 128 256) }] }

theorem u29506 : Upper (D 7) (R 7) [96,288,9,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29506 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29507 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 26 145 96 198 134 390), lower := (rows 97 290 13 26 145 96 64 128 256), losses := [] }

theorem u29507 : Upper (D 7) (R 7) [96,288,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29508 : Route 9 := (fun mask => (mask,id))

def c29508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29508 : Upper (D 7) (R 7) [96,288,9,18,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,129,128] 13 (by decide) (choices 1) [2,4] r29508 c29508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11319
  · exact u11320

def b29509 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 97 290 13 26 148 33 194 194 450), lower := (rows 97 290 13 26 148 33 64 128 256), losses := [{ target := 0, region := (rows 0 35 4 12 20 32 111 175 303), good := (rows 482 482 478 474 476 482 64 128 256) }] }

theorem u29509 : Upper (D 7) (R 7) [96,288,9,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29510 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 26 148 34 193 193 449), lower := (rows 97 290 13 26 148 34 64 128 256), losses := [] }

theorem u29510 : Upper (D 7) (R 7) [96,288,9,18,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29511 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 26 148 96 195 131 387), lower := (rows 97 290 13 26 148 96 64 128 256), losses := [] }

theorem u29511 : Upper (D 7) (R 7) [96,288,9,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29512 : Route 9 := (fun mask => (mask,id))

def c29512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29512 : Upper (D 7) (R 7) [96,288,9,18,132,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,132,128] 13 (by decide) (choices 1) [1,2] r29512 c29512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11321
  · exact u11322

def b29513 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 418, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 290 13 26 208 33 198 134 390), lower := (rows 97 290 13 26 208 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 288 45 61 241 33 97 128 256) }] }

theorem u29513 : Upper (D 7) (R 7) [96,288,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29514 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 26 208 34 197 133 389), lower := (rows 97 290 13 26 208 34 64 128 256), losses := [] }

theorem u29514 : Upper (D 7) (R 7) [96,288,9,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29515 : Route 9 := (fun mask => (mask,id))

def c29515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29515 : Upper (D 7) (R 7) [96,288,9,18,192,4] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,192,4] 13 (by decide) (choices 1) [1,2,128] r29515 c29515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11323
  · exact u11324
  · exact u11325

def r29516 : Route 9 := (fun mask => (mask,id))

def c29516 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29516 : Upper (D 7) (R 7) [96,288,9,18,192,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,192,128] 13 (by decide) (choices 1) [1,2,4] r29516 c29516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11326
  · exact u11327
  · exact u11328

def b29517 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 28 82 33 194 130 386), lower := (rows 97 290 13 28 82 33 64 128 256), losses := [] }

theorem u29517 : Upper (D 7) (R 7) [96,288,9,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29518 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 290 13 28 82 34 193 129 385), lower := (rows 97 290 13 28 82 34 64 128 256), losses := [] }

theorem u29518 : Upper (D 7) (R 7) [96,288,9,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29519 : Route 9 := (fun mask => (mask,id))

def c29519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29519 : Upper (D 7) (R 7) [96,288,9,20,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,20,66,128] 13 (by decide) (choices 1) [1,2,128] r29519 c29519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11329
  · exact u11330
  · exact u11331

#print axioms u29519
end Delivery.IrregularNine14.P07
