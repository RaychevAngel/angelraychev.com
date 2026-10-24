import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0348
import IrregularNine14P06C0349
import IrregularNine14P06C0350

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36480 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 74 100 13 21 434 466 402 402), lower := (rows 35 74 100 13 21 32 64 128 256), losses := [] }

theorem u36480 : Upper (D 6) (R 6) [34,72,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36481 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 74 100 13 22 433 465 401 401), lower := (rows 35 74 100 13 22 32 64 128 256), losses := [] }

theorem u36481 : Upper (D 6) (R 6) [34,72,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36482 : Route 9 := (fun mask => (mask,id))

def c36482 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36482 : Upper (D 6) (R 6) [34,72,96,5,129] 13 := by
  apply FastRouting.sound _ _ [34,72,96,5,129] 13 (by decide) (choices 1) [2,4,16,256] r36482 c36482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20912
  · exact u20913
  · exact u20914
  · exact u20915

def r36483 : Route 9 := (fun mask => (mask,id))

def c36483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36483 : Upper (D 6) (R 6) [34,72,96,5,130] 13 := by
  apply FastRouting.sound _ _ [34,72,96,5,130] 13 (by decide) (choices 1) [1,4,16,256] r36483 c36483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20916
  · exact u20917
  · exact u20918
  · exact u20919

def r36484 : Route 9 := (fun mask => (mask,id))

def c36484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36484 : Upper (D 6) (R 6) [34,72,96,5,132] 13 := by
  apply FastRouting.sound _ _ [34,72,96,5,132] 13 (by decide) (choices 1) [1,2,16,256] r36484 c36484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20920
  · exact u20921
  · exact u20922
  · exact u20923

def r36485 : Route 9 := (fun mask => (mask,id))

def c36485 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36485 : Upper (D 6) (R 6) [34,72,96,5,384] 13 := by
  apply FastRouting.sound _ _ [34,72,96,5,384] 13 (by decide) (choices 1) [1,2,4,16] r36485 c36485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20924
  · exact u20925
  · exact u20926
  · exact u20927

def b36486 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 25 19 420 452 388 388), lower := (rows 35 74 100 25 19 32 64 128 256), losses := [] }

theorem u36486 : Upper (D 6) (R 6) [34,72,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36487 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 100 25 21 422 454 390 390), lower := (rows 35 74 100 25 21 32 64 128 256), losses := [] }

theorem u36487 : Upper (D 6) (R 6) [34,72,96,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36488 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 425, targets := 64 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 74 100 25 22 421 453 389 389), lower := (rows 35 74 100 25 22 32 64 128 256), losses := [] }

theorem u36488 : Upper (D 6) (R 6) [34,72,96,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36489 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 74 100 25 145 294 326 390 262), lower := (rows 35 74 100 25 145 32 64 128 256), losses := [] }

theorem u36489 : Upper (D 6) (R 6) [34,72,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36490 : Route 9 := (fun mask => (mask,id))

def c36490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36490 : Upper (D 6) (R 6) [34,72,96,17,130] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,130] 13 (by decide) (choices 1) [1,4,256] r36490 c36490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20928
  · exact u20929
  · exact u20930

def r36491 : Route 9 := (fun mask => (mask,id))

def c36491 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36491 : Upper (D 6) (R 6) [34,72,96,17,132] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,132] 13 (by decide) (choices 1) [1,2,4,256] r36491 c36491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20931
  · exact u20932
  · exact u20933
  · exact u20934

def r36492 : Route 9 := (fun mask => (mask,id))

def c36492 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36492 : Upper (D 6) (R 6) [34,72,96,17,384] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,384] 13 (by decide) (choices 1) [1,2,4] r36492 c36492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20935
  · exact u20936
  · exact u20937

def b36493 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 74 100 26 21 421 453 389 389), lower := (rows 35 74 100 26 21 32 64 128 256), losses := [] }

theorem u36493 : Upper (D 6) (R 6) [34,72,96,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36494 : Route 9 := (fun mask => (mask,id))

def c36494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36494 : Upper (D 6) (R 6) [34,72,96,18,129] 13 := by
  apply FastRouting.sound _ _ [34,72,96,18,129] 13 (by decide) (choices 1) [1,4,256] r36494 c36494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20938
  · exact u20939
  · exact u20940

def r36495 : Route 9 := (fun mask => (mask,id))

def c36495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36495 : Upper (D 6) (R 6) [34,72,96,18,132] 13 := by
  apply FastRouting.sound _ _ [34,72,96,18,132] 13 (by decide) (choices 1) [1,4,256] r36495 c36495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20941
  · exact u20942
  · exact u20943

def r36496 : Route 9 := (fun mask => (mask,id))

def c36496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36496 : Upper (D 6) (R 6) [34,72,96,18,384] 13 := by
  apply FastRouting.sound _ _ [34,72,96,18,384] 13 (by decide) (choices 1) [1,4] r36496 c36496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20944
  · exact u20945

def b36497 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 100 28 19 421 453 389 389), lower := (rows 35 74 100 28 19 32 64 128 256), losses := [] }

theorem u36497 : Upper (D 6) (R 6) [34,72,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36498 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 100 28 21 419 451 387 387), lower := (rows 35 74 100 28 21 32 64 128 256), losses := [] }

theorem u36498 : Upper (D 6) (R 6) [34,72,96,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36499 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 26, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 28 22 417 449 385 385), lower := (rows 35 74 100 28 22 32 64 128 256), losses := [] }

theorem u36499 : Upper (D 6) (R 6) [34,72,96,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36500 : Route 9 := (fun mask => (mask,id))

def c36500 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36500 : Upper (D 6) (R 6) [34,72,96,20,129] 13 := by
  apply FastRouting.sound _ _ [34,72,96,20,129] 13 (by decide) (choices 1) [1,2,4,256] r36500 c36500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20946
  · exact u20947
  · exact u20948
  · exact u20949

def r36501 : Route 9 := (fun mask => (mask,id))

def c36501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36501 : Upper (D 6) (R 6) [34,72,96,20,130] 13 := by
  apply FastRouting.sound _ _ [34,72,96,20,130] 13 (by decide) (choices 1) [1,4,256] r36501 c36501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20950
  · exact u20951
  · exact u20952

def b36502 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 100 28 148 291 323 387 259), lower := (rows 35 74 100 28 148 32 64 128 256), losses := [] }

theorem u36502 : Upper (D 6) (R 6) [34,72,96,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36503 : Route 9 := (fun mask => (mask,id))

def c36503 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36503 : Upper (D 6) (R 6) [34,72,96,20,384] 13 := by
  apply FastRouting.sound _ _ [34,72,96,20,384] 13 (by decide) (choices 1) [1,2,4] r36503 c36503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20953
  · exact u20954
  · exact u20955

def b36504 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 100 137 19 308 340 404 276), lower := (rows 35 74 100 137 19 32 64 128 256), losses := [] }

theorem u36504 : Upper (D 6) (R 6) [34,72,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36505 : Route 9 := (fun mask => (mask,id))

def c36505 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36505 : Upper (D 6) (R 6) [34,72,96,129,5] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,5] 13 (by decide) (choices 1) [2,4,16,256] r36505 c36505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20956
  · exact u20957
  · exact u20958
  · exact u20959

def r36506 : Route 9 := (fun mask => (mask,id))

def c36506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36506 : Upper (D 6) (R 6) [34,72,96,129,6] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,6] 13 (by decide) (choices 1) [1,4,16,256] r36506 c36506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20960
  · exact u20961
  · exact u20962
  · exact u20963

def r36507 : Route 9 := (fun mask => (mask,id))

def c36507 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36507 : Upper (D 6) (R 6) [34,72,96,129,257] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,257] 13 (by decide) (choices 1) [2,4,16] r36507 c36507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20964
  · exact u20965
  · exact u20966

def r36508 : Route 9 := (fun mask => (mask,id))

def c36508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36508 : Upper (D 6) (R 6) [34,72,96,129,258] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,258] 13 (by decide) (choices 1) [1,4,16] r36508 c36508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20967
  · exact u20968
  · exact u20969

def r36509 : Route 9 := (fun mask => (mask,id))

def c36509 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36509 : Upper (D 6) (R 6) [34,72,96,129,260] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,260] 13 (by decide) (choices 1) [1,2,4,16] r36509 c36509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20970
  · exact u20971
  · exact u20972
  · exact u20973

def b36510 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 74 100 138 21 309 341 405 277), lower := (rows 35 74 100 138 21 32 64 128 256), losses := [] }

theorem u36510 : Upper (D 6) (R 6) [34,72,96,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36511 : Route 9 := (fun mask => (mask,id))

def c36511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36511 : Upper (D 6) (R 6) [34,72,96,130,257] 13 := by
  apply FastRouting.sound _ _ [34,72,96,130,257] 13 (by decide) (choices 1) [1,4,16] r36511 c36511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20974
  · exact u20975
  · exact u20976

def r36512 : Route 9 := (fun mask => (mask,id))

def c36512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36512 : Upper (D 6) (R 6) [34,72,96,130,260] 13 := by
  apply FastRouting.sound _ _ [34,72,96,130,260] 13 (by decide) (choices 1) [1,4,16] r36512 c36512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20977
  · exact u20978
  · exact u20979

def b36513 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 100 140 19 309 341 405 277), lower := (rows 35 74 100 140 19 32 64 128 256), losses := [] }

theorem u36513 : Upper (D 6) (R 6) [34,72,96,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36514 : Route 9 := (fun mask => (mask,id))

def c36514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36514 : Upper (D 6) (R 6) [34,72,96,132,5] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,5] 13 (by decide) (choices 1) [1,2,16,256] r36514 c36514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20980
  · exact u20981
  · exact u20982
  · exact u20983

def b36515 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 425, targets := 64 },{ cop := 4, region := 289, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 74 100 140 22 305 337 401 273), lower := (rows 35 74 100 140 22 32 64 128 256), losses := [] }

theorem u36515 : Upper (D 6) (R 6) [34,72,96,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36516 : Route 9 := (fun mask => (mask,id))

def c36516 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36516 : Upper (D 6) (R 6) [34,72,96,132,257] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,257] 13 (by decide) (choices 1) [1,2,4,16] r36516 c36516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20984
  · exact u20985
  · exact u20986
  · exact u20987

def r36517 : Route 9 := (fun mask => (mask,id))

def c36517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36517 : Upper (D 6) (R 6) [34,72,96,132,258] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,258] 13 (by decide) (choices 1) [1,4,16] r36517 c36517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20988
  · exact u20989
  · exact u20990

def r36518 : Route 9 := (fun mask => (mask,id))

def c36518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36518 : Upper (D 6) (R 6) [34,72,96,132,260] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,260] 13 (by decide) (choices 1) [1,2,16] r36518 c36518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20991
  · exact u20992
  · exact u20993

def b36519 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 100 152 19 293 325 389 261), lower := (rows 35 74 100 152 19 32 64 128 256), losses := [] }

theorem u36519 : Upper (D 6) (R 6) [34,72,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36520 : Route 9 := (fun mask => (mask,id))

def c36520 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36520 : Upper (D 6) (R 6) [34,72,96,144,5] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,5] 13 (by decide) (choices 1) [1,2,4,256] r36520 c36520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20994
  · exact u20995
  · exact u20996
  · exact u20997

def b36521 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 425, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 74 100 152 22 293 325 389 261), lower := (rows 35 74 100 152 22 32 64 128 256), losses := [] }

theorem u36521 : Upper (D 6) (R 6) [34,72,96,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36522 : Route 9 := (fun mask => (mask,id))

def c36522 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36522 : Upper (D 6) (R 6) [34,72,96,144,257] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,257] 13 (by decide) (choices 1) [1,2,4] r36522 c36522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20998
  · exact u20999
  · exact u21000

def r36523 : Route 9 := (fun mask => (mask,id))

def c36523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36523 : Upper (D 6) (R 6) [34,72,96,144,258] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,258] 13 (by decide) (choices 1) [1,4] r36523 c36523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21001
  · exact u21002

def r36524 : Route 9 := (fun mask => (mask,id))

def c36524 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36524 : Upper (D 6) (R 6) [34,72,96,144,260] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,260] 13 (by decide) (choices 1) [1,2,4] r36524 c36524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21003
  · exact u21004
  · exact u21005

def b36525 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 100 392 19 53 85 149 277), lower := (rows 35 74 100 392 19 32 64 128 256), losses := [] }

theorem u36525 : Upper (D 6) (R 6) [34,72,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36526 : Route 9 := (fun mask => (mask,id))

def c36526 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36526 : Upper (D 6) (R 6) [34,72,96,384,5] 13 := by
  apply FastRouting.sound _ _ [34,72,96,384,5] 13 (by decide) (choices 1) [1,2,4,16] r36526 c36526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21006
  · exact u21007
  · exact u21008
  · exact u21009

def r36527 : Route 9 := (fun mask => (mask,id))

def c36527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36527 : Upper (D 6) (R 6) [34,72,96,384,6] 13 := by
  apply FastRouting.sound _ _ [34,72,96,384,6] 13 (by decide) (choices 1) [1,4,16] r36527 c36527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21010
  · exact u21011
  · exact u21012

def b36528 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 74 133 14 21 368 368 496 368), lower := (rows 35 74 133 14 21 32 64 128 256), losses := [] }

theorem u36528 : Upper (D 6) (R 6) [34,72,129,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36529 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 133 14 49 372 340 468 340), lower := (rows 35 74 133 14 49 32 64 128 256), losses := [] }

theorem u36529 : Upper (D 6) (R 6) [34,72,129,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36530 : Route 9 := (fun mask => (mask,id))

def c36530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36530 : Upper (D 6) (R 6) [34,72,129,6,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6,36] 13 (by decide) (choices 1) [1,16,64,256] r36530 c36530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21013
  · exact u21014
  · exact u21015
  · exact u21016

def b36531 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 133 14 81 308 372 436 308), lower := (rows 35 74 133 14 81 32 64 128 256), losses := [] }

theorem u36531 : Upper (D 6) (R 6) [34,72,129,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36532 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 14 84 305 369 433 305), lower := (rows 35 74 133 14 84 32 64 128 256), losses := [] }

theorem u36532 : Upper (D 6) (R 6) [34,72,129,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36533 : Route 9 := (fun mask => (mask,id))

def c36533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36533 : Upper (D 6) (R 6) [34,72,129,6,96] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6,96] 13 (by decide) (choices 1) [1,4,16,256] r36533 c36533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21017
  · exact u21018
  · exact u21019
  · exact u21020

def r36534 : Route 9 := (fun mask => (mask,id))

def c36534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36534 : Upper (D 6) (R 6) [34,72,129,6,257] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6,257] 13 (by decide) (choices 1) [4,16,64] r36534 c36534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21021
  · exact u21022
  · exact u21023

def r36535 : Route 9 := (fun mask => (mask,id))

def c36535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36535 : Upper (D 6) (R 6) [34,72,129,6,260] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6,260] 13 (by decide) (choices 1) [1,16,64] r36535 c36535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21024
  · exact u21025
  · exact u21026

def r36536 : Route 9 := (fun mask => (mask,id))

def c36536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36536 : Upper (D 6) (R 6) [34,72,129,6,288] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6,288] 13 (by decide) (choices 1) [1,4,16,64] r36536 c36536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21027
  · exact u21028
  · exact u21029
  · exact u21030

def r36537 : Route 9 := (fun mask => (mask,id))

def c36537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36537 : Upper (D 6) (R 6) [34,72,129,6,320] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6,320] 13 (by decide) (choices 1) [1,4,16] r36537 c36537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21031
  · exact u21032
  · exact u21033

def r36538 : Route 9 := (fun mask => (mask,id))

def c36538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36538 : Upper (D 6) (R 6) [34,72,129,17,6] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,6] 13 (by decide) (choices 1) [4,64,256] r36538 c36538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21034
  · exact u21035
  · exact u21036

def b36539 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 133 25 50 356 324 452 324), lower := (rows 35 74 133 25 50 32 64 128 256), losses := [] }

theorem u36539 : Upper (D 6) (R 6) [34,72,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36539
end Delivery.IrregularNine14.P06
