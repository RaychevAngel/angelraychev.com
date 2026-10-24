import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0398
import IrregularNine14P07C0399
import IrregularNine14P07C0400

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37440 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 76 152 145 291 323 387 259), lower := (rows 37 98 76 152 145 32 64 128 256), losses := [] }

theorem u37440 : Upper (D 7) (R 7) [36,96,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37441 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 76 152 146 291 323 387 259), lower := (rows 37 98 76 152 146 32 64 128 256), losses := [] }

theorem u37441 : Upper (D 7) (R 7) [36,96,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37442 : Route 9 := (fun mask => (mask,id))

def c37442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37442 : Upper (D 7) (R 7) [36,96,72,144,257] 13 := by
  apply FastRouting.sound _ _ [36,96,72,144,257] 13 (by decide) (choices 1) [1,2,128] r37442 c37442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23901
  · exact u23902
  · exact u23903

def r37443 : Route 9 := (fun mask => (mask,id))

def c37443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37443 : Upper (D 7) (R 7) [36,96,72,144,258] 13 := by
  apply FastRouting.sound _ _ [36,96,72,144,258] 13 (by decide) (choices 1) [1,2,128] r37443 c37443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23904
  · exact u23905
  · exact u23906

def b37444 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 76 152 400 35 67 131 259), lower := (rows 37 98 76 152 400 32 64 128 256), losses := [] }

theorem u37444 : Upper (D 7) (R 7) [36,96,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37445 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 226, targets := 1 },{ cop := 4, region := 392, targets := 64 }], pairs := [(1,0),(2,5),(3,5),(3,6)], upper := (rows 37 98 76 265 19 178 210 146 402), lower := (rows 37 98 76 265 19 32 64 128 256), losses := [] }

theorem u37445 : Upper (D 7) (R 7) [36,96,72,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37446 : Route 9 := (fun mask => (mask,id))

def c37446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37446 : Upper (D 7) (R 7) [36,96,72,257,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,129] 13 (by decide) (choices 1) [2,16,128] r37446 c37446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23907
  · exact u23908
  · exact u23909

def r37447 : Route 9 := (fun mask => (mask,id))

def c37447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37447 : Upper (D 7) (R 7) [36,96,72,257,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,130] 13 (by decide) (choices 1) [1,2,16,128] r37447 c37447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23910
  · exact u23911
  · exact u23912
  · exact u23913

def r37448 : Route 9 := (fun mask => (mask,id))

def c37448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37448 : Upper (D 7) (R 7) [36,96,72,258,3] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,3] 13 (by decide) (choices 1) [1,16,128] r37448 c37448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23914
  · exact u23915
  · exact u23916

def r37449 : Route 9 := (fun mask => (mask,id))

def c37449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37449 : Upper (D 7) (R 7) [36,96,72,258,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,129] 13 (by decide) (choices 1) [1,2,16,128] r37449 c37449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23917
  · exact u23918
  · exact u23919
  · exact u23920

def r37450 : Route 9 := (fun mask => (mask,id))

def c37450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37450 : Upper (D 7) (R 7) [36,96,72,258,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,130] 13 (by decide) (choices 1) [1,16,128] r37450 c37450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23921
  · exact u23922
  · exact u23923

def r37451 : Route 9 := (fun mask => (mask,id))

def c37451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37451 : Upper (D 7) (R 7) [36,96,72,272,3] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,3] 13 (by decide) (choices 1) [1,2,128] r37451 c37451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23924
  · exact u23925
  · exact u23926

def r37452 : Route 9 := (fun mask => (mask,id))

def c37452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37452 : Upper (D 7) (R 7) [36,96,72,272,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,129] 13 (by decide) (choices 1) [1,2,128] r37452 c37452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23927
  · exact u23928
  · exact u23929

def r37453 : Route 9 := (fun mask => (mask,id))

def c37453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37453 : Upper (D 7) (R 7) [36,96,72,272,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,130] 13 (by decide) (choices 1) [1,2,128] r37453 c37453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23930
  · exact u23931
  · exact u23932

def r37454 : Route 9 := (fun mask => (mask,id))

def c37454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37454 : Upper (D 7) (R 7) [36,96,72,384,3] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,3] 13 (by decide) (choices 1) [1,2,16,128] r37454 c37454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23933
  · exact u23934
  · exact u23935
  · exact u23936

def r37455 : Route 9 := (fun mask => (mask,id))

def c37455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37455 : Upper (D 7) (R 7) [36,96,72,384,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,129] 13 (by decide) (choices 1) [1,2,16] r37455 c37455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23937
  · exact u23938
  · exact u23939

def r37456 : Route 9 := (fun mask => (mask,id))

def c37456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37456 : Upper (D 7) (R 7) [36,96,72,384,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,130] 13 (by decide) (choices 1) [1,2,16] r37456 c37456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23940
  · exact u23941
  · exact u23942

def b37457 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 26 496 464 464 464), lower := (rows 37 98 133 11 26 32 64 128 256), losses := [] }

theorem u37457 : Upper (D 7) (R 7) [36,96,129,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37458 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 88 434 466 402 402), lower := (rows 37 98 133 11 88 32 64 128 256), losses := [] }

theorem u37458 : Upper (D 7) (R 7) [36,96,129,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37459 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 146 376 344 472 344), lower := (rows 37 98 133 11 146 32 64 128 256), losses := [] }

theorem u37459 : Upper (D 7) (R 7) [36,96,129,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37460 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 152 370 338 466 338), lower := (rows 37 98 133 11 152 32 64 128 256), losses := [] }

theorem u37460 : Upper (D 7) (R 7) [36,96,129,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37461 : PairBound 9 := { available := 282, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 208 314 346 410 282), lower := (rows 37 98 133 11 208 32 64 128 256), losses := [] }

theorem u37461 : Upper (D 7) (R 7) [36,96,129,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37462 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 274 248 216 216 472), lower := (rows 37 98 133 11 274 32 64 128 256), losses := [] }

theorem u37462 : Upper (D 7) (R 7) [36,96,129,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37463 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 280 242 210 210 466), lower := (rows 37 98 133 11 280 32 64 128 256), losses := [] }

theorem u37463 : Upper (D 7) (R 7) [36,96,129,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37464 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 336 186 218 154 410), lower := (rows 37 98 133 11 336 32 64 128 256), losses := [] }

theorem u37464 : Upper (D 7) (R 7) [36,96,129,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37465 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 400 122 90 218 346), lower := (rows 37 98 133 11 400 32 64 128 256), losses := [] }

theorem u37465 : Upper (D 7) (R 7) [36,96,129,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37466 : Route 9 := (fun mask => (mask,id))

def c37466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u37466 : Upper (D 7) (R 7) [36,96,129,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,10] 13 (by decide) (choices 1) [2,64,128,256] r37466 c37466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23943
  · exact u23944
  · exact u23945
  · exact u23946

def b37467 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 133 25 82 426 458 394 394), lower := (rows 37 98 133 25 82 32 64 128 256), losses := [] }

theorem u37467 : Upper (D 7) (R 7) [36,96,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37468 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 98 133 25 88 418 450 386 386), lower := (rows 37 98 133 25 88 32 64 128 256), losses := [] }

theorem u37468 : Upper (D 7) (R 7) [36,96,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37469 : Route 9 := (fun mask => (mask,id))

def c37469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37469 : Upper (D 7) (R 7) [36,96,129,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,130] 13 (by decide) (choices 1) [2,8,64,256] r37469 c37469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23947
  · exact u23948
  · exact u23949
  · exact u23950

def b37470 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 133 25 152 354 322 450 322), lower := (rows 37 98 133 25 152 32 64 128 256), losses := [] }

theorem u37470 : Upper (D 7) (R 7) [36,96,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37471 : Route 9 := (fun mask => (mask,id))

def c37471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37471 : Upper (D 7) (R 7) [36,96,129,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,192] 13 (by decide) (choices 1) [2,8,256] r37471 c37471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23951
  · exact u23952
  · exact u23953

def r37472 : Route 9 := (fun mask => (mask,id))

def c37472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37472 : Upper (D 7) (R 7) [36,96,129,17,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,258] 13 (by decide) (choices 1) [2,8,64,128] r37472 c37472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23954
  · exact u23955
  · exact u23956
  · exact u23957

def r37473 : Route 9 := (fun mask => (mask,id))

def c37473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37473 : Upper (D 7) (R 7) [36,96,129,17,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,264] 13 (by decide) (choices 1) [2,64,128] r37473 c37473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23958
  · exact u23959
  · exact u23960

def r37474 : Route 9 := (fun mask => (mask,id))

def c37474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37474 : Upper (D 7) (R 7) [36,96,129,17,320] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,320] 13 (by decide) (choices 1) [2,8,128] r37474 c37474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23961
  · exact u23962
  · exact u23963

def r37475 : Route 9 := (fun mask => (mask,id))

def c37475 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37475 : Upper (D 7) (R 7) [36,96,129,17,384] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,384] 13 (by decide) (choices 1) [2,8,64] r37475 c37475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23964
  · exact u23965
  · exact u23966

def b37476 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 133 26 26 481 449 449 449), lower := (rows 37 98 133 26 26 32 64 128 256), losses := [] }

theorem u37476 : Upper (D 7) (R 7) [36,96,129,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37477 : PairBound 9 := { available := 394, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 133 26 81 426 458 394 394), lower := (rows 37 98 133 26 81 32 64 128 256), losses := [] }

theorem u37477 : Upper (D 7) (R 7) [36,96,129,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37478 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 133 26 82 425 457 393 393), lower := (rows 37 98 133 26 82 32 64 128 256), losses := [] }

theorem u37478 : Upper (D 7) (R 7) [36,96,129,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37479 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 133 26 88 419 451 387 387), lower := (rows 37 98 133 26 88 32 64 128 256), losses := [] }

theorem u37479 : Upper (D 7) (R 7) [36,96,129,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37480 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 133 26 145 362 330 458 330), lower := (rows 37 98 133 26 145 32 64 128 256), losses := [] }

theorem u37480 : Upper (D 7) (R 7) [36,96,129,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37481 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 133 26 146 361 329 457 329), lower := (rows 37 98 133 26 146 32 64 128 256), losses := [] }

theorem u37481 : Upper (D 7) (R 7) [36,96,129,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37482 : Route 9 := (fun mask => (mask,id))

def c37482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37482 : Upper (D 7) (R 7) [36,96,129,18,136] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,136] 13 (by decide) (choices 1) [1,2,64,256] r37482 c37482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23967
  · exact u23968
  · exact u23969
  · exact u23970

def r37483 : Route 9 := (fun mask => (mask,id))

def c37483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37483 : Upper (D 7) (R 7) [36,96,129,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,192] 13 (by decide) (choices 1) [1,2,8,256] r37483 c37483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23971
  · exact u23972
  · exact u23973
  · exact u23974

def r37484 : Route 9 := (fun mask => (mask,id))

def c37484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37484 : Upper (D 7) (R 7) [36,96,129,18,257] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,257] 13 (by decide) (choices 1) [2,8,64,128] r37484 c37484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23975
  · exact u23976
  · exact u23977
  · exact u23978

def b37485 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 133 26 274 233 201 201 457), lower := (rows 37 98 133 26 274 32 64 128 256), losses := [] }

theorem u37485 : Upper (D 7) (R 7) [36,96,129,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37486 : Route 9 := (fun mask => (mask,id))

def c37486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37486 : Upper (D 7) (R 7) [36,96,129,18,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,264] 13 (by decide) (choices 1) [1,2,64,128] r37486 c37486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23979
  · exact u23980
  · exact u23981
  · exact u23982

def r37487 : Route 9 := (fun mask => (mask,id))

def c37487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37487 : Upper (D 7) (R 7) [36,96,129,18,320] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,320] 13 (by decide) (choices 1) [1,2,8,128] r37487 c37487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23983
  · exact u23984
  · exact u23985
  · exact u23986

def r37488 : Route 9 := (fun mask => (mask,id))

def c37488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37488 : Upper (D 7) (R 7) [36,96,129,18,384] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,384] 13 (by decide) (choices 1) [1,2,8,64] r37488 c37488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23987
  · exact u23988
  · exact u23989
  · exact u23990

def r37489 : Route 9 := (fun mask => (mask,id))

def c37489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37489 : Upper (D 7) (R 7) [36,96,129,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,130] 13 (by decide) (choices 1) [2,8,16,256] r37489 c37489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23991
  · exact u23992
  · exact u23993
  · exact u23994

def r37490 : Route 9 := (fun mask => (mask,id))

def c37490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37490 : Upper (D 7) (R 7) [36,96,129,65,136] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,136] 13 (by decide) (choices 1) [2,16,256] r37490 c37490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23995
  · exact u23996
  · exact u23997

def r37491 : Route 9 := (fun mask => (mask,id))

def c37491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37491 : Upper (D 7) (R 7) [36,96,129,65,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,258] 13 (by decide) (choices 1) [2,8,16,128] r37491 c37491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23998
  · exact u23999
  · exact u24000
  · exact u24001

def r37492 : Route 9 := (fun mask => (mask,id))

def c37492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37492 : Upper (D 7) (R 7) [36,96,129,65,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,264] 13 (by decide) (choices 1) [2,16,128] r37492 c37492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24002
  · exact u24003
  · exact u24004

def r37493 : Route 9 := (fun mask => (mask,id))

def c37493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37493 : Upper (D 7) (R 7) [36,96,129,65,384] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,384] 13 (by decide) (choices 1) [2,8,16] r37493 c37493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24005
  · exact u24006
  · exact u24007

def b37494 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 146 313 345 409 281), lower := (rows 37 98 133 74 146 32 64 128 256), losses := [] }

theorem u37494 : Upper (D 7) (R 7) [36,96,129,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37495 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 152 307 339 403 275), lower := (rows 37 98 133 74 152 32 64 128 256), losses := [] }

theorem u37495 : Upper (D 7) (R 7) [36,96,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37496 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 273 186 218 154 410), lower := (rows 37 98 133 74 273 32 64 128 256), losses := [] }

theorem u37496 : Upper (D 7) (R 7) [36,96,129,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37497 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 274 185 217 153 409), lower := (rows 37 98 133 74 274 32 64 128 256), losses := [] }

theorem u37497 : Upper (D 7) (R 7) [36,96,129,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37498 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 280 179 211 147 403), lower := (rows 37 98 133 74 280 32 64 128 256), losses := [] }

theorem u37498 : Upper (D 7) (R 7) [36,96,129,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37499 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 400 59 91 155 283), lower := (rows 37 98 133 74 400 32 64 128 256), losses := [] }

theorem u37499 : Upper (D 7) (R 7) [36,96,129,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37499
end Delivery.IrregularNine14.P07
