import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0200
import IrregularNine14P06C0201
import IrregularNine14P06C0202

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30480 : Route 9 := (fun mask => (mask,id))

def c30480 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30480 : Upper (D 6) (R 6) [10,33,65,20,160] 13 := by
  apply FastRouting.sound _ _ [10,33,65,20,160] 13 (by decide) (choices 1) [2,4,64,256] r30480 c30480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12045
  · exact u12046
  · exact u12047
  · exact u12048

def r30481 : Route 9 := (fun mask => (mask,id))

def c30481 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30481 : Upper (D 6) (R 6) [10,33,65,20,192] 13 := by
  apply FastRouting.sound _ _ [10,33,65,20,192] 13 (by decide) (choices 1) [2,4,256] r30481 c30481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12049
  · exact u12050
  · exact u12051

def r30482 : Route 9 := (fun mask => (mask,id))

def c30482 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30482 : Upper (D 6) (R 6) [10,33,65,20,384] 13 := by
  apply FastRouting.sound _ _ [10,33,65,20,384] 13 (by decide) (choices 1) [2,4,64] r30482 c30482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12052
  · exact u12053
  · exact u12054

def b30483 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 4, region := 488, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 35 69 88 22 420 484 420 420), lower := (rows 11 35 69 88 22 32 64 128 256), losses := [] }

theorem u30483 : Upper (D 6) (R 6) [10,33,65,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30484 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 88 50 420 452 388 388), lower := (rows 11 35 69 88 50 32 64 128 256), losses := [] }

theorem u30484 : Upper (D 6) (R 6) [10,33,65,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30485 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 35 69 88 52 422 454 390 390), lower := (rows 11 35 69 88 52 32 64 128 256), losses := [] }

theorem u30485 : Upper (D 6) (R 6) [10,33,65,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30486 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 35 69 88 146 292 356 420 292), lower := (rows 11 35 69 88 146 32 64 128 256), losses := [] }

theorem u30486 : Upper (D 6) (R 6) [10,33,65,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30487 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 35 69 88 148 294 358 422 294), lower := (rows 11 35 69 88 148 32 64 128 256), losses := [{ target := 6, region := (rows 9 14 4 8 20 52 0 148 276), good := (rows 11 35 439 443 438 32 0 128 256) }] }

theorem u30487 : Upper (D 6) (R 6) [10,33,65,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30488 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 35 69 88 176 294 326 390 262), lower := (rows 11 35 69 88 176 32 64 128 256), losses := [] }

theorem u30488 : Upper (D 6) (R 6) [10,33,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30489 : Route 9 := (fun mask => (mask,id))

def c30489 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30489 : Upper (D 6) (R 6) [10,33,65,80,384] 13 := by
  apply FastRouting.sound _ _ [10,33,65,80,384] 13 (by decide) (choices 1) [2,4] r30489 c30489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12055
  · exact u12056

def r30490 : Route 9 := (fun mask => (mask,id))

def c30490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30490 : Upper (D 6) (R 6) [10,33,65,132,6] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,6] 13 (by decide) (choices 1) [16,64,256] r30490 c30490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12057
  · exact u12058
  · exact u12059

def b30491 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 140 50 372 340 468 340), lower := (rows 11 35 69 140 50 32 64 128 256), losses := [] }

theorem u30491 : Upper (D 6) (R 6) [10,33,65,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30492 : Route 9 := (fun mask => (mask,id))

def c30492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30492 : Upper (D 6) (R 6) [10,33,65,132,36] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,36] 13 (by decide) (choices 1) [2,16,64,256] r30492 c30492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12060
  · exact u12061
  · exact u12062
  · exact u12063

def r30493 : Route 9 := (fun mask => (mask,id))

def c30493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30493 : Upper (D 6) (R 6) [10,33,65,132,66] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,66] 13 (by decide) (choices 1) [4,16,256] r30493 c30493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12064
  · exact u12065
  · exact u12066

def b30494 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 69 140 84 306 370 434 306), lower := (rows 11 35 69 140 84 32 64 128 256), losses := [] }

theorem u30494 : Upper (D 6) (R 6) [10,33,65,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30495 : Route 9 := (fun mask => (mask,id))

def c30495 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30495 : Upper (D 6) (R 6) [10,33,65,132,96] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,96] 13 (by decide) (choices 1) [2,4,16,256] r30495 c30495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12067
  · exact u12068
  · exact u12069
  · exact u12070

def r30496 : Route 9 := (fun mask => (mask,id))

def c30496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30496 : Upper (D 6) (R 6) [10,33,65,132,258] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,258] 13 (by decide) (choices 1) [4,16,64] r30496 c30496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12071
  · exact u12072
  · exact u12073

def r30497 : Route 9 := (fun mask => (mask,id))

def c30497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30497 : Upper (D 6) (R 6) [10,33,65,132,260] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,260] 13 (by decide) (choices 1) [2,16,64] r30497 c30497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12074
  · exact u12075
  · exact u12076

def r30498 : Route 9 := (fun mask => (mask,id))

def c30498 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30498 : Upper (D 6) (R 6) [10,33,65,132,288] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,288] 13 (by decide) (choices 1) [2,4,16,64] r30498 c30498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12077
  · exact u12078
  · exact u12079
  · exact u12080

def r30499 : Route 9 := (fun mask => (mask,id))

def c30499 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30499 : Upper (D 6) (R 6) [10,33,65,132,320] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,320] 13 (by decide) (choices 1) [2,4,16] r30499 c30499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12081
  · exact u12082
  · exact u12083

def b30500 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 35 69 152 22 356 356 484 356), lower := (rows 11 35 69 152 22 32 64 128 256), losses := [] }

theorem u30500 : Upper (D 6) (R 6) [10,33,65,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30501 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 152 50 356 324 452 324), lower := (rows 11 35 69 152 50 32 64 128 256), losses := [] }

theorem u30501 : Upper (D 6) (R 6) [10,33,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30502 : Route 9 := (fun mask => (mask,id))

def c30502 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30502 : Upper (D 6) (R 6) [10,33,65,144,36] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,36] 13 (by decide) (choices 1) [2,4,64,256] r30502 c30502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12084
  · exact u12085
  · exact u12086
  · exact u12087

def b30503 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 35 69 152 82 292 356 420 292), lower := (rows 11 35 69 152 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 55 87 151 279), good := (rows 493 485 485 504 508 32 64 128 256) }] }

theorem u30503 : Upper (D 6) (R 6) [10,33,65,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30504 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 69 152 84 294 358 422 294), lower := (rows 11 35 69 152 84 32 64 128 256), losses := [] }

theorem u30504 : Upper (D 6) (R 6) [10,33,65,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30505 : Route 9 := (fun mask => (mask,id))

def c30505 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30505 : Upper (D 6) (R 6) [10,33,65,144,96] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,96] 13 (by decide) (choices 1) [2,4,256] r30505 c30505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12088
  · exact u12089
  · exact u12090

def r30506 : Route 9 := (fun mask => (mask,id))

def c30506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30506 : Upper (D 6) (R 6) [10,33,65,144,258] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,258] 13 (by decide) (choices 1) [4,64] r30506 c30506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12091
  · exact u12092

def r30507 : Route 9 := (fun mask => (mask,id))

def c30507 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30507 : Upper (D 6) (R 6) [10,33,65,144,260] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,260] 13 (by decide) (choices 1) [2,4,64] r30507 c30507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12093
  · exact u12094
  · exact u12095

def r30508 : Route 9 := (fun mask => (mask,id))

def c30508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30508 : Upper (D 6) (R 6) [10,33,65,144,288] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,288] 13 (by decide) (choices 1) [2,4,64] r30508 c30508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12096
  · exact u12097
  · exact u12098

def r30509 : Route 9 := (fun mask => (mask,id))

def c30509 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30509 : Upper (D 6) (R 6) [10,33,65,144,320] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,320] 13 (by decide) (choices 1) [2,4] r30509 c30509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12099
  · exact u12100

def b30510 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 4, region := 488, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 35 69 200 22 308 372 436 308), lower := (rows 11 35 69 200 22 32 64 128 256), losses := [] }

theorem u30510 : Upper (D 6) (R 6) [10,33,65,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30511 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 200 50 308 340 404 276), lower := (rows 11 35 69 200 50 32 64 128 256), losses := [] }

theorem u30511 : Upper (D 6) (R 6) [10,33,65,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30512 : Route 9 := (fun mask => (mask,id))

def c30512 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30512 : Upper (D 6) (R 6) [10,33,65,192,36] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,36] 13 (by decide) (choices 1) [2,4,16,256] r30512 c30512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12101
  · exact u12102
  · exact u12103
  · exact u12104

def r30513 : Route 9 := (fun mask => (mask,id))

def c30513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30513 : Upper (D 6) (R 6) [10,33,65,192,258] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,258] 13 (by decide) (choices 1) [4,16] r30513 c30513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12105
  · exact u12106

def r30514 : Route 9 := (fun mask => (mask,id))

def c30514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30514 : Upper (D 6) (R 6) [10,33,65,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,260] 13 (by decide) (choices 1) [2,4,16] r30514 c30514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12107
  · exact u12108
  · exact u12109

def r30515 : Route 9 := (fun mask => (mask,id))

def c30515 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30515 : Upper (D 6) (R 6) [10,33,65,192,288] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,288] 13 (by decide) (choices 1) [2,4,16] r30515 c30515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12110
  · exact u12111
  · exact u12112

def r30516 : Route 9 := (fun mask => (mask,id))

def c30516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30516 : Upper (D 6) (R 6) [10,33,65,384,6] 13 := by
  apply FastRouting.sound _ _ [10,33,65,384,6] 13 (by decide) (choices 1) [4,16,64] r30516 c30516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12113
  · exact u12114
  · exact u12115

def b30517 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 392 50 116 84 212 340), lower := (rows 11 35 69 392 50 32 64 128 256), losses := [] }

theorem u30517 : Upper (D 6) (R 6) [10,33,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30518 : Route 9 := (fun mask => (mask,id))

def c30518 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30518 : Upper (D 6) (R 6) [10,33,65,384,36] 13 := by
  apply FastRouting.sound _ _ [10,33,65,384,36] 13 (by decide) (choices 1) [2,4,16,64] r30518 c30518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12116
  · exact u12117
  · exact u12118
  · exact u12119

def r30519 : Route 9 := (fun mask => (mask,id))

def c30519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30519 : Upper (D 6) (R 6) [10,33,65,384,66] 13 := by
  apply FastRouting.sound _ _ [10,33,65,384,66] 13 (by decide) (choices 1) [4,16] r30519 c30519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12120
  · exact u12121

def b30520 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 69 392 84 54 118 182 310), lower := (rows 11 35 69 392 84 32 64 128 256), losses := [] }

theorem u30520 : Upper (D 6) (R 6) [10,33,65,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30521 : Route 9 := (fun mask => (mask,id))

def c30521 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30521 : Upper (D 6) (R 6) [10,33,65,384,96] 13 := by
  apply FastRouting.sound _ _ [10,33,65,384,96] 13 (by decide) (choices 1) [2,4,16] r30521 c30521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12122
  · exact u12123
  · exact u12124

def b30522 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 28 21 480 480 480 480), lower := (rows 11 35 70 28 21 32 64 128 256), losses := [] }

theorem u30522 : Upper (D 6) (R 6) [10,33,66,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30523 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 70 28 49 484 452 452 452), lower := (rows 11 35 70 28 49 32 64 128 256), losses := [] }

theorem u30523 : Upper (D 6) (R 6) [10,33,66,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30524 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 70 28 52 481 449 449 449), lower := (rows 11 35 70 28 52 32 64 128 256), losses := [] }

theorem u30524 : Upper (D 6) (R 6) [10,33,66,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30525 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 28 81 420 484 420 420), lower := (rows 11 35 70 28 81 32 64 128 256), losses := [] }

theorem u30525 : Upper (D 6) (R 6) [10,33,66,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30526 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 28 84 417 481 417 417), lower := (rows 11 35 70 28 84 32 64 128 256), losses := [] }

theorem u30526 : Upper (D 6) (R 6) [10,33,66,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30527 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 70 28 112 421 453 389 389), lower := (rows 11 35 70 28 112 32 64 128 256), losses := [] }

theorem u30527 : Upper (D 6) (R 6) [10,33,66,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30528 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 35 70 28 145 356 356 484 356), lower := (rows 11 35 70 28 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 95 159 287), good := (rows 494 486 486 508 508 32 64 128 256) },{ target := 1, region := (rows 1 0 4 8 17 44 76 140 268), good := (rows 505 49 484 508 145 32 64 128 256) }] }

theorem u30528 : Upper (D 6) (R 6) [10,33,66,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30529 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 70 28 148 353 353 481 353), lower := (rows 11 35 70 28 148 32 64 128 256), losses := [] }

theorem u30529 : Upper (D 6) (R 6) [10,33,66,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30530 : Route 9 := (fun mask => (mask,id))

def c30530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30530 : Upper (D 6) (R 6) [10,33,66,20,160] 13 := by
  apply FastRouting.sound _ _ [10,33,66,20,160] 13 (by decide) (choices 1) [1,4,64,256] r30530 c30530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12125
  · exact u12126
  · exact u12127
  · exact u12128

def r30531 : Route 9 := (fun mask => (mask,id))

def c30531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30531 : Upper (D 6) (R 6) [10,33,66,20,192] 13 := by
  apply FastRouting.sound _ _ [10,33,66,20,192] 13 (by decide) (choices 1) [1,4,256] r30531 c30531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12129
  · exact u12130
  · exact u12131

def r30532 : Route 9 := (fun mask => (mask,id))

def c30532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30532 : Upper (D 6) (R 6) [10,33,66,20,384] 13 := by
  apply FastRouting.sound _ _ [10,33,66,20,384] 13 (by decide) (choices 1) [1,4,64] r30532 c30532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12132
  · exact u12133
  · exact u12134

def b30533 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 88 21 420 484 420 420), lower := (rows 11 35 70 88 21 32 64 128 256), losses := [] }

theorem u30533 : Upper (D 6) (R 6) [10,33,66,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30534 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 70 88 49 420 452 388 388), lower := (rows 11 35 70 88 49 32 64 128 256), losses := [] }

theorem u30534 : Upper (D 6) (R 6) [10,33,66,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30535 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c30535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30535 : Upper (D 6) (R 6) [10,33,66,80,36] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,36] 13 (by decide) (choices 1) [1,4,128] r30535 c30535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12135
  · exact u12136
  · exact u12137

def r30536 : Route 9 := (fun mask => (mask,id))

def c30536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30536 : Upper (D 6) (R 6) [10,33,66,80,129] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,129] 13 (by decide) (choices 1) [4,256] r30536 c30536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12138
  · exact u12139

def r30537 : Route 9 := (fun mask => (mask,id))

def c30537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30537 : Upper (D 6) (R 6) [10,33,66,80,132] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,132] 13 (by decide) (choices 1) [1,4,256] r30537 c30537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12140
  · exact u12141
  · exact u12142

def r30538 : Route 9 := (fun mask => (mask,id))

def c30538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30538 : Upper (D 6) (R 6) [10,33,66,80,160] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,160] 13 (by decide) (choices 1) [1,4,256] r30538 c30538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12143
  · exact u12144
  · exact u12145

def r30539 : Route 9 := (fun mask => (mask,id))

def c30539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30539 : Upper (D 6) (R 6) [10,33,66,80,384] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,384] 13 (by decide) (choices 1) [1,4] r30539 c30539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12146
  · exact u12147

#print axioms u30539
end Delivery.IrregularNine14.P06
