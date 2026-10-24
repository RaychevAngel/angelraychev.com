import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0400
import IrregularNine14P07C0401
import IrregularNine14P07C0402

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37500 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 133 88 145 298 330 394 266), lower := (rows 37 98 133 88 145 32 64 128 256), losses := [] }

theorem u37500 : Upper (D 7) (R 7) [36,96,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37501 : Route 9 := (fun mask => (mask,id))

def c37501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37501 : Upper (D 7) (R 7) [36,96,129,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,130] 13 (by decide) (choices 1) [1,2,8,256] r37501 c37501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24008
  · exact u24009
  · exact u24010
  · exact u24011

def b37502 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 98 133 88 152 291 323 387 259), lower := (rows 37 98 133 88 152 32 64 128 256), losses := [] }

theorem u37502 : Upper (D 7) (R 7) [36,96,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37503 : Route 9 := (fun mask => (mask,id))

def c37503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37503 : Upper (D 7) (R 7) [36,96,129,80,257] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,257] 13 (by decide) (choices 1) [2,8,128] r37503 c37503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24012
  · exact u24013
  · exact u24014

def r37504 : Route 9 := (fun mask => (mask,id))

def c37504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37504 : Upper (D 7) (R 7) [36,96,129,80,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,258] 13 (by decide) (choices 1) [1,2,8,128] r37504 c37504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24015
  · exact u24016
  · exact u24017
  · exact u24018

def r37505 : Route 9 := (fun mask => (mask,id))

def c37505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37505 : Upper (D 7) (R 7) [36,96,129,80,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,264] 13 (by decide) (choices 1) [1,2,128] r37505 c37505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24019
  · exact u24020
  · exact u24021

def r37506 : Route 9 := (fun mask => (mask,id))

def c37506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37506 : Upper (D 7) (R 7) [36,96,129,80,384] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,384] 13 (by decide) (choices 1) [1,2,8] r37506 c37506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24022
  · exact u24023
  · exact u24024

def b37507 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 37 98 133 137 274 122 90 218 346), lower := (rows 37 98 133 137 274 32 64 128 256), losses := [] }

theorem u37507 : Upper (D 7) (R 7) [36,96,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37508 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 37 98 133 137 280 114 82 210 338), lower := (rows 37 98 133 137 280 32 64 128 256), losses := [] }

theorem u37508 : Upper (D 7) (R 7) [36,96,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37509 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 37 98 133 137 336 58 90 154 282), lower := (rows 37 98 133 137 336 32 64 128 256), losses := [] }

theorem u37509 : Upper (D 7) (R 7) [36,96,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37510 : Route 9 := (fun mask => (mask,id))

def c37510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37510 : Upper (D 7) (R 7) [36,96,129,130,257] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130,257] 13 (by decide) (choices 1) [2,8,16,64] r37510 c37510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24025
  · exact u24026
  · exact u24027
  · exact u24028

def r37511 : Route 9 := (fun mask => (mask,id))

def c37511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37511 : Upper (D 7) (R 7) [36,96,129,130,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130,258] 13 (by decide) (choices 1) [1,8,16,64] r37511 c37511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24029
  · exact u24030
  · exact u24031
  · exact u24032

def r37512 : Route 9 := (fun mask => (mask,id))

def c37512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37512 : Upper (D 7) (R 7) [36,96,129,130,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130,264] 13 (by decide) (choices 1) [1,2,16,64] r37512 c37512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24033
  · exact u24034
  · exact u24035
  · exact u24036

def r37513 : Route 9 := (fun mask => (mask,id))

def c37513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37513 : Upper (D 7) (R 7) [36,96,129,130,320] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130,320] 13 (by decide) (choices 1) [1,2,8,16] r37513 c37513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24037
  · exact u24038
  · exact u24039
  · exact u24040

def r37514 : Route 9 := (fun mask => (mask,id))

def c37514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37514 : Upper (D 7) (R 7) [36,96,129,144,257] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,257] 13 (by decide) (choices 1) [2,8,64] r37514 c37514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24041
  · exact u24042
  · exact u24043

def r37515 : Route 9 := (fun mask => (mask,id))

def c37515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37515 : Upper (D 7) (R 7) [36,96,129,144,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,258] 13 (by decide) (choices 1) [1,2,8,64] r37515 c37515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24044
  · exact u24045
  · exact u24046
  · exact u24047

def r37516 : Route 9 := (fun mask => (mask,id))

def c37516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37516 : Upper (D 7) (R 7) [36,96,129,144,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,264] 13 (by decide) (choices 1) [1,2,64] r37516 c37516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24048
  · exact u24049
  · exact u24050

def r37517 : Route 9 := (fun mask => (mask,id))

def c37517 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37517 : Upper (D 7) (R 7) [36,96,129,144,320] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,320] 13 (by decide) (choices 1) [1,2,8] r37517 c37517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24051
  · exact u24052
  · exact u24053

def r37518 : Route 9 := (fun mask => (mask,id))

def c37518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37518 : Upper (D 7) (R 7) [36,96,129,192,257] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,257] 13 (by decide) (choices 1) [2,8,16] r37518 c37518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24054
  · exact u24055
  · exact u24056

def r37519 : Route 9 := (fun mask => (mask,id))

def c37519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37519 : Upper (D 7) (R 7) [36,96,129,192,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,258] 13 (by decide) (choices 1) [1,2,8,16] r37519 c37519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24057
  · exact u24058
  · exact u24059
  · exact u24060

def r37520 : Route 9 := (fun mask => (mask,id))

def c37520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37520 : Upper (D 7) (R 7) [36,96,129,192,264] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,264] 13 (by decide) (choices 1) [1,2,16] r37520 c37520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24061
  · exact u24062
  · exact u24063

def b37521 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 134 11 25 496 464 464 464), lower := (rows 37 98 134 11 25 32 64 128 256), losses := [] }

theorem u37521 : Upper (D 7) (R 7) [36,96,130,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37522 : Route 9 := (fun mask => (mask,id))

def c37522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u37522 : Upper (D 7) (R 7) [36,96,130,3,65] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,65] 13 (by decide) (choices 1) [8,16,128,256] r37522 c37522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24064
  · exact u24065
  · exact u24066
  · exact u24067

def r37523 : Route 9 := (fun mask => (mask,id))

def c37523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37523 : Upper (D 7) (R 7) [36,96,130,3,72] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,72] 13 (by decide) (choices 1) [1,16,128,256] r37523 c37523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24068
  · exact u24069
  · exact u24070
  · exact u24071

def b37524 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 134 11 145 376 344 472 344), lower := (rows 37 98 134 11 145 32 64 128 256), losses := [] }

theorem u37524 : Upper (D 7) (R 7) [36,96,130,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37525 : Route 9 := (fun mask => (mask,id))

def c37525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37525 : Upper (D 7) (R 7) [36,96,130,3,136] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,136] 13 (by decide) (choices 1) [1,16,64,256] r37525 c37525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24072
  · exact u24073
  · exact u24074
  · exact u24075

def r37526 : Route 9 := (fun mask => (mask,id))

def c37526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37526 : Upper (D 7) (R 7) [36,96,130,3,192] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,192] 13 (by decide) (choices 1) [1,8,16,256] r37526 c37526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24076
  · exact u24077
  · exact u24078
  · exact u24079

def r37527 : Route 9 := (fun mask => (mask,id))

def c37527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u37527 : Upper (D 7) (R 7) [36,96,130,3,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,257] 13 (by decide) (choices 1) [8,16,64,128] r37527 c37527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24080
  · exact u24081
  · exact u24082
  · exact u24083

def r37528 : Route 9 := (fun mask => (mask,id))

def c37528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37528 : Upper (D 7) (R 7) [36,96,130,3,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,264] 13 (by decide) (choices 1) [1,16,64,128] r37528 c37528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24084
  · exact u24085
  · exact u24086
  · exact u24087

def r37529 : Route 9 := (fun mask => (mask,id))

def c37529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37529 : Upper (D 7) (R 7) [36,96,130,3,320] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,320] 13 (by decide) (choices 1) [1,8,16,128] r37529 c37529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24088
  · exact u24089
  · exact u24090
  · exact u24091

def r37530 : Route 9 := (fun mask => (mask,id))

def c37530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37530 : Upper (D 7) (R 7) [36,96,130,3,384] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3,384] 13 (by decide) (choices 1) [1,8,16,64] r37530 c37530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24092
  · exact u24093
  · exact u24094
  · exact u24095

def b37531 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 134 25 25 482 450 450 450), lower := (rows 37 98 134 25 25 32 64 128 256), losses := [] }

theorem u37531 : Upper (D 7) (R 7) [36,96,130,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37532 : Route 9 := (fun mask => (mask,id))

def c37532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u37532 : Upper (D 7) (R 7) [36,96,130,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,10] 13 (by decide) (choices 1) [1,64,128,256] r37532 c37532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24096
  · exact u24097
  · exact u24098
  · exact u24099

def b37533 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 134 25 81 426 458 394 394), lower := (rows 37 98 134 25 81 32 64 128 256), losses := [] }

theorem u37533 : Upper (D 7) (R 7) [36,96,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37534 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 134 25 82 425 457 393 393), lower := (rows 37 98 134 25 82 32 64 128 256), losses := [] }

theorem u37534 : Upper (D 7) (R 7) [36,96,130,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37535 : Route 9 := (fun mask => (mask,id))

def c37535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37535 : Upper (D 7) (R 7) [36,96,130,17,72] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,72] 13 (by decide) (choices 1) [1,2,128,256] r37535 c37535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24100
  · exact u24101
  · exact u24102
  · exact u24103

def b37536 : PairBound 9 := { available := 330, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 134 25 145 362 330 458 330), lower := (rows 37 98 134 25 145 32 64 128 256), losses := [] }

theorem u37536 : Upper (D 7) (R 7) [36,96,130,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37537 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 134 25 146 361 329 457 329), lower := (rows 37 98 134 25 146 32 64 128 256), losses := [] }

theorem u37537 : Upper (D 7) (R 7) [36,96,130,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37538 : Route 9 := (fun mask => (mask,id))

def c37538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37538 : Upper (D 7) (R 7) [36,96,130,17,136] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,136] 13 (by decide) (choices 1) [1,2,64,256] r37538 c37538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24104
  · exact u24105
  · exact u24106
  · exact u24107

def r37539 : Route 9 := (fun mask => (mask,id))

def c37539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37539 : Upper (D 7) (R 7) [36,96,130,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,192] 13 (by decide) (choices 1) [1,2,8,256] r37539 c37539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24108
  · exact u24109
  · exact u24110
  · exact u24111

def b37540 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 134 25 273 234 202 202 458), lower := (rows 37 98 134 25 273 32 64 128 256), losses := [] }

theorem u37540 : Upper (D 7) (R 7) [36,96,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37541 : Route 9 := (fun mask => (mask,id))

def c37541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37541 : Upper (D 7) (R 7) [36,96,130,17,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,258] 13 (by decide) (choices 1) [1,8,64,128] r37541 c37541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24112
  · exact u24113
  · exact u24114
  · exact u24115

def r37542 : Route 9 := (fun mask => (mask,id))

def c37542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37542 : Upper (D 7) (R 7) [36,96,130,17,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,264] 13 (by decide) (choices 1) [1,2,64,128] r37542 c37542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24116
  · exact u24117
  · exact u24118
  · exact u24119

def r37543 : Route 9 := (fun mask => (mask,id))

def c37543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37543 : Upper (D 7) (R 7) [36,96,130,17,320] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,320] 13 (by decide) (choices 1) [1,2,8,128] r37543 c37543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24120
  · exact u24121
  · exact u24122
  · exact u24123

def r37544 : Route 9 := (fun mask => (mask,id))

def c37544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37544 : Upper (D 7) (R 7) [36,96,130,17,384] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,384] 13 (by decide) (choices 1) [1,2,8,64] r37544 c37544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24124
  · exact u24125
  · exact u24126
  · exact u24127

def r37545 : Route 9 := (fun mask => (mask,id))

def c37545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37545 : Upper (D 7) (R 7) [36,96,130,18,65] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,65] 13 (by decide) (choices 1) [1,8,128,256] r37545 c37545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24128
  · exact u24129
  · exact u24130
  · exact u24131

def b37546 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 134 26 88 417 449 385 385), lower := (rows 37 98 134 26 88 32 64 128 256), losses := [] }

theorem u37546 : Upper (D 7) (R 7) [36,96,130,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37547 : Route 9 := (fun mask => (mask,id))

def c37547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37547 : Upper (D 7) (R 7) [36,96,130,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,129] 13 (by decide) (choices 1) [1,8,64,256] r37547 c37547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24132
  · exact u24133
  · exact u24134
  · exact u24135

def b37548 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 37 98 134 26 152 353 321 449 321), lower := (rows 37 98 134 26 152 32 64 128 256), losses := [] }

theorem u37548 : Upper (D 7) (R 7) [36,96,130,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37549 : Route 9 := (fun mask => (mask,id))

def c37549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37549 : Upper (D 7) (R 7) [36,96,130,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,192] 13 (by decide) (choices 1) [1,8,256] r37549 c37549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24136
  · exact u24137
  · exact u24138

def r37550 : Route 9 := (fun mask => (mask,id))

def c37550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37550 : Upper (D 7) (R 7) [36,96,130,18,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,257] 13 (by decide) (choices 1) [1,8,64,128] r37550 c37550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24139
  · exact u24140
  · exact u24141
  · exact u24142

def r37551 : Route 9 := (fun mask => (mask,id))

def c37551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37551 : Upper (D 7) (R 7) [36,96,130,18,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,264] 13 (by decide) (choices 1) [1,64,128] r37551 c37551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24143
  · exact u24144
  · exact u24145

def r37552 : Route 9 := (fun mask => (mask,id))

def c37552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37552 : Upper (D 7) (R 7) [36,96,130,18,320] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,320] 13 (by decide) (choices 1) [1,8,128] r37552 c37552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24146
  · exact u24147
  · exact u24148

def r37553 : Route 9 := (fun mask => (mask,id))

def c37553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37553 : Upper (D 7) (R 7) [36,96,130,18,384] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,384] 13 (by decide) (choices 1) [1,8,64] r37553 c37553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24149
  · exact u24150
  · exact u24151

def r37554 : Route 9 := (fun mask => (mask,id))

def c37554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37554 : Upper (D 7) (R 7) [36,96,130,65,129] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,129] 13 (by decide) (choices 1) [2,8,16,256] r37554 c37554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24152
  · exact u24153
  · exact u24154
  · exact u24155

def b37555 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 134 73 146 313 345 409 281), lower := (rows 37 98 134 73 146 32 64 128 256), losses := [] }

theorem u37555 : Upper (D 7) (R 7) [36,96,130,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37556 : Route 9 := (fun mask => (mask,id))

def c37556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37556 : Upper (D 7) (R 7) [36,96,130,65,136] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,136] 13 (by decide) (choices 1) [1,2,16,256] r37556 c37556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24156
  · exact u24157
  · exact u24158
  · exact u24159

def r37557 : Route 9 := (fun mask => (mask,id))

def c37557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37557 : Upper (D 7) (R 7) [36,96,130,65,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,257] 13 (by decide) (choices 1) [2,8,16,128] r37557 c37557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24160
  · exact u24161
  · exact u24162
  · exact u24163

def r37558 : Route 9 := (fun mask => (mask,id))

def c37558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37558 : Upper (D 7) (R 7) [36,96,130,65,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,258] 13 (by decide) (choices 1) [1,8,16,128] r37558 c37558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24164
  · exact u24165
  · exact u24166
  · exact u24167

def r37559 : Route 9 := (fun mask => (mask,id))

def c37559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37559 : Upper (D 7) (R 7) [36,96,130,65,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,264] 13 (by decide) (choices 1) [1,2,16,128] r37559 c37559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24168
  · exact u24169
  · exact u24170
  · exact u24171

#print axioms u37559
end Delivery.IrregularNine14.P07
