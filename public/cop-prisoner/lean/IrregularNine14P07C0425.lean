import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0147
import IrregularNine14P07C0148

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25500 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 262 73 176 48 75 139 267), lower := (rows 37 194 262 73 176 48 64 128 256), losses := [] }

theorem u25500 : Upper (D 7) (R 7) [36,192,258,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25500 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25501 : Route 9 := (fun mask => (mask,id))

def c25501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25501 : Upper (D 7) (R 7) [36,192,258,80,160,1] 13 := by
  apply FastRouting.sound _ _ [36,192,258,80,160,1] 13 (by decide) (choices 1) [1,2,8] r25501 c25501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8874
  · exact u8875
  · exact u8876

def b25502 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 37 194 262 88 176 34 73 137 265), lower := (rows 37 194 262 88 176 34 64 128 256), losses := [] }

theorem u25502 : Upper (D 7) (R 7) [36,192,258,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25503 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 56, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 37 194 262 88 176 40 67 131 259), lower := (rows 37 194 262 88 176 40 64 128 256), losses := [] }

theorem u25503 : Upper (D 7) (R 7) [36,192,258,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25503 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25504 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 11 50 33 208 208 464), lower := (rows 37 194 268 11 50 33 64 128 256), losses := [] }

theorem u25504 : Upper (D 7) (R 7) [36,192,264,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25505 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 268 11 50 48 193 193 449), lower := (rows 37 194 268 11 50 48 64 128 256), losses := [] }

theorem u25505 : Upper (D 7) (R 7) [36,192,264,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25505 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25506 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 268 11 50 96 209 145 401), lower := (rows 37 194 268 11 50 96 64 128 256), losses := [] }

theorem u25506 : Upper (D 7) (R 7) [36,192,264,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25507 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(0,6),(1,0),(2,1),(4,1)], upper := (rows 37 194 268 11 81 34 240 176 432), lower := (rows 37 194 268 11 81 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 65 129 257), good := (rows 501 192 284 477 465 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 162 301 43 17 34 0 128 256) }] }

theorem u25507 : Upper (D 7) (R 7) [36,192,264,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25508 : Route 9 := (fun mask => (mask,id))

def c25508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25508 : Upper (D 7) (R 7) [36,192,264,3,65,16] 13 := by
  apply FastRouting.sound _ _ [36,192,264,3,65,16] 13 (by decide) (choices 1) [2,32,128] r25508 c25508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8877
  · exact u8878
  · exact u8879

def r25509 : Route 9 := (fun mask => (mask,id))

def c25509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25509 : Upper (D 7) (R 7) [36,192,264,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,264,3,65,128] 13 (by decide) (choices 1) [2,16,32] r25509 c25509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8880
  · exact u8881
  · exact u8882

def b25510 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 11 112 33 210 146 402), lower := (rows 37 194 268 11 112 33 64 128 256), losses := [] }

theorem u25510 : Upper (D 7) (R 7) [36,192,264,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25511 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,1),(4,0),(4,1),(4,7)], upper := (rows 37 194 268 11 112 34 209 145 401), lower := (rows 37 194 268 11 112 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 32 73 137 265), good := (rows 501 192 460 477 112 32 64 128 256) }] }

theorem u25511 : Upper (D 7) (R 7) [36,192,264,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25512 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 268 11 112 48 195 131 387), lower := (rows 37 194 268 11 112 48 64 128 256), losses := [] }

theorem u25512 : Upper (D 7) (R 7) [36,192,264,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25513 : Route 9 := (fun mask => (mask,id))

def c25513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25513 : Upper (D 7) (R 7) [36,192,264,3,96,128] 13 := by
  apply FastRouting.sound _ _ [36,192,264,3,96,128] 13 (by decide) (choices 1) [1,2,16] r25513 c25513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8883
  · exact u8884
  · exact u8885

def b25514 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 268 25 50 33 194 194 450), lower := (rows 37 194 268 25 50 33 64 128 256), losses := [] }

theorem u25514 : Upper (D 7) (R 7) [36,192,264,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25515 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 268 25 50 34 193 193 449), lower := (rows 37 194 268 25 50 34 64 128 256), losses := [] }

theorem u25515 : Upper (D 7) (R 7) [36,192,264,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25516 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 268 25 50 96 195 131 387), lower := (rows 37 194 268 25 50 96 64 128 256), losses := [] }

theorem u25516 : Upper (D 7) (R 7) [36,192,264,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25517 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 268 25 112 33 194 130 386), lower := (rows 37 194 268 25 112 33 64 128 256), losses := [] }

theorem u25517 : Upper (D 7) (R 7) [36,192,264,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25518 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,0),(4,7)], upper := (rows 37 194 268 25 112 34 195 131 387), lower := (rows 37 194 268 25 112 34 64 128 256), losses := [] }

theorem u25518 : Upper (D 7) (R 7) [36,192,264,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25519 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(1,5),(2,5),(4,0),(4,1)], upper := (rows 37 194 268 25 112 160 67 131 259), lower := (rows 37 194 268 25 112 160 64 128 256), losses := [] }

theorem u25519 : Upper (D 7) (R 7) [36,192,264,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25520 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 26 81 33 226 162 418), lower := (rows 37 194 268 26 81 33 64 128 256), losses := [] }

theorem u25520 : Upper (D 7) (R 7) [36,192,264,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25521 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(2,6),(4,1)], upper := (rows 37 194 268 26 81 34 225 161 417), lower := (rows 37 194 268 26 81 34 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 98 301 58 81 34 64 0 256) }] }

theorem u25521 : Upper (D 7) (R 7) [36,192,264,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25522 : Route 9 := (fun mask => (mask,id))

def c25522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25522 : Upper (D 7) (R 7) [36,192,264,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,264,18,65,128] 13 (by decide) (choices 1) [1,2,32] r25522 c25522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8886
  · exact u8887
  · exact u8888

def b25523 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 26 112 33 195 131 387), lower := (rows 37 194 268 26 112 33 64 128 256), losses := [] }

theorem u25523 : Upper (D 7) (R 7) [36,192,264,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25524 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 194 268 26 112 34 193 129 385), lower := (rows 37 194 268 26 112 34 64 128 256), losses := [] }

theorem u25524 : Upper (D 7) (R 7) [36,192,264,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25525 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 37 194 268 26 112 160 67 131 259), lower := (rows 37 194 268 26 112 160 64 128 256), losses := [] }

theorem u25525 : Upper (D 7) (R 7) [36,192,264,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25526 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 42 19 33 208 208 464), lower := (rows 37 194 268 42 19 33 64 128 256), losses := [] }

theorem u25526 : Upper (D 7) (R 7) [36,192,264,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25527 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 194 268 42 19 48 193 193 449), lower := (rows 37 194 268 42 19 48 64 128 256), losses := [] }

theorem u25527 : Upper (D 7) (R 7) [36,192,264,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25527 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25528 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 405, targets := 64 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 194 268 42 19 96 209 145 401), lower := (rows 37 194 268 42 19 96 64 128 256), losses := [] }

theorem u25528 : Upper (D 7) (R 7) [36,192,264,34,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25529 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 42 81 33 210 146 402), lower := (rows 37 194 268 42 81 33 64 128 256), losses := [] }

theorem u25529 : Upper (D 7) (R 7) [36,192,264,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25530 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 194 268 42 81 34 209 145 401), lower := (rows 37 194 268 42 81 34 64 128 256), losses := [] }

theorem u25530 : Upper (D 7) (R 7) [36,192,264,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25531 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 3, region := 389, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 37 194 268 42 81 48 195 131 387), lower := (rows 37 194 268 42 81 48 64 128 256), losses := [] }

theorem u25531 : Upper (D 7) (R 7) [36,192,264,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25531 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25532 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 194 268 42 81 160 83 147 275), lower := (rows 37 194 268 42 81 160 64 128 256), losses := [] }

theorem u25532 : Upper (D 7) (R 7) [36,192,264,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25533 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 268 56 19 33 194 194 450), lower := (rows 37 194 268 56 19 33 64 128 256), losses := [] }

theorem u25533 : Upper (D 7) (R 7) [36,192,264,48,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25534 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 37 194 268 56 19 34 193 193 449), lower := (rows 37 194 268 56 19 34 64 128 256), losses := [] }

theorem u25534 : Upper (D 7) (R 7) [36,192,264,48,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25535 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 194 268 56 19 96 195 131 387), lower := (rows 37 194 268 56 19 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 98 64 128 256), good := (rows 36 226 268 56 58 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 98 64 128 256), good := (rows 37 224 268 56 57 96 96 128 256) }] }

theorem u25535 : Upper (D 7) (R 7) [36,192,264,48,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25536 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 268 56 81 33 194 130 386), lower := (rows 37 194 268 56 81 33 64 128 256), losses := [] }

theorem u25536 : Upper (D 7) (R 7) [36,192,264,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25537 : Route 9 := (fun mask => (mask,id))

def c25537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25537 : Upper (D 7) (R 7) [36,192,264,48,65,2] 13 := by
  apply FastRouting.sound _ _ [36,192,264,48,65,2] 13 (by decide) (choices 1) [1,2,128] r25537 c25537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8889
  · exact u8890
  · exact u8891

def r25538 : Route 9 := (fun mask => (mask,id))

def c25538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25538 : Upper (D 7) (R 7) [36,192,264,48,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,264,48,65,128] 13 (by decide) (choices 1) [1,2] r25538 c25538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8892
  · exact u8893

def r25539 : Route 9 := (fun mask => (mask,id))

def c25539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u25539 : Upper (D 7) (R 7) [36,192,264,65,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,3,2] 13 (by decide) (choices 1) [16,32,128] r25539 c25539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8894
  · exact u8895
  · exact u8896

def r25540 : Route 9 := (fun mask => (mask,id))

def c25540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25540 : Upper (D 7) (R 7) [36,192,264,65,3,16] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,3,16] 13 (by decide) (choices 1) [2,32,128] r25540 c25540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8897
  · exact u8898
  · exact u8899

def r25541 : Route 9 := (fun mask => (mask,id))

def c25541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25541 : Upper (D 7) (R 7) [36,192,264,65,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,3,128] 13 (by decide) (choices 1) [2,16,32] r25541 c25541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8900
  · exact u8901
  · exact u8902

def b25542 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 73 50 33 210 146 402), lower := (rows 37 194 268 73 50 33 64 128 256), losses := [] }

theorem u25542 : Upper (D 7) (R 7) [36,192,264,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25543 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 268 73 50 34 209 145 401), lower := (rows 37 194 268 73 50 34 64 128 256), losses := [] }

theorem u25543 : Upper (D 7) (R 7) [36,192,264,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25544 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 268 73 50 48 195 131 387), lower := (rows 37 194 268 73 50 48 64 128 256), losses := [] }

theorem u25544 : Upper (D 7) (R 7) [36,192,264,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25544 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25545 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 268 73 50 160 83 147 275), lower := (rows 37 194 268 73 50 160 64 128 256), losses := [] }

theorem u25545 : Upper (D 7) (R 7) [36,192,264,65,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25546 : Route 9 := (fun mask => (mask,id))

def c25546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25546 : Upper (D 7) (R 7) [36,192,264,65,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,129,2] 13 (by decide) (choices 1) [2,16,32] r25546 c25546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8903
  · exact u8904
  · exact u8905

def r25547 : Route 9 := (fun mask => (mask,id))

def c25547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25547 : Upper (D 7) (R 7) [36,192,264,65,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,129,16] 13 (by decide) (choices 1) [2,32] r25547 c25547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8906
  · exact u8907

def b25548 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 73 176 33 82 146 274), lower := (rows 37 194 268 73 176 33 64 128 256), losses := [] }

theorem u25548 : Upper (D 7) (R 7) [36,192,264,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25549 : Route 9 := (fun mask => (mask,id))

def c25549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25549 : Upper (D 7) (R 7) [36,192,264,65,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,160,2] 13 (by decide) (choices 1) [1,2,16] r25549 c25549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8908
  · exact u8909
  · exact u8910

def b25550 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 268 73 176 48 67 131 259), lower := (rows 37 194 268 73 176 48 64 128 256), losses := [] }

theorem u25550 : Upper (D 7) (R 7) [36,192,264,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25550 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25551 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 88 19 33 226 162 418), lower := (rows 37 194 268 88 19 33 64 128 256), losses := [] }

theorem u25551 : Upper (D 7) (R 7) [36,192,264,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25552 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6),(2,1),(2,6),(3,1)], upper := (rows 37 194 268 88 19 34 225 161 417), lower := (rows 37 194 268 88 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 65 129 257), good := (rows 485 192 268 92 477 32 64 128 256) },{ target := 6, region := (rows 9 2 12 8 16 50 0 153 281), good := (rows 421 162 397 445 435 34 0 128 256) }] }

theorem u25552 : Upper (D 7) (R 7) [36,192,264,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25553 : Route 9 := (fun mask => (mask,id))

def c25553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25553 : Upper (D 7) (R 7) [36,192,264,80,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,264,80,3,128] 13 (by decide) (choices 1) [1,2,32] r25553 c25553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8911
  · exact u8912
  · exact u8913

def b25554 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 88 50 33 195 131 387), lower := (rows 37 194 268 88 50 33 64 128 256), losses := [] }

theorem u25554 : Upper (D 7) (R 7) [36,192,264,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25555 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 194 268 88 50 34 193 129 385), lower := (rows 37 194 268 88 50 34 64 128 256), losses := [] }

theorem u25555 : Upper (D 7) (R 7) [36,192,264,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25556 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 56, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 37 194 268 88 50 160 67 131 259), lower := (rows 37 194 268 88 50 160 64 128 256), losses := [] }

theorem u25556 : Upper (D 7) (R 7) [36,192,264,80,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25557 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 268 88 145 33 98 162 290), lower := (rows 37 194 268 88 145 33 64 128 256), losses := [] }

theorem u25557 : Upper (D 7) (R 7) [36,192,264,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25558 : Route 9 := (fun mask => (mask,id))

def c25558 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25558 : Upper (D 7) (R 7) [36,192,264,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,264,80,129,2] 13 (by decide) (choices 1) [1,2,32] r25558 c25558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8914
  · exact u8915
  · exact u8916

def b25559 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 88 176 33 67 131 259), lower := (rows 37 194 268 88 176 33 64 128 256), losses := [] }

theorem u25559 : Upper (D 7) (R 7) [36,192,264,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25559
end Delivery.IrregularNine14.P07
