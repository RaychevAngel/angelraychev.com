import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0074
import IrregularNine14P08C0075

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13500 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 137 152 112 112 240 368), lower := (rows 97 7 262 137 152 32 64 128 256), losses := [] }

theorem u13500 : Upper (D 8) (R 8) [96,5,258,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13501 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 262 137 176 120 120 248 376), lower := (rows 97 7 262 137 176 32 64 128 256), losses := [] }

theorem u13501 : Upper (D 8) (R 8) [96,5,258,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13502 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 262 137 208 56 120 184 312), lower := (rows 97 7 262 137 208 32 64 128 256), losses := [] }

theorem u13502 : Upper (D 8) (R 8) [96,5,258,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13503 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 152 152 97 97 225 353), lower := (rows 97 7 262 152 152 32 64 128 256), losses := [] }

theorem u13503 : Upper (D 8) (R 8) [96,5,258,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13504 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 152 176 105 105 233 361), lower := (rows 97 7 262 152 176 32 64 128 256), losses := [] }

theorem u13504 : Upper (D 8) (R 8) [96,5,258,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13505 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 152 208 41 105 169 297), lower := (rows 97 7 262 152 208 32 64 128 256), losses := [] }

theorem u13505 : Upper (D 8) (R 8) [96,5,258,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13506 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 262 168 176 121 89 217 345), lower := (rows 97 7 262 168 176 32 64 128 256), losses := [] }

theorem u13506 : Upper (D 8) (R 8) [96,5,258,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13507 : Route 9 := (fun mask => (mask,id))

def c13507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13507 : Upper (D 8) (R 8) [96,5,258,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,258,160,192] 13 (by decide) (choices 1) [1,8,16] r13507 c13507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4479
  · exact u4480
  · exact u4481

def b13508 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 26 49 224 224 224 480), lower := (rows 97 7 268 26 49 32 64 128 256), losses := [] }

theorem u13508 : Upper (D 8) (R 8) [96,5,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13509 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 26 81 160 224 160 416), lower := (rows 97 7 268 26 81 32 64 128 256), losses := [] }

theorem u13509 : Upper (D 8) (R 8) [96,5,264,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13510 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 26 112 161 225 161 417), lower := (rows 97 7 268 26 112 32 64 128 256), losses := [] }

theorem u13510 : Upper (D 8) (R 8) [96,5,264,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13511 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 268 26 145 224 224 224 480), lower := (rows 97 7 268 26 145 32 64 128 256), losses := [] }

theorem u13511 : Upper (D 8) (R 8) [96,5,264,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13512 : Route 9 := (fun mask => (mask,id))

def c13512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13512 : Upper (D 8) (R 8) [96,5,264,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,264,18,160] 13 (by decide) (choices 1) [1,64,128] r13512 c13512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4482
  · exact u4483
  · exact u4484

def b13513 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 268 26 208 161 225 161 417), lower := (rows 97 7 268 26 208 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 268 446 144 32 0 128 256) }] }

theorem u13513 : Upper (D 8) (R 8) [96,5,264,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13514 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 41 50 240 208 208 464), lower := (rows 97 7 268 41 50 32 64 128 256), losses := [] }

theorem u13514 : Upper (D 8) (R 8) [96,5,264,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13515 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 41 82 176 240 176 432), lower := (rows 97 7 268 41 82 32 64 128 256), losses := [] }

theorem u13515 : Upper (D 8) (R 8) [96,5,264,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13516 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 41 146 240 240 240 496), lower := (rows 97 7 268 41 146 32 64 128 256), losses := [] }

theorem u13516 : Upper (D 8) (R 8) [96,5,264,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13517 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 41 176 242 210 210 466), lower := (rows 97 7 268 41 176 32 64 128 256), losses := [] }

theorem u13517 : Upper (D 8) (R 8) [96,5,264,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13518 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 41 208 178 242 178 434), lower := (rows 97 7 268 41 208 32 64 128 256), losses := [] }

theorem u13518 : Upper (D 8) (R 8) [96,5,264,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13519 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 42 49 240 208 208 464), lower := (rows 97 7 268 42 49 32 64 128 256), losses := [] }

theorem u13519 : Upper (D 8) (R 8) [96,5,264,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13520 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 42 81 176 240 176 432), lower := (rows 97 7 268 42 81 32 64 128 256), losses := [] }

theorem u13520 : Upper (D 8) (R 8) [96,5,264,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13521 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 42 112 177 209 145 401), lower := (rows 97 7 268 42 112 32 64 128 256), losses := [] }

theorem u13521 : Upper (D 8) (R 8) [96,5,264,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13522 : Route 9 := (fun mask => (mask,id))

def c13522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13522 : Upper (D 8) (R 8) [96,5,264,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,264,34,129] 13 (by decide) (choices 1) [16,64,128] r13522 c13522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4485
  · exact u4486
  · exact u4487

def r13523 : Route 9 := (fun mask => (mask,id))

def c13523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13523 : Upper (D 8) (R 8) [96,5,264,34,160] 13 := by
  apply FastRouting.sound _ _ [96,5,264,34,160] 13 (by decide) (choices 1) [1,16,64,128] r13523 c13523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4488
  · exact u4489
  · exact u4490
  · exact u4491

def r13524 : Route 9 := (fun mask => (mask,id))

def c13524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13524 : Upper (D 8) (R 8) [96,5,264,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,264,34,192] 13 (by decide) (choices 1) [1,16,128] r13524 c13524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4492
  · exact u4493
  · exact u4494

def b13525 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 56 49 226 194 194 450), lower := (rows 97 7 268 56 49 32 64 128 256), losses := [] }

theorem u13525 : Upper (D 8) (R 8) [96,5,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13526 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 56 50 225 193 193 449), lower := (rows 97 7 268 56 50 32 64 128 256), losses := [] }

theorem u13526 : Upper (D 8) (R 8) [96,5,264,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13527 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 56 81 162 226 162 418), lower := (rows 97 7 268 56 81 32 64 128 256), losses := [] }

theorem u13527 : Upper (D 8) (R 8) [96,5,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13528 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 268 56 82 161 225 161 417), lower := (rows 97 7 268 56 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 268 60 446 32 0 128 256) }] }

theorem u13528 : Upper (D 8) (R 8) [96,5,264,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13529 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 56 112 163 195 131 387), lower := (rows 97 7 268 56 112 32 64 128 256), losses := [] }

theorem u13529 : Upper (D 8) (R 8) [96,5,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13530 : Route 9 := (fun mask => (mask,id))

def c13530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13530 : Upper (D 8) (R 8) [96,5,264,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,264,48,129] 13 (by decide) (choices 1) [2,64,128] r13530 c13530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4495
  · exact u4496
  · exact u4497

def r13531 : Route 9 := (fun mask => (mask,id))

def c13531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13531 : Upper (D 8) (R 8) [96,5,264,48,130] 13 := by
  apply FastRouting.sound _ _ [96,5,264,48,130] 13 (by decide) (choices 1) [1,64,128] r13531 c13531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4498
  · exact u4499
  · exact u4500

def b13532 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 56 176 227 195 195 451), lower := (rows 97 7 268 56 176 32 64 128 256), losses := [] }

theorem u13532 : Upper (D 8) (R 8) [96,5,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13533 : Route 9 := (fun mask => (mask,id))

def c13533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13533 : Upper (D 8) (R 8) [96,5,264,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,264,48,192] 13 (by decide) (choices 1) [1,2,128] r13533 c13533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4501
  · exact u4502
  · exact u4503

def b13534 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 73 50 176 240 176 432), lower := (rows 97 7 268 73 50 32 64 128 256), losses := [] }

theorem u13534 : Upper (D 8) (R 8) [96,5,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13535 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 73 146 176 240 176 432), lower := (rows 97 7 268 73 146 32 64 128 256), losses := [] }

theorem u13535 : Upper (D 8) (R 8) [96,5,264,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13536 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 73 176 178 242 178 434), lower := (rows 97 7 268 73 176 32 64 128 256), losses := [] }

theorem u13536 : Upper (D 8) (R 8) [96,5,264,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13537 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 74 145 176 240 176 432), lower := (rows 97 7 268 74 145 32 64 128 256), losses := [] }

theorem u13537 : Upper (D 8) (R 8) [96,5,264,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13538 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 74 176 177 241 177 433), lower := (rows 97 7 268 74 176 32 64 128 256), losses := [] }

theorem u13538 : Upper (D 8) (R 8) [96,5,264,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13539 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 88 50 161 225 161 417), lower := (rows 97 7 268 88 50 32 64 128 256), losses := [] }

theorem u13539 : Upper (D 8) (R 8) [96,5,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13540 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 88 145 162 226 162 418), lower := (rows 97 7 268 88 145 32 64 128 256), losses := [] }

theorem u13540 : Upper (D 8) (R 8) [96,5,264,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13541 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 88 146 161 225 161 417), lower := (rows 97 7 268 88 146 32 64 128 256), losses := [] }

theorem u13541 : Upper (D 8) (R 8) [96,5,264,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13542 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 88 176 163 227 163 419), lower := (rows 97 7 268 88 176 32 64 128 256), losses := [] }

theorem u13542 : Upper (D 8) (R 8) [96,5,264,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13543 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 104 50 177 209 145 401), lower := (rows 97 7 268 104 50 32 64 128 256), losses := [] }

theorem u13543 : Upper (D 8) (R 8) [96,5,264,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13544 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 104 145 178 242 178 434), lower := (rows 97 7 268 104 145 32 64 128 256), losses := [] }

theorem u13544 : Upper (D 8) (R 8) [96,5,264,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13545 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 104 146 177 241 177 433), lower := (rows 97 7 268 104 146 32 64 128 256), losses := [] }

theorem u13545 : Upper (D 8) (R 8) [96,5,264,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13546 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 104 176 179 211 147 403), lower := (rows 97 7 268 104 176 32 64 128 256), losses := [] }

theorem u13546 : Upper (D 8) (R 8) [96,5,264,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13547 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 137 50 240 240 240 496), lower := (rows 97 7 268 137 50 32 64 128 256), losses := [] }

theorem u13547 : Upper (D 8) (R 8) [96,5,264,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13548 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 137 82 176 240 176 432), lower := (rows 97 7 268 137 82 32 64 128 256), losses := [] }

theorem u13548 : Upper (D 8) (R 8) [96,5,264,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13549 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 137 146 112 112 240 368), lower := (rows 97 7 268 137 146 32 64 128 256), losses := [] }

theorem u13549 : Upper (D 8) (R 8) [96,5,264,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13550 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 137 176 114 114 242 370), lower := (rows 97 7 268 137 176 32 64 128 256), losses := [] }

theorem u13550 : Upper (D 8) (R 8) [96,5,264,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13551 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 137 208 50 114 178 306), lower := (rows 97 7 268 137 208 32 64 128 256), losses := [] }

theorem u13551 : Upper (D 8) (R 8) [96,5,264,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13552 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 138 49 240 240 240 496), lower := (rows 97 7 268 138 49 32 64 128 256), losses := [] }

theorem u13552 : Upper (D 8) (R 8) [96,5,264,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13553 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 138 81 176 240 176 432), lower := (rows 97 7 268 138 81 32 64 128 256), losses := [] }

theorem u13553 : Upper (D 8) (R 8) [96,5,264,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13554 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 138 112 177 241 177 433), lower := (rows 97 7 268 138 112 32 64 128 256), losses := [] }

theorem u13554 : Upper (D 8) (R 8) [96,5,264,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13555 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 138 145 112 112 240 368), lower := (rows 97 7 268 138 145 32 64 128 256), losses := [] }

theorem u13555 : Upper (D 8) (R 8) [96,5,264,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13556 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 138 176 113 113 241 369), lower := (rows 97 7 268 138 176 32 64 128 256), losses := [] }

theorem u13556 : Upper (D 8) (R 8) [96,5,264,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13557 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 138 208 49 113 177 305), lower := (rows 97 7 268 138 208 32 64 128 256), losses := [] }

theorem u13557 : Upper (D 8) (R 8) [96,5,264,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13558 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 152 49 226 226 226 482), lower := (rows 97 7 268 152 49 32 64 128 256), losses := [] }

theorem u13558 : Upper (D 8) (R 8) [96,5,264,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13559 : Route 9 := (fun mask => (mask,id))

def c13559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13559 : Upper (D 8) (R 8) [96,5,264,144,34] 13 := by
  apply FastRouting.sound _ _ [96,5,264,144,34] 13 (by decide) (choices 1) [1,64,128] r13559 c13559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4504
  · exact u4505
  · exact u4506

#print axioms u13559
end Delivery.IrregularNine14.P08
