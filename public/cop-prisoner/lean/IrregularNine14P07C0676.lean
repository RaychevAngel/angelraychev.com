import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0489
import IrregularNine14P07C0490
import IrregularNine14P07C0491

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40560 : Route 9 := (fun mask => (mask,id))

def c40560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40560 : Upper (D 7) (R 7) [96,260,160,66,136] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,136] 13 (by decide) (choices 1) [1,2,16] r40560 c40560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29368
  · exact u29369
  · exact u29370

def r40561 : Route 9 := (fun mask => (mask,id))

def c40561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40561 : Upper (D 7) (R 7) [96,260,160,80,129] 13 := by
  apply FastRouting.sound _ _ [96,260,160,80,129] 13 (by decide) (choices 1) [1,2,8] r40561 c40561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29371
  · exact u29372
  · exact u29373

def r40562 : Route 9 := (fun mask => (mask,id))

def c40562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40562 : Upper (D 7) (R 7) [96,260,160,80,130] 13 := by
  apply FastRouting.sound _ _ [96,260,160,80,130] 13 (by decide) (choices 1) [1,2,8] r40562 c40562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29374
  · exact u29375
  · exact u29376

def b40563 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(2,6)], upper := (rows 97 262 164 88 152 35 67 131 259), lower := (rows 97 262 164 88 152 32 64 128 256), losses := [] }

theorem u40563 : Upper (D 7) (R 7) [96,260,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40564 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 290 7 11 28 240 208 208 464), lower := (rows 97 290 7 11 28 32 64 128 256), losses := [] }

theorem u40564 : Upper (D 7) (R 7) [96,288,3,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40565 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 290 7 11 84 184 216 152 408), lower := (rows 97 290 7 11 84 32 64 128 256), losses := [] }

theorem u40565 : Upper (D 7) (R 7) [96,288,3,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40566 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 290 7 11 148 248 216 216 472), lower := (rows 97 290 7 11 148 32 64 128 256), losses := [] }

theorem u40566 : Upper (D 7) (R 7) [96,288,3,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40567 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 290 7 11 208 188 220 156 412), lower := (rows 97 290 7 11 208 32 64 128 256), losses := [] }

theorem u40567 : Upper (D 7) (R 7) [96,288,3,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40568 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 290 7 13 26 240 208 208 464), lower := (rows 97 290 7 13 26 32 64 128 256), losses := [] }

theorem u40568 : Upper (D 7) (R 7) [96,288,3,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40569 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 13 82 184 216 152 408), lower := (rows 97 290 7 13 82 32 64 128 256), losses := [] }

theorem u40569 : Upper (D 7) (R 7) [96,288,3,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40570 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 13 88 178 210 146 402), lower := (rows 97 290 7 13 88 32 64 128 256), losses := [] }

theorem u40570 : Upper (D 7) (R 7) [96,288,3,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40571 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 13 146 248 216 216 472), lower := (rows 97 290 7 13 146 32 64 128 256), losses := [] }

theorem u40571 : Upper (D 7) (R 7) [96,288,3,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40572 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 13 152 242 210 210 466), lower := (rows 97 290 7 13 152 32 64 128 256), losses := [] }

theorem u40572 : Upper (D 7) (R 7) [96,288,3,5,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40573 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 13 208 186 218 154 410), lower := (rows 97 290 7 13 208 32 64 128 256), losses := [] }

theorem u40573 : Upper (D 7) (R 7) [96,288,3,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40574 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 290 7 14 25 240 208 208 464), lower := (rows 97 290 7 14 25 32 64 128 256), losses := [] }

theorem u40574 : Upper (D 7) (R 7) [96,288,3,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40575 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 193 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 14 88 177 209 145 401), lower := (rows 97 290 7 14 88 32 64 128 256), losses := [] }

theorem u40575 : Upper (D 7) (R 7) [96,288,3,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40576 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 193 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 14 145 248 216 216 472), lower := (rows 97 290 7 14 145 32 64 128 256), losses := [] }

theorem u40576 : Upper (D 7) (R 7) [96,288,3,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40577 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 193 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 14 152 241 209 209 465), lower := (rows 97 290 7 14 152 32 64 128 256), losses := [] }

theorem u40577 : Upper (D 7) (R 7) [96,288,3,6,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40578 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 193 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 14 208 185 217 153 409), lower := (rows 97 290 7 14 208 32 64 128 256), losses := [] }

theorem u40578 : Upper (D 7) (R 7) [96,288,3,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40579 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 290 7 25 26 228 196 196 452), lower := (rows 97 290 7 25 26 32 64 128 256), losses := [] }

theorem u40579 : Upper (D 7) (R 7) [96,288,3,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40580 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 290 7 25 28 226 194 194 450), lower := (rows 97 290 7 25 28 32 64 128 256), losses := [] }

theorem u40580 : Upper (D 7) (R 7) [96,288,3,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40581 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 290 7 25 82 172 204 140 396), lower := (rows 97 290 7 25 82 32 64 128 256), losses := [] }

theorem u40581 : Upper (D 7) (R 7) [96,288,3,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40582 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 290 7 25 84 170 202 138 394), lower := (rows 97 290 7 25 84 32 64 128 256), losses := [] }

theorem u40582 : Upper (D 7) (R 7) [96,288,3,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40583 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 97 290 7 25 88 166 198 134 390), lower := (rows 97 290 7 25 88 32 64 128 256), losses := [] }

theorem u40583 : Upper (D 7) (R 7) [96,288,3,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40584 : Route 9 := (fun mask => (mask,id))

def c40584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40584 : Upper (D 7) (R 7) [96,288,3,17,130] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,130] 13 (by decide) (choices 1) [4,8,64,128] r40584 c40584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29377
  · exact u29378
  · exact u29379
  · exact u29380

def r40585 : Route 9 := (fun mask => (mask,id))

def c40585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40585 : Upper (D 7) (R 7) [96,288,3,17,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,132] 13 (by decide) (choices 1) [2,8,64,128] r40585 c40585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29381
  · exact u29382
  · exact u29383
  · exact u29384

def r40586 : Route 9 := (fun mask => (mask,id))

def c40586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40586 : Upper (D 7) (R 7) [96,288,3,17,136] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,136] 13 (by decide) (choices 1) [2,4,64,128] r40586 c40586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29385
  · exact u29386
  · exact u29387
  · exact u29388

def b40587 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 290 7 25 208 174 206 142 398), lower := (rows 97 290 7 25 208 32 64 128 256), losses := [] }

theorem u40587 : Upper (D 7) (R 7) [96,288,3,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40588 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 97 290 7 26 28 225 193 193 449), lower := (rows 97 290 7 26 28 32 64 128 256), losses := [] }

theorem u40588 : Upper (D 7) (R 7) [96,288,3,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40589 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 7 26 81 172 204 140 396), lower := (rows 97 290 7 26 81 32 64 128 256), losses := [] }

theorem u40589 : Upper (D 7) (R 7) [96,288,3,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40590 : Route 9 := (fun mask => (mask,id))

def c40590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40590 : Upper (D 7) (R 7) [96,288,3,18,68] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,68] 13 (by decide) (choices 1) [1,8,128] r40590 c40590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29389
  · exact u29390
  · exact u29391

def b40591 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 290 7 26 88 165 197 133 389), lower := (rows 97 290 7 26 88 32 64 128 256), losses := [] }

theorem u40591 : Upper (D 7) (R 7) [96,288,3,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40592 : Route 9 := (fun mask => (mask,id))

def c40592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40592 : Upper (D 7) (R 7) [96,288,3,18,129] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,129] 13 (by decide) (choices 1) [4,8,64,128] r40592 c40592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29392
  · exact u29393
  · exact u29394
  · exact u29395

def r40593 : Route 9 := (fun mask => (mask,id))

def c40593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40593 : Upper (D 7) (R 7) [96,288,3,18,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,132] 13 (by decide) (choices 1) [1,8,64,128] r40593 c40593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29396
  · exact u29397
  · exact u29398
  · exact u29399

def r40594 : Route 9 := (fun mask => (mask,id))

def c40594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40594 : Upper (D 7) (R 7) [96,288,3,18,136] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,136] 13 (by decide) (choices 1) [1,4,64,128] r40594 c40594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29400
  · exact u29401
  · exact u29402
  · exact u29403

def r40595 : Route 9 := (fun mask => (mask,id))

def c40595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40595 : Upper (D 7) (R 7) [96,288,3,18,192] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,192] 13 (by decide) (choices 1) [1,4,8,128] r40595 c40595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29404
  · exact u29405
  · exact u29406
  · exact u29407

def b40596 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 7 28 81 170 202 138 394), lower := (rows 97 290 7 28 81 32 64 128 256), losses := [] }

theorem u40596 : Upper (D 7) (R 7) [96,288,3,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40597 : Route 9 := (fun mask => (mask,id))

def c40597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40597 : Upper (D 7) (R 7) [96,288,3,20,66] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,66] 13 (by decide) (choices 1) [1,8,128] r40597 c40597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29408
  · exact u29409
  · exact u29410

def b40598 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 290 7 28 88 163 195 131 387), lower := (rows 97 290 7 28 88 32 64 128 256), losses := [] }

theorem u40598 : Upper (D 7) (R 7) [96,288,3,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40599 : Route 9 := (fun mask => (mask,id))

def c40599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40599 : Upper (D 7) (R 7) [96,288,3,20,129] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,129] 13 (by decide) (choices 1) [2,8,64,128] r40599 c40599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29411
  · exact u29412
  · exact u29413
  · exact u29414

def r40600 : Route 9 := (fun mask => (mask,id))

def c40600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40600 : Upper (D 7) (R 7) [96,288,3,20,130] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,130] 13 (by decide) (choices 1) [1,8,64,128] r40600 c40600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29415
  · exact u29416
  · exact u29417
  · exact u29418

def r40601 : Route 9 := (fun mask => (mask,id))

def c40601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40601 : Upper (D 7) (R 7) [96,288,3,20,136] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,136] 13 (by decide) (choices 1) [1,2,64,128] r40601 c40601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29419
  · exact u29420
  · exact u29421
  · exact u29422

def r40602 : Route 9 := (fun mask => (mask,id))

def c40602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40602 : Upper (D 7) (R 7) [96,288,3,20,192] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,192] 13 (by decide) (choices 1) [1,2,8,128] r40602 c40602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29423
  · exact u29424
  · exact u29425
  · exact u29426

def b40603 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 7 73 146 188 220 156 412), lower := (rows 97 290 7 73 146 32 64 128 256), losses := [] }

theorem u40603 : Upper (D 7) (R 7) [96,288,3,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40604 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 7 73 148 186 218 154 410), lower := (rows 97 290 7 73 148 32 64 128 256), losses := [] }

theorem u40604 : Upper (D 7) (R 7) [96,288,3,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40605 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 7 73 152 182 214 150 406), lower := (rows 97 290 7 73 152 32 64 128 256), losses := [] }

theorem u40605 : Upper (D 7) (R 7) [96,288,3,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40606 : Route 9 := (fun mask => (mask,id))

def c40606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40606 : Upper (D 7) (R 7) [96,288,3,66,129] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,129] 13 (by decide) (choices 1) [4,8,16,128] r40606 c40606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29427
  · exact u29428
  · exact u29429
  · exact u29430

def r40607 : Route 9 := (fun mask => (mask,id))

def c40607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40607 : Upper (D 7) (R 7) [96,288,3,66,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,132] 13 (by decide) (choices 1) [1,8,16,128] r40607 c40607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29431
  · exact u29432
  · exact u29433
  · exact u29434

def r40608 : Route 9 := (fun mask => (mask,id))

def c40608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40608 : Upper (D 7) (R 7) [96,288,3,66,136] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,136] 13 (by decide) (choices 1) [1,4,16,128] r40608 c40608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29435
  · exact u29436
  · exact u29437
  · exact u29438

def r40609 : Route 9 := (fun mask => (mask,id))

def c40609 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40609 : Upper (D 7) (R 7) [96,288,3,68,129] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68,129] 13 (by decide) (choices 1) [2,8,16,128] r40609 c40609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29439
  · exact u29440
  · exact u29441
  · exact u29442

def r40610 : Route 9 := (fun mask => (mask,id))

def c40610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40610 : Upper (D 7) (R 7) [96,288,3,68,130] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68,130] 13 (by decide) (choices 1) [1,8,16,128] r40610 c40610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29443
  · exact u29444
  · exact u29445
  · exact u29446

def r40611 : Route 9 := (fun mask => (mask,id))

def c40611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40611 : Upper (D 7) (R 7) [96,288,3,68,136] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68,136] 13 (by decide) (choices 1) [1,2,16,128] r40611 c40611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29447
  · exact u29448
  · exact u29449
  · exact u29450

def r40612 : Route 9 := (fun mask => (mask,id))

def c40612 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40612 : Upper (D 7) (R 7) [96,288,3,80,129] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,129] 13 (by decide) (choices 1) [2,4,8,128] r40612 c40612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29451
  · exact u29452
  · exact u29453
  · exact u29454

def r40613 : Route 9 := (fun mask => (mask,id))

def c40613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40613 : Upper (D 7) (R 7) [96,288,3,80,130] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,130] 13 (by decide) (choices 1) [1,4,8,128] r40613 c40613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29455
  · exact u29456
  · exact u29457
  · exact u29458

def r40614 : Route 9 := (fun mask => (mask,id))

def c40614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40614 : Upper (D 7) (R 7) [96,288,3,80,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,132] 13 (by decide) (choices 1) [1,2,8,128] r40614 c40614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29459
  · exact u29460
  · exact u29461
  · exact u29462

def b40615 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 290 7 88 152 167 199 135 391), lower := (rows 97 290 7 88 152 32 64 128 256), losses := [] }

theorem u40615 : Upper (D 7) (R 7) [96,288,3,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40616 : Route 9 := (fun mask => (mask,id))

def c40616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40616 : Upper (D 7) (R 7) [96,288,3,129,130] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129,130] 13 (by decide) (choices 1) [4,8,16,64] r40616 c40616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29463
  · exact u29464
  · exact u29465
  · exact u29466

def r40617 : Route 9 := (fun mask => (mask,id))

def c40617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40617 : Upper (D 7) (R 7) [96,288,3,129,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129,132] 13 (by decide) (choices 1) [2,8,16,64] r40617 c40617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29467
  · exact u29468
  · exact u29469
  · exact u29470

def b40618 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 290 7 137 152 118 86 214 342), lower := (rows 97 290 7 137 152 32 64 128 256), losses := [] }

theorem u40618 : Upper (D 7) (R 7) [96,288,3,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40619 : Route 9 := (fun mask => (mask,id))

def c40619 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40619 : Upper (D 7) (R 7) [96,288,3,129,192] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129,192] 13 (by decide) (choices 1) [2,4,8,16] r40619 c40619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29471
  · exact u29472
  · exact u29473
  · exact u29474

#print axioms u40619
end Delivery.IrregularNine14.P07
