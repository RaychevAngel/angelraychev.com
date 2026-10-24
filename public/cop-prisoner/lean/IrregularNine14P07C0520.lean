import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0226
import IrregularNine14P07C0227
import IrregularNine14P07C0228

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31200 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 7 42 324 73 19 176 240 176 432), lower := (rows 7 42 324 73 19 32 64 128 256), losses := [] }

theorem u31200 : Upper (D 7) (R 7) [6,40,320,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31201 : Route 9 := (fun mask => (mask,id))

def c31201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31201 : Upper (D 7) (R 7) [6,40,320,65,33] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,33] 13 (by decide) (choices 1) [2,16,128] r31201 c31201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13594
  · exact u13595
  · exact u13596

def b31202 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 324 73 50 177 209 145 401), lower := (rows 7 42 324 73 50 32 64 128 256), losses := [] }

theorem u31202 : Upper (D 7) (R 7) [6,40,320,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31203 : Route 9 := (fun mask => (mask,id))

def c31203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31203 : Upper (D 7) (R 7) [6,40,320,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,129] 13 (by decide) (choices 1) [2,16,128] r31203 c31203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13597
  · exact u13598
  · exact u13599

def r31204 : Route 9 := (fun mask => (mask,id))

def c31204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31204 : Upper (D 7) (R 7) [6,40,320,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,130] 13 (by decide) (choices 1) [1,16,128] r31204 c31204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13600
  · exact u13601
  · exact u13602

def r31205 : Route 9 := (fun mask => (mask,id))

def c31205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31205 : Upper (D 7) (R 7) [6,40,320,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,160] 13 (by decide) (choices 1) [1,2,16,128] r31205 c31205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13603
  · exact u13604
  · exact u13605
  · exact u13606

def b31206 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 176, targets := 64 },{ cop := 4, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1),(4,6)], upper := (rows 7 42 324 74 49 177 209 145 401), lower := (rows 7 42 324 74 49 32 64 128 256), losses := [] }

theorem u31206 : Upper (D 7) (R 7) [6,40,320,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31207 : Route 9 := (fun mask => (mask,id))

def c31207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31207 : Upper (D 7) (R 7) [6,40,320,66,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,66,129] 13 (by decide) (choices 1) [1,16,128] r31207 c31207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13607
  · exact u13608
  · exact u13609

def r31208 : Route 9 := (fun mask => (mask,id))

def c31208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31208 : Upper (D 7) (R 7) [6,40,320,66,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,66,160] 13 (by decide) (choices 1) [1,16,128] r31208 c31208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13610
  · exact u13611
  · exact u13612

def b31209 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 324 88 19 161 225 161 417), lower := (rows 7 42 324 88 19 32 64 128 256), losses := [] }

theorem u31209 : Upper (D 7) (R 7) [6,40,320,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31210 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 324 88 49 163 195 131 387), lower := (rows 7 42 324 88 49 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 23 24 16 0 67 131 259), good := (rows 455 463 324 92 477 0 64 128 256) }] }

theorem u31210 : Upper (D 7) (R 7) [6,40,320,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31211 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 324 88 50 161 193 129 385), lower := (rows 7 42 324 88 50 32 64 128 256), losses := [] }

theorem u31211 : Upper (D 7) (R 7) [6,40,320,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31212 : Route 9 := (fun mask => (mask,id))

def c31212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31212 : Upper (D 7) (R 7) [6,40,320,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,80,129] 13 (by decide) (choices 1) [1,2,128] r31212 c31212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13613
  · exact u13614
  · exact u13615

def r31213 : Route 9 := (fun mask => (mask,id))

def c31213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31213 : Upper (D 7) (R 7) [6,40,320,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,320,80,130] 13 (by decide) (choices 1) [1,128] r31213 c31213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13616
  · exact u13617

def r31214 : Route 9 := (fun mask => (mask,id))

def c31214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31214 : Upper (D 7) (R 7) [6,40,320,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,80,160] 13 (by decide) (choices 1) [1,2,128] r31214 c31214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13618
  · exact u13619
  · exact u13620

def b31215 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 324 137 19 240 240 240 496), lower := (rows 7 42 324 137 19 32 64 128 256), losses := [] }

theorem u31215 : Upper (D 7) (R 7) [6,40,320,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31216 : Route 9 := (fun mask => (mask,id))

def c31216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31216 : Upper (D 7) (R 7) [6,40,320,129,33] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,33] 13 (by decide) (choices 1) [2,16,64,128] r31216 c31216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13621
  · exact u13622
  · exact u13623
  · exact u13624

def b31217 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 324 137 50 241 209 209 465), lower := (rows 7 42 324 137 50 32 64 128 256), losses := [] }

theorem u31217 : Upper (D 7) (R 7) [6,40,320,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31218 : Route 9 := (fun mask => (mask,id))

def c31218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31218 : Upper (D 7) (R 7) [6,40,320,129,65] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,65] 13 (by decide) (choices 1) [2,16,128] r31218 c31218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13625
  · exact u13626
  · exact u13627

def r31219 : Route 9 := (fun mask => (mask,id))

def c31219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31219 : Upper (D 7) (R 7) [6,40,320,129,66] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,66] 13 (by decide) (choices 1) [1,16,128] r31219 c31219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13628
  · exact u13629
  · exact u13630

def r31220 : Route 9 := (fun mask => (mask,id))

def c31220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31220 : Upper (D 7) (R 7) [6,40,320,129,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,96] 13 (by decide) (choices 1) [1,2,16,128] r31220 c31220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13631
  · exact u13632
  · exact u13633
  · exact u13634

def b31221 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 42 324 137 145 114 114 242 370), lower := (rows 7 42 324 137 145 32 64 128 256), losses := [] }

theorem u31221 : Upper (D 7) (R 7) [6,40,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31222 : Route 9 := (fun mask => (mask,id))

def c31222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31222 : Upper (D 7) (R 7) [6,40,320,129,130] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,130] 13 (by decide) (choices 1) [1,16,64] r31222 c31222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13635
  · exact u13636
  · exact u13637

def r31223 : Route 9 := (fun mask => (mask,id))

def c31223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31223 : Upper (D 7) (R 7) [6,40,320,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,160] 13 (by decide) (choices 1) [1,2,16,64] r31223 c31223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13638
  · exact u13639
  · exact u13640
  · exact u13641

def r31224 : Route 9 := (fun mask => (mask,id))

def c31224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31224 : Upper (D 7) (R 7) [6,40,320,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,192] 13 (by decide) (choices 1) [1,2,16] r31224 c31224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13642
  · exact u13643
  · exact u13644

def r31225 : Route 9 := (fun mask => (mask,id))

def c31225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31225 : Upper (D 7) (R 7) [6,40,320,130,33] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,33] 13 (by decide) (choices 1) [1,16,64,128] r31225 c31225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13645
  · exact u13646
  · exact u13647
  · exact u13648

def b31226 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 324 138 81 177 241 177 433), lower := (rows 7 42 324 138 81 32 64 128 256), losses := [] }

theorem u31226 : Upper (D 7) (R 7) [6,40,320,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31227 : Route 9 := (fun mask => (mask,id))

def c31227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31227 : Upper (D 7) (R 7) [6,40,320,130,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,96] 13 (by decide) (choices 1) [1,16,128] r31227 c31227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13649
  · exact u13650
  · exact u13651

def r31228 : Route 9 := (fun mask => (mask,id))

def c31228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31228 : Upper (D 7) (R 7) [6,40,320,130,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,129] 13 (by decide) (choices 1) [1,16,64] r31228 c31228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13652
  · exact u13653
  · exact u13654

def b31229 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 138 176 113 81 209 337), lower := (rows 7 42 324 138 176 32 64 128 256), losses := [] }

theorem u31229 : Upper (D 7) (R 7) [6,40,320,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31230 : Route 9 := (fun mask => (mask,id))

def c31230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31230 : Upper (D 7) (R 7) [6,40,320,130,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,192] 13 (by decide) (choices 1) [1,16] r31230 c31230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13655
  · exact u13656

def b31231 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 324 152 19 225 225 225 481), lower := (rows 7 42 324 152 19 32 64 128 256), losses := [] }

theorem u31231 : Upper (D 7) (R 7) [6,40,320,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31232 : Route 9 := (fun mask => (mask,id))

def c31232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31232 : Upper (D 7) (R 7) [6,40,320,144,33] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,33] 13 (by decide) (choices 1) [1,2,64,128] r31232 c31232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13657
  · exact u13658
  · exact u13659
  · exact u13660

def b31233 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 324 152 50 225 193 193 449), lower := (rows 7 42 324 152 50 32 64 128 256), losses := [] }

theorem u31233 : Upper (D 7) (R 7) [6,40,320,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31234 : Route 9 := (fun mask => (mask,id))

def c31234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31234 : Upper (D 7) (R 7) [6,40,320,144,65] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,65] 13 (by decide) (choices 1) [1,2,128] r31234 c31234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13661
  · exact u13662
  · exact u13663

def r31235 : Route 9 := (fun mask => (mask,id))

def c31235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31235 : Upper (D 7) (R 7) [6,40,320,144,66] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,66] 13 (by decide) (choices 1) [1,128] r31235 c31235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13664
  · exact u13665

def r31236 : Route 9 := (fun mask => (mask,id))

def c31236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31236 : Upper (D 7) (R 7) [6,40,320,144,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,96] 13 (by decide) (choices 1) [1,2,128] r31236 c31236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13666
  · exact u13667
  · exact u13668

def b31237 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 324 152 145 99 99 227 355), lower := (rows 7 42 324 152 145 32 64 128 256), losses := [] }

theorem u31237 : Upper (D 7) (R 7) [6,40,320,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31238 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 324 152 146 97 97 225 353), lower := (rows 7 42 324 152 146 32 64 128 256), losses := [] }

theorem u31238 : Upper (D 7) (R 7) [6,40,320,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31239 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 152 176 99 67 195 323), lower := (rows 7 42 324 152 176 32 64 128 256), losses := [] }

theorem u31239 : Upper (D 7) (R 7) [6,40,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31240 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 324 152 208 35 99 163 291), lower := (rows 7 42 324 152 208 32 64 128 256), losses := [] }

theorem u31240 : Upper (D 7) (R 7) [6,40,320,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31241 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 324 200 19 177 241 177 433), lower := (rows 7 42 324 200 19 32 64 128 256), losses := [] }

theorem u31241 : Upper (D 7) (R 7) [6,40,320,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31242 : Route 9 := (fun mask => (mask,id))

def c31242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31242 : Upper (D 7) (R 7) [6,40,320,192,33] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,33] 13 (by decide) (choices 1) [1,2,16,128] r31242 c31242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13669
  · exact u13670
  · exact u13671
  · exact u13672

def b31243 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 324 200 50 177 209 145 401), lower := (rows 7 42 324 200 50 32 64 128 256), losses := [] }

theorem u31243 : Upper (D 7) (R 7) [6,40,320,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31244 : Route 9 := (fun mask => (mask,id))

def c31244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31244 : Upper (D 7) (R 7) [6,40,320,192,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,129] 13 (by decide) (choices 1) [1,2,16] r31244 c31244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13673
  · exact u13674
  · exact u13675

def r31245 : Route 9 := (fun mask => (mask,id))

def c31245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31245 : Upper (D 7) (R 7) [6,40,320,192,130] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,130] 13 (by decide) (choices 1) [1,16] r31245 c31245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13676
  · exact u13677

def r31246 : Route 9 := (fun mask => (mask,id))

def c31246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31246 : Upper (D 7) (R 7) [6,40,320,192,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,160] 13 (by decide) (choices 1) [1,2,16] r31246 c31246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13678
  · exact u13679
  · exact u13680

def b31247 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 13 56 19 480 448 448 448), lower := (rows 7 98 13 56 19 32 64 128 256), losses := [] }

theorem u31247 : Upper (D 7) (R 7) [6,96,9,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31248 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 13 56 81 418 450 386 386), lower := (rows 7 98 13 56 81 32 64 128 256), losses := [] }

theorem u31248 : Upper (D 7) (R 7) [6,96,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31249 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 13 56 82 417 449 385 385), lower := (rows 7 98 13 56 82 32 64 128 256), losses := [] }

theorem u31249 : Upper (D 7) (R 7) [6,96,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31250 : Route 9 := (fun mask => (mask,id))

def c31250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u31250 : Upper (D 7) (R 7) [6,96,9,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,129] 13 (by decide) (choices 1) [2,64,128,256] r31250 c31250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13681
  · exact u13682
  · exact u13683
  · exact u13684

def r31251 : Route 9 := (fun mask => (mask,id))

def c31251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u31251 : Upper (D 7) (R 7) [6,96,9,48,130] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,130] 13 (by decide) (choices 1) [1,64,128,256] r31251 c31251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13685
  · exact u13686
  · exact u13687
  · exact u13688

def r31252 : Route 9 := (fun mask => (mask,id))

def c31252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31252 : Upper (D 7) (R 7) [6,96,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,192] 13 (by decide) (choices 1) [1,2,128,256] r31252 c31252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13689
  · exact u13690
  · exact u13691
  · exact u13692

def r31253 : Route 9 := (fun mask => (mask,id))

def c31253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31253 : Upper (D 7) (R 7) [6,96,9,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,257] 13 (by decide) (choices 1) [2,64,128] r31253 c31253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13693
  · exact u13694
  · exact u13695

def r31254 : Route 9 := (fun mask => (mask,id))

def c31254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31254 : Upper (D 7) (R 7) [6,96,9,48,258] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,258] 13 (by decide) (choices 1) [1,64,128] r31254 c31254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13696
  · exact u13697
  · exact u13698

def r31255 : Route 9 := (fun mask => (mask,id))

def c31255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31255 : Upper (D 7) (R 7) [6,96,9,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,320] 13 (by decide) (choices 1) [1,2,128] r31255 c31255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13699
  · exact u13700
  · exact u13701

def r31256 : Route 9 := (fun mask => (mask,id))

def c31256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31256 : Upper (D 7) (R 7) [6,96,9,48,384] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,384] 13 (by decide) (choices 1) [1,2,64,128] r31256 c31256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13702
  · exact u13703
  · exact u13704
  · exact u13705

def b31257 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 98 13 152 19 480 480 480 480), lower := (rows 7 98 13 152 19 32 64 128 256), losses := [] }

theorem u31257 : Upper (D 7) (R 7) [6,96,9,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31258 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 7 98 13 152 49 482 450 450 450), lower := (rows 7 98 13 152 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 455 450 461 156 477 0 64 128 256) }] }

theorem u31258 : Upper (D 7) (R 7) [6,96,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31259 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 13 152 50 481 449 449 449), lower := (rows 7 98 13 152 50 32 64 128 256), losses := [] }

theorem u31259 : Upper (D 7) (R 7) [6,96,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31259
end Delivery.IrregularNine14.P07
