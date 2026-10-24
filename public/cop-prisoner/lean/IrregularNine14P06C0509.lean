import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0202
import IrregularNine14P06C0203

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30540 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 70 140 21 368 368 496 368), lower := (rows 11 35 70 140 21 32 64 128 256), losses := [] }

theorem u30540 : Upper (D 6) (R 6) [10,33,66,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30541 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 70 140 49 372 340 468 340), lower := (rows 11 35 70 140 49 32 64 128 256), losses := [] }

theorem u30541 : Upper (D 6) (R 6) [10,33,66,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30542 : Route 9 := (fun mask => (mask,id))

def c30542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30542 : Upper (D 6) (R 6) [10,33,66,132,36] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,36] 13 (by decide) (choices 1) [1,16,64,256] r30542 c30542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12148
  · exact u12149
  · exact u12150
  · exact u12151

def r30543 : Route 9 := (fun mask => (mask,id))

def c30543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30543 : Upper (D 6) (R 6) [10,33,66,132,65] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,65] 13 (by decide) (choices 1) [4,16,256] r30543 c30543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12152
  · exact u12153
  · exact u12154

def b30544 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 70 140 84 305 369 433 305), lower := (rows 11 35 70 140 84 32 64 128 256), losses := [] }

theorem u30544 : Upper (D 6) (R 6) [10,33,66,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30545 : Route 9 := (fun mask => (mask,id))

def c30545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30545 : Upper (D 6) (R 6) [10,33,66,132,96] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,96] 13 (by decide) (choices 1) [1,4,16,256] r30545 c30545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12155
  · exact u12156
  · exact u12157
  · exact u12158

def r30546 : Route 9 := (fun mask => (mask,id))

def c30546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30546 : Upper (D 6) (R 6) [10,33,66,132,257] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,257] 13 (by decide) (choices 1) [4,16,64] r30546 c30546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12159
  · exact u12160
  · exact u12161

def r30547 : Route 9 := (fun mask => (mask,id))

def c30547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30547 : Upper (D 6) (R 6) [10,33,66,132,260] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,260] 13 (by decide) (choices 1) [1,16,64] r30547 c30547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12162
  · exact u12163
  · exact u12164

def r30548 : Route 9 := (fun mask => (mask,id))

def c30548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30548 : Upper (D 6) (R 6) [10,33,66,132,288] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,288] 13 (by decide) (choices 1) [1,4,16,64] r30548 c30548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12165
  · exact u12166
  · exact u12167
  · exact u12168

def r30549 : Route 9 := (fun mask => (mask,id))

def c30549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30549 : Upper (D 6) (R 6) [10,33,66,132,320] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,320] 13 (by decide) (choices 1) [1,4,16] r30549 c30549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12169
  · exact u12170
  · exact u12171

def b30550 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 70 152 21 356 356 484 356), lower := (rows 11 35 70 152 21 32 64 128 256), losses := [] }

theorem u30550 : Upper (D 6) (R 6) [10,33,66,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30551 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 70 152 49 356 324 452 324), lower := (rows 11 35 70 152 49 32 64 128 256), losses := [] }

theorem u30551 : Upper (D 6) (R 6) [10,33,66,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30552 : Route 9 := (fun mask => (mask,id))

def c30552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30552 : Upper (D 6) (R 6) [10,33,66,144,36] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,36] 13 (by decide) (choices 1) [1,4,64,256] r30552 c30552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12172
  · exact u12173
  · exact u12174
  · exact u12175

def r30553 : Route 9 := (fun mask => (mask,id))

def c30553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30553 : Upper (D 6) (R 6) [10,33,66,144,65] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,65] 13 (by decide) (choices 1) [4,256] r30553 c30553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12176
  · exact u12177

def b30554 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 70 152 84 293 357 421 293), lower := (rows 11 35 70 152 84 32 64 128 256), losses := [] }

theorem u30554 : Upper (D 6) (R 6) [10,33,66,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30555 : Route 9 := (fun mask => (mask,id))

def c30555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30555 : Upper (D 6) (R 6) [10,33,66,144,96] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,96] 13 (by decide) (choices 1) [1,4,256] r30555 c30555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12178
  · exact u12179
  · exact u12180

def r30556 : Route 9 := (fun mask => (mask,id))

def c30556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30556 : Upper (D 6) (R 6) [10,33,66,144,257] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,257] 13 (by decide) (choices 1) [4,64] r30556 c30556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12181
  · exact u12182

def r30557 : Route 9 := (fun mask => (mask,id))

def c30557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30557 : Upper (D 6) (R 6) [10,33,66,144,260] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,260] 13 (by decide) (choices 1) [1,4,64] r30557 c30557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12183
  · exact u12184
  · exact u12185

def r30558 : Route 9 := (fun mask => (mask,id))

def c30558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30558 : Upper (D 6) (R 6) [10,33,66,144,288] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,288] 13 (by decide) (choices 1) [1,4,64] r30558 c30558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12186
  · exact u12187
  · exact u12188

def r30559 : Route 9 := (fun mask => (mask,id))

def c30559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30559 : Upper (D 6) (R 6) [10,33,66,144,320] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,320] 13 (by decide) (choices 1) [1,4] r30559 c30559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12189
  · exact u12190

def b30560 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 70 200 21 308 372 436 308), lower := (rows 11 35 70 200 21 32 64 128 256), losses := [] }

theorem u30560 : Upper (D 6) (R 6) [10,33,66,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30561 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 70 200 49 308 340 404 276), lower := (rows 11 35 70 200 49 32 64 128 256), losses := [] }

theorem u30561 : Upper (D 6) (R 6) [10,33,66,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30562 : Route 9 := (fun mask => (mask,id))

def c30562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30562 : Upper (D 6) (R 6) [10,33,66,192,36] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,36] 13 (by decide) (choices 1) [1,4,16,256] r30562 c30562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12191
  · exact u12192
  · exact u12193
  · exact u12194

def r30563 : Route 9 := (fun mask => (mask,id))

def c30563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30563 : Upper (D 6) (R 6) [10,33,66,192,257] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,257] 13 (by decide) (choices 1) [4,16] r30563 c30563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12195
  · exact u12196

def r30564 : Route 9 := (fun mask => (mask,id))

def c30564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30564 : Upper (D 6) (R 6) [10,33,66,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,260] 13 (by decide) (choices 1) [1,4,16] r30564 c30564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12197
  · exact u12198
  · exact u12199

def r30565 : Route 9 := (fun mask => (mask,id))

def c30565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30565 : Upper (D 6) (R 6) [10,33,66,192,288] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,288] 13 (by decide) (choices 1) [1,4,16] r30565 c30565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12200
  · exact u12201
  · exact u12202

def r30566 : Route 9 := (fun mask => (mask,id))

def c30566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30566 : Upper (D 6) (R 6) [10,33,66,384,5] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384,5] 13 (by decide) (choices 1) [4,16,64] r30566 c30566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12203
  · exact u12204
  · exact u12205

def b30567 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 70 392 49 116 84 212 340), lower := (rows 11 35 70 392 49 32 64 128 256), losses := [] }

theorem u30567 : Upper (D 6) (R 6) [10,33,66,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30568 : Route 9 := (fun mask => (mask,id))

def c30568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30568 : Upper (D 6) (R 6) [10,33,66,384,36] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384,36] 13 (by decide) (choices 1) [1,4,16,64] r30568 c30568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12206
  · exact u12207
  · exact u12208
  · exact u12209

def r30569 : Route 9 := (fun mask => (mask,id))

def c30569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30569 : Upper (D 6) (R 6) [10,33,66,384,65] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384,65] 13 (by decide) (choices 1) [4,16] r30569 c30569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12210
  · exact u12211

def b30570 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 70 392 84 53 117 181 309), lower := (rows 11 35 70 392 84 32 64 128 256), losses := [] }

theorem u30570 : Upper (D 6) (R 6) [10,33,66,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30571 : Route 9 := (fun mask => (mask,id))

def c30571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30571 : Upper (D 6) (R 6) [10,33,66,384,96] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384,96] 13 (by decide) (choices 1) [1,4,16] r30571 c30571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12212
  · exact u12213
  · exact u12214

def b30572 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 84 13 22 480 480 480 480), lower := (rows 11 35 84 13 22 32 64 128 256), losses := [] }

theorem u30572 : Upper (D 6) (R 6) [10,33,80,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30573 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 84 13 50 484 452 452 452), lower := (rows 11 35 84 13 50 32 64 128 256), losses := [] }

theorem u30573 : Upper (D 6) (R 6) [10,33,80,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30574 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 13 52 482 450 450 450), lower := (rows 11 35 84 13 52 32 64 128 256), losses := [] }

theorem u30574 : Upper (D 6) (R 6) [10,33,80,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30575 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 13 82 420 484 420 420), lower := (rows 11 35 84 13 82 32 64 128 256), losses := [] }

theorem u30575 : Upper (D 6) (R 6) [10,33,80,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30576 : PairBound 9 := { available := 418, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 84 13 84 418 482 418 418), lower := (rows 11 35 84 13 84 32 64 128 256), losses := [] }

theorem u30576 : Upper (D 6) (R 6) [10,33,80,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30577 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 13 112 422 454 390 390), lower := (rows 11 35 84 13 112 32 64 128 256), losses := [] }

theorem u30577 : Upper (D 6) (R 6) [10,33,80,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30578 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 13 146 356 356 484 356), lower := (rows 11 35 84 13 146 32 64 128 256), losses := [] }

theorem u30578 : Upper (D 6) (R 6) [10,33,80,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30579 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 84 13 148 354 354 482 354), lower := (rows 11 35 84 13 148 32 64 128 256), losses := [] }

theorem u30579 : Upper (D 6) (R 6) [10,33,80,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30580 : Route 9 := (fun mask => (mask,id))

def c30580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30580 : Upper (D 6) (R 6) [10,33,80,5,160] 13 := by
  apply FastRouting.sound _ _ [10,33,80,5,160] 13 (by decide) (choices 1) [2,4,64,256] r30580 c30580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12215
  · exact u12216
  · exact u12217
  · exact u12218

def b30581 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 13 208 294 358 422 294), lower := (rows 11 35 84 13 208 32 64 128 256), losses := [] }

theorem u30581 : Upper (D 6) (R 6) [10,33,80,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30582 : Route 9 := (fun mask => (mask,id))

def c30582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30582 : Upper (D 6) (R 6) [10,33,80,5,384] 13 := by
  apply FastRouting.sound _ _ [10,33,80,5,384] 13 (by decide) (choices 1) [2,4,64] r30582 c30582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12219
  · exact u12220
  · exact u12221

def b30583 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 73 22 420 484 420 420), lower := (rows 11 35 84 73 22 32 64 128 256), losses := [] }

theorem u30583 : Upper (D 6) (R 6) [10,33,80,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30584 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 84 73 50 420 452 388 388), lower := (rows 11 35 84 73 50 32 64 128 256), losses := [] }

theorem u30584 : Upper (D 6) (R 6) [10,33,80,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30585 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 84 73 52 422 454 390 390), lower := (rows 11 35 84 73 52 32 64 128 256), losses := [{ target := 2, region := (rows 21 18 0 12 16 32 64 128 256), good := (rows 11 35 91 73 59 32 64 128 256) }] }

theorem u30585 : Upper (D 6) (R 6) [10,33,80,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30586 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 73 146 292 356 420 292), lower := (rows 11 35 84 73 146 32 64 128 256), losses := [] }

theorem u30586 : Upper (D 6) (R 6) [10,33,80,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30587 : Route 9 := (fun mask => (mask,id))

def c30587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30587 : Upper (D 6) (R 6) [10,33,80,65,132] 13 := by
  apply FastRouting.sound _ _ [10,33,80,65,132] 13 (by decide) (choices 1) [2,4,256] r30587 c30587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12222
  · exact u12223
  · exact u12224

def r30588 : Route 9 := (fun mask => (mask,id))

def c30588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30588 : Upper (D 6) (R 6) [10,33,80,65,160] 13 := by
  apply FastRouting.sound _ _ [10,33,80,65,160] 13 (by decide) (choices 1) [2,4,256] r30588 c30588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12225
  · exact u12226
  · exact u12227

def r30589 : Route 9 := (fun mask => (mask,id))

def c30589 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30589 : Upper (D 6) (R 6) [10,33,80,65,384] 13 := by
  apply FastRouting.sound _ _ [10,33,80,65,384] 13 (by decide) (choices 1) [2,4] r30589 c30589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12228
  · exact u12229

def b30590 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 22 356 356 484 356), lower := (rows 11 35 84 137 22 32 64 128 256), losses := [] }

theorem u30590 : Upper (D 6) (R 6) [10,33,80,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30591 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 84 137 50 356 324 452 324), lower := (rows 11 35 84 137 50 32 64 128 256), losses := [] }

theorem u30591 : Upper (D 6) (R 6) [10,33,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30592 : Route 9 := (fun mask => (mask,id))

def c30592 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30592 : Upper (D 6) (R 6) [10,33,80,129,36] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129,36] 13 (by decide) (choices 1) [2,4,64,256] r30592 c30592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12230
  · exact u12231
  · exact u12232
  · exact u12233

def b30593 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 137 82 292 356 420 292), lower := (rows 11 35 84 137 82 32 64 128 256), losses := [] }

theorem u30593 : Upper (D 6) (R 6) [10,33,80,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30594 : PairBound 9 := { available := 294, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 84 137 84 294 358 422 294), lower := (rows 11 35 84 137 84 32 64 128 256), losses := [] }

theorem u30594 : Upper (D 6) (R 6) [10,33,80,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30595 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 137 112 294 326 390 262), lower := (rows 11 35 84 137 112 32 64 128 256), losses := [] }

theorem u30595 : Upper (D 6) (R 6) [10,33,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30596 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 274 100 100 228 356), lower := (rows 11 35 84 137 274 32 64 128 256), losses := [] }

theorem u30596 : Upper (D 6) (R 6) [10,33,80,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30597 : Route 9 := (fun mask => (mask,id))

def c30597 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30597 : Upper (D 6) (R 6) [10,33,80,129,260] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129,260] 13 (by decide) (choices 1) [2,4,64] r30597 c30597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12234
  · exact u12235
  · exact u12236

def r30598 : Route 9 := (fun mask => (mask,id))

def c30598 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30598 : Upper (D 6) (R 6) [10,33,80,129,288] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129,288] 13 (by decide) (choices 1) [2,4,64] r30598 c30598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12237
  · exact u12238
  · exact u12239

def b30599 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 137 336 38 102 166 294), lower := (rows 11 35 84 137 336 32 64 128 256), losses := [] }

theorem u30599 : Upper (D 6) (R 6) [10,33,80,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30599
end Delivery.IrregularNine14.P06
