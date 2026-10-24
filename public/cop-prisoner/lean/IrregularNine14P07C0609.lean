import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0369
import IrregularNine14P07C0370
import IrregularNine14P07C0371

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36540 : Route 9 := (fun mask => (mask,id))

def c36540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36540 : Upper (D 7) (R 7) [36,40,18,257,65] 13 := by
  apply FastRouting.sound _ _ [36,40,18,257,65] 13 (by decide) (choices 1) [2,64,128] r36540 c36540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22169
  · exact u22170
  · exact u22171

def b36541 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 42 22 265 82 225 193 193 449), lower := (rows 37 42 22 265 82 32 64 128 256), losses := [] }

theorem u36541 : Upper (D 7) (R 7) [36,40,18,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36542 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36542 : Upper (D 7) (R 7) [36,40,18,257,192] 13 := by
  apply FastRouting.sound _ _ [36,40,18,257,192] 13 (by decide) (choices 1) [1,2,64] r36542 c36542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22172
  · exact u22173
  · exact u22174

def b36543 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 266 81 225 193 193 449), lower := (rows 37 42 22 266 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 17 0 81 145 273), good := (rows 477 10 478 266 465 0 64 128 256) }] }

theorem u36543 : Upper (D 7) (R 7) [36,40,18,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36544 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36544 : Upper (D 7) (R 7) [36,40,18,258,192] 13 := by
  apply FastRouting.sound _ _ [36,40,18,258,192] 13 (by decide) (choices 1) [1,64] r36544 c36544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22175
  · exact u22176

def b36545 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 22 328 19 225 193 193 449), lower := (rows 37 42 22 328 19 32 64 128 256), losses := [] }

theorem u36545 : Upper (D 7) (R 7) [36,40,18,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36546 : Route 9 := (fun mask => (mask,id))

def c36546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36546 : Upper (D 7) (R 7) [36,40,18,320,65] 13 := by
  apply FastRouting.sound _ _ [36,40,18,320,65] 13 (by decide) (choices 1) [1,2,128] r36546 c36546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22177
  · exact u22178
  · exact u22179

def b36547 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 42 22 328 82 161 193 129 385), lower := (rows 37 42 22 328 82 32 64 128 256), losses := [] }

theorem u36547 : Upper (D 7) (R 7) [36,40,18,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36548 : Route 9 := (fun mask => (mask,id))

def c36548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36548 : Upper (D 7) (R 7) [36,40,18,320,129] 13 := by
  apply FastRouting.sound _ _ [36,40,18,320,129] 13 (by decide) (choices 1) [1,2,64,128] r36548 c36548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22180
  · exact u22181
  · exact u22182
  · exact u22183

def b36549 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 42 22 328 146 225 193 193 449), lower := (rows 37 42 22 328 146 32 64 128 256), losses := [] }

theorem u36549 : Upper (D 7) (R 7) [36,40,18,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36550 : Route 9 := (fun mask => (mask,id))

def c36550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36550 : Upper (D 7) (R 7) [36,40,18,320,192] 13 := by
  apply FastRouting.sound _ _ [36,40,18,320,192] 13 (by decide) (choices 1) [1,2,128] r36550 c36550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22184
  · exact u22185
  · exact u22186

def b36551 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 69 88 19 418 450 386 386), lower := (rows 37 42 69 88 19 32 64 128 256), losses := [] }

theorem u36551 : Upper (D 7) (R 7) [36,40,65,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36552 : Route 9 := (fun mask => (mask,id))

def c36552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36552 : Upper (D 7) (R 7) [36,40,65,80,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,129] 13 (by decide) (choices 1) [2,128,256] r36552 c36552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22187
  · exact u22188
  · exact u22189

def r36553 : Route 9 := (fun mask => (mask,id))

def c36553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36553 : Upper (D 7) (R 7) [36,40,65,80,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,130] 13 (by decide) (choices 1) [1,2,128,256] r36553 c36553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22190
  · exact u22191
  · exact u22192
  · exact u22193

def r36554 : Route 9 := (fun mask => (mask,id))

def c36554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36554 : Upper (D 7) (R 7) [36,40,65,80,257] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,257] 13 (by decide) (choices 1) [2,128] r36554 c36554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22194
  · exact u22195

def r36555 : Route 9 := (fun mask => (mask,id))

def c36555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36555 : Upper (D 7) (R 7) [36,40,65,80,258] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,258] 13 (by decide) (choices 1) [1,2,128] r36555 c36555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22196
  · exact u22197
  · exact u22198

def r36556 : Route 9 := (fun mask => (mask,id))

def c36556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36556 : Upper (D 7) (R 7) [36,40,65,80,384] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,384] 13 (by decide) (choices 1) [1,2,128] r36556 c36556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22199
  · exact u22200
  · exact u22201

def r36557 : Route 9 := (fun mask => (mask,id))

def c36557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36557 : Upper (D 7) (R 7) [36,40,65,129,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,129,66] 13 (by decide) (choices 1) [2,16,128,256] r36557 c36557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22202
  · exact u22203
  · exact u22204
  · exact u22205

def b36558 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 42 69 137 146 370 338 466 338), lower := (rows 37 42 69 137 146 32 64 128 256), losses := [] }

theorem u36558 : Upper (D 7) (R 7) [36,40,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36559 : Route 9 := (fun mask => (mask,id))

def c36559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36559 : Upper (D 7) (R 7) [36,40,65,129,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,129,192] 13 (by decide) (choices 1) [2,16,256] r36559 c36559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22206
  · exact u22207
  · exact u22208

def r36560 : Route 9 := (fun mask => (mask,id))

def c36560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36560 : Upper (D 7) (R 7) [36,40,65,129,258] 13 := by
  apply FastRouting.sound _ _ [36,40,65,129,258] 13 (by decide) (choices 1) [2,16,64,128] r36560 c36560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22209
  · exact u22210
  · exact u22211
  · exact u22212

def r36561 : Route 9 := (fun mask => (mask,id))

def c36561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36561 : Upper (D 7) (R 7) [36,40,65,129,320] 13 := by
  apply FastRouting.sound _ _ [36,40,65,129,320] 13 (by decide) (choices 1) [2,16,128] r36561 c36561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22213
  · exact u22214
  · exact u22215

def r36562 : Route 9 := (fun mask => (mask,id))

def c36562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36562 : Upper (D 7) (R 7) [36,40,65,129,384] 13 := by
  apply FastRouting.sound _ _ [36,40,65,129,384] 13 (by decide) (choices 1) [2,16,64] r36562 c36562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22216
  · exact u22217
  · exact u22218

def b36563 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 42 69 138 19 496 464 464 464), lower := (rows 37 42 69 138 19 32 64 128 256), losses := [] }

theorem u36563 : Upper (D 7) (R 7) [36,40,65,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36564 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 42 69 138 81 434 466 402 402), lower := (rows 37 42 69 138 81 32 64 128 256), losses := [] }

theorem u36564 : Upper (D 7) (R 7) [36,40,65,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36565 : Route 9 := (fun mask => (mask,id))

def c36565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36565 : Upper (D 7) (R 7) [36,40,65,130,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130,66] 13 (by decide) (choices 1) [1,16,128,256] r36565 c36565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22219
  · exact u22220
  · exact u22221
  · exact u22222

theorem m36566_2 : Upper (D 7) (R 7) [36,40,65,130,192,2] 13 :=
  permutation_upper _ _ _ [36,40,65,130,192,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22223

def r36566 : Route 9 := (fun mask => (mask,id))

def c36566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36566 : Upper (D 7) (R 7) [36,40,65,130,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130,192] 13 (by decide) (choices 1) [1,2,16,256] r36566 c36566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22223
  · exact m36566_2
  · exact u22224
  · exact u22225

def r36567 : Route 9 := (fun mask => (mask,id))

def c36567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36567 : Upper (D 7) (R 7) [36,40,65,130,257] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130,257] 13 (by decide) (choices 1) [2,16,64,128] r36567 c36567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22226
  · exact u22227
  · exact u22228
  · exact u22229

def r36568 : Route 9 := (fun mask => (mask,id))

def c36568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36568 : Upper (D 7) (R 7) [36,40,65,130,320] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130,320] 13 (by decide) (choices 1) [1,2,16,128] r36568 c36568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22230
  · exact u22231
  · exact u22232
  · exact u22233

def b36569 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 69 152 19 482 450 450 450), lower := (rows 37 42 69 152 19 32 64 128 256), losses := [] }

theorem u36569 : Upper (D 7) (R 7) [36,40,65,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36570 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 42 69 152 81 418 450 386 386), lower := (rows 37 42 69 152 81 32 64 128 256), losses := [] }

theorem u36570 : Upper (D 7) (R 7) [36,40,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36571 : Route 9 := (fun mask => (mask,id))

def c36571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36571 : Upper (D 7) (R 7) [36,40,65,144,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144,66] 13 (by decide) (choices 1) [1,2,128,256] r36571 c36571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22234
  · exact u22235
  · exact u22236
  · exact u22237

def b36572 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 37 42 69 152 145 354 322 450 322), lower := (rows 37 42 69 152 145 32 64 128 256), losses := [] }

theorem u36572 : Upper (D 7) (R 7) [36,40,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36573 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 69 152 146 355 323 451 323), lower := (rows 37 42 69 152 146 32 64 128 256), losses := [] }

theorem u36573 : Upper (D 7) (R 7) [36,40,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36574 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 69 152 208 291 323 387 259), lower := (rows 37 42 69 152 208 32 64 128 256), losses := [] }

theorem u36574 : Upper (D 7) (R 7) [36,40,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36575 : Route 9 := (fun mask => (mask,id))

def c36575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36575 : Upper (D 7) (R 7) [36,40,65,144,257] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144,257] 13 (by decide) (choices 1) [2,64,128] r36575 c36575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22238
  · exact u22239
  · exact u22240

def r36576 : Route 9 := (fun mask => (mask,id))

def c36576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36576 : Upper (D 7) (R 7) [36,40,65,144,258] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144,258] 13 (by decide) (choices 1) [1,2,64,128] r36576 c36576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22241
  · exact u22242
  · exact u22243
  · exact u22244

def r36577 : Route 9 := (fun mask => (mask,id))

def c36577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36577 : Upper (D 7) (R 7) [36,40,65,144,320] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144,320] 13 (by decide) (choices 1) [1,2,128] r36577 c36577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22245
  · exact u22246
  · exact u22247

def b36578 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 69 152 400 99 67 195 323), lower := (rows 37 42 69 152 400 32 64 128 256), losses := [] }

theorem u36578 : Upper (D 7) (R 7) [36,40,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36579 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 69 200 19 434 466 402 402), lower := (rows 37 42 69 200 19 32 64 128 256), losses := [] }

theorem u36579 : Upper (D 7) (R 7) [36,40,65,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36580 : Route 9 := (fun mask => (mask,id))

def c36580 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36580 : Upper (D 7) (R 7) [36,40,65,192,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,129] 13 (by decide) (choices 1) [2,16,256] r36580 c36580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22248
  · exact u22249
  · exact u22250

def r36581 : Route 9 := (fun mask => (mask,id))

def c36581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36581 : Upper (D 7) (R 7) [36,40,65,192,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,130] 13 (by decide) (choices 1) [1,2,16,256] r36581 c36581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22251
  · exact u22252
  · exact u22253
  · exact u22254

def r36582 : Route 9 := (fun mask => (mask,id))

def c36582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36582 : Upper (D 7) (R 7) [36,40,65,192,257] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,257] 13 (by decide) (choices 1) [2,16,128] r36582 c36582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22255
  · exact u22256
  · exact u22257

def r36583 : Route 9 := (fun mask => (mask,id))

def c36583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36583 : Upper (D 7) (R 7) [36,40,65,192,258] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,258] 13 (by decide) (choices 1) [1,2,16,128] r36583 c36583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22258
  · exact u22259
  · exact u22260
  · exact u22261

def r36584 : Route 9 := (fun mask => (mask,id))

def c36584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36584 : Upper (D 7) (R 7) [36,40,65,192,384] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,384] 13 (by decide) (choices 1) [1,2,16] r36584 c36584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22262
  · exact u22263
  · exact u22264

def r36585 : Route 9 := (fun mask => (mask,id))

def c36585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36585 : Upper (D 7) (R 7) [36,40,65,257,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,257,66] 13 (by decide) (choices 1) [2,16,128] r36585 c36585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22265
  · exact u22266
  · exact u22267

def r36586 : Route 9 := (fun mask => (mask,id))

def c36586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36586 : Upper (D 7) (R 7) [36,40,65,257,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,257,130] 13 (by decide) (choices 1) [2,16,64,128] r36586 c36586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22268
  · exact u22269
  · exact u22270
  · exact u22271

def r36587 : Route 9 := (fun mask => (mask,id))

def c36587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36587 : Upper (D 7) (R 7) [36,40,65,257,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,257,192] 13 (by decide) (choices 1) [2,16,128] r36587 c36587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22272
  · exact u22273
  · exact u22274

def b36588 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 42 69 266 19 240 208 208 464), lower := (rows 37 42 69 266 19 32 64 128 256), losses := [] }

theorem u36588 : Upper (D 7) (R 7) [36,40,65,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36589 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 42 69 266 81 178 210 146 402), lower := (rows 37 42 69 266 81 32 64 128 256), losses := [] }

theorem u36589 : Upper (D 7) (R 7) [36,40,65,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36590 : Route 9 := (fun mask => (mask,id))

def c36590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36590 : Upper (D 7) (R 7) [36,40,65,258,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,66] 13 (by decide) (choices 1) [1,16,128] r36590 c36590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22275
  · exact u22276
  · exact u22277

def r36591 : Route 9 := (fun mask => (mask,id))

def c36591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36591 : Upper (D 7) (R 7) [36,40,65,258,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,129] 13 (by decide) (choices 1) [2,16,64,128] r36591 c36591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22278
  · exact u22279
  · exact u22280
  · exact u22281

def r36592 : Route 9 := (fun mask => (mask,id))

def c36592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36592 : Upper (D 7) (R 7) [36,40,65,258,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,130] 13 (by decide) (choices 1) [1,16,64,128] r36592 c36592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22282
  · exact u22283
  · exact u22284
  · exact u22285

def r36593 : Route 9 := (fun mask => (mask,id))

def c36593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36593 : Upper (D 7) (R 7) [36,40,65,258,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,192] 13 (by decide) (choices 1) [1,2,16,128] r36593 c36593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22286
  · exact u22287
  · exact u22288
  · exact u22289

def b36594 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 69 280 19 226 194 194 450), lower := (rows 37 42 69 280 19 32 64 128 256), losses := [] }

theorem u36594 : Upper (D 7) (R 7) [36,40,65,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36595 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 42 69 280 81 162 194 130 386), lower := (rows 37 42 69 280 81 32 64 128 256), losses := [] }

theorem u36595 : Upper (D 7) (R 7) [36,40,65,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36596 : Route 9 := (fun mask => (mask,id))

def c36596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36596 : Upper (D 7) (R 7) [36,40,65,272,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272,66] 13 (by decide) (choices 1) [1,2,128] r36596 c36596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22290
  · exact u22291
  · exact u22292

def r36597 : Route 9 := (fun mask => (mask,id))

def c36597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36597 : Upper (D 7) (R 7) [36,40,65,272,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272,129] 13 (by decide) (choices 1) [2,64,128] r36597 c36597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22293
  · exact u22294
  · exact u22295

def r36598 : Route 9 := (fun mask => (mask,id))

def c36598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36598 : Upper (D 7) (R 7) [36,40,65,272,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272,130] 13 (by decide) (choices 1) [1,2,64,128] r36598 c36598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22296
  · exact u22297
  · exact u22298
  · exact u22299

def r36599 : Route 9 := (fun mask => (mask,id))

def c36599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36599 : Upper (D 7) (R 7) [36,40,65,272,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272,192] 13 (by decide) (choices 1) [1,2,128] r36599 c36599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22300
  · exact u22301
  · exact u22302

#print axioms u36599
end Delivery.IrregularNine14.P07
