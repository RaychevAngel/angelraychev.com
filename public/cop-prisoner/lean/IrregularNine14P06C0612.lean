import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0354
import IrregularNine14P06C0355
import IrregularNine14P06C0356

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36720 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 21 355 323 451 323), lower := (rows 35 74 148 44 21 32 64 128 256), losses := [] }

theorem u36720 : Upper (D 6) (R 6) [34,72,144,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36721 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 22 353 321 449 321), lower := (rows 35 74 148 44 22 32 64 128 256), losses := [] }

theorem u36721 : Upper (D 6) (R 6) [34,72,144,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36722 : Route 9 := (fun mask => (mask,id))

def c36722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36722 : Upper (D 6) (R 6) [34,72,144,36,65] 13 := by
  apply FastRouting.sound _ _ [34,72,144,36,65] 13 (by decide) (choices 1) [1,2,4,256] r36722 c36722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21289
  · exact u21290
  · exact u21291
  · exact u21292

def b36723 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 148 44 82 293 325 389 261), lower := (rows 35 74 148 44 82 32 64 128 256), losses := [] }

theorem u36723 : Upper (D 6) (R 6) [34,72,144,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36724 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 84 291 323 387 259), lower := (rows 35 74 148 44 84 32 64 128 256), losses := [] }

theorem u36724 : Upper (D 6) (R 6) [34,72,144,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36725 : Route 9 := (fun mask => (mask,id))

def c36725 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36725 : Upper (D 6) (R 6) [34,72,144,36,257] 13 := by
  apply FastRouting.sound _ _ [34,72,144,36,257] 13 (by decide) (choices 1) [1,2,4,64] r36725 c36725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21293
  · exact u21294
  · exact u21295
  · exact u21296

def r36726 : Route 9 := (fun mask => (mask,id))

def c36726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36726 : Upper (D 6) (R 6) [34,72,144,36,258] 13 := by
  apply FastRouting.sound _ _ [34,72,144,36,258] 13 (by decide) (choices 1) [1,4,64] r36726 c36726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21297
  · exact u21298
  · exact u21299

def b36727 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 276 99 67 195 323), lower := (rows 35 74 148 44 276 32 64 128 256), losses := [] }

theorem u36727 : Upper (D 6) (R 6) [34,72,144,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36728 : Route 9 := (fun mask => (mask,id))

def c36728 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36728 : Upper (D 6) (R 6) [34,72,144,36,320] 13 := by
  apply FastRouting.sound _ _ [34,72,144,36,320] 13 (by decide) (choices 1) [1,2,4] r36728 c36728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21300
  · exact u21301
  · exact u21302

def b36729 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 148 265 19 100 100 228 356), lower := (rows 35 74 148 265 19 32 64 128 256), losses := [] }

theorem u36729 : Upper (D 6) (R 6) [34,72,144,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36730 : Route 9 := (fun mask => (mask,id))

def c36730 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36730 : Upper (D 6) (R 6) [34,72,144,257,5] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,5] 13 (by decide) (choices 1) [2,4,64] r36730 c36730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21303
  · exact u21304
  · exact u21305

def r36731 : Route 9 := (fun mask => (mask,id))

def c36731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36731 : Upper (D 6) (R 6) [34,72,144,257,6] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,6] 13 (by decide) (choices 1) [1,4,64] r36731 c36731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21306
  · exact u21307
  · exact u21308

def b36732 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 148 265 49 102 70 198 326), lower := (rows 35 74 148 265 49 32 64 128 256), losses := [] }

theorem u36732 : Upper (D 6) (R 6) [34,72,144,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36733 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 148 265 50 101 69 197 325), lower := (rows 35 74 148 265 50 32 64 128 256), losses := [] }

theorem u36733 : Upper (D 6) (R 6) [34,72,144,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36734 : Route 9 := (fun mask => (mask,id))

def c36734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36734 : Upper (D 6) (R 6) [34,72,144,257,36] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,36] 13 (by decide) (choices 1) [1,2,4,64] r36734 c36734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21309
  · exact u21310
  · exact u21311
  · exact u21312

def r36735 : Route 9 := (fun mask => (mask,id))

def c36735 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36735 : Upper (D 6) (R 6) [34,72,144,257,65] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,65] 13 (by decide) (choices 1) [2,4] r36735 c36735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21313
  · exact u21314

def b36736 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 148 265 82 37 101 165 293), lower := (rows 35 74 148 265 82 32 64 128 256), losses := [] }

theorem u36736 : Upper (D 6) (R 6) [34,72,144,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36737 : Route 9 := (fun mask => (mask,id))

def c36737 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36737 : Upper (D 6) (R 6) [34,72,144,257,68] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,68] 13 (by decide) (choices 1) [1,2,4] r36737 c36737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21315
  · exact u21316
  · exact u21317

def r36738 : Route 9 := (fun mask => (mask,id))

def c36738 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36738 : Upper (D 6) (R 6) [34,72,144,257,96] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,96] 13 (by decide) (choices 1) [1,2,4] r36738 c36738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21318
  · exact u21319
  · exact u21320

def r36739 : Route 9 := (fun mask => (mask,id))

def c36739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36739 : Upper (D 6) (R 6) [34,72,144,258,5] 13 := by
  apply FastRouting.sound _ _ [34,72,144,258,5] 13 (by decide) (choices 1) [1,4,64] r36739 c36739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21321
  · exact u21322
  · exact u21323

def b36740 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 148 266 49 101 69 197 325), lower := (rows 35 74 148 266 49 32 64 128 256), losses := [] }

theorem u36740 : Upper (D 6) (R 6) [34,72,144,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36741 : Route 9 := (fun mask => (mask,id))

def c36741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36741 : Upper (D 6) (R 6) [34,72,144,258,36] 13 := by
  apply FastRouting.sound _ _ [34,72,144,258,36] 13 (by decide) (choices 1) [1,4,64] r36741 c36741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21324
  · exact u21325
  · exact u21326

def b36742 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 4, region := 164, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 148 266 81 37 101 165 293), lower := (rows 35 74 148 266 81 32 64 128 256), losses := [] }

theorem u36742 : Upper (D 6) (R 6) [34,72,144,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36743 : Route 9 := (fun mask => (mask,id))

def c36743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36743 : Upper (D 6) (R 6) [34,72,144,258,68] 13 := by
  apply FastRouting.sound _ _ [34,72,144,258,68] 13 (by decide) (choices 1) [1,4] r36743 c36743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21327
  · exact u21328

def r36744 : Route 9 := (fun mask => (mask,id))

def c36744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36744 : Upper (D 6) (R 6) [34,72,144,258,96] 13 := by
  apply FastRouting.sound _ _ [34,72,144,258,96] 13 (by decide) (choices 1) [1,4] r36744 c36744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21329
  · exact u21330

def b36745 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 148 268 19 101 101 229 357), lower := (rows 35 74 148 268 19 32 64 128 256), losses := [] }

theorem u36745 : Upper (D 6) (R 6) [34,72,144,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36746 : Route 9 := (fun mask => (mask,id))

def c36746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36746 : Upper (D 6) (R 6) [34,72,144,260,5] 13 := by
  apply FastRouting.sound _ _ [34,72,144,260,5] 13 (by decide) (choices 1) [1,2,64] r36746 c36746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21331
  · exact u21332
  · exact u21333

def r36747 : Route 9 := (fun mask => (mask,id))

def c36747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36747 : Upper (D 6) (R 6) [34,72,144,260,6] 13 := by
  apply FastRouting.sound _ _ [34,72,144,260,6] 13 (by decide) (choices 1) [1,64] r36747 c36747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21334
  · exact u21335

def b36748 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 148 268 49 103 71 199 327), lower := (rows 35 74 148 268 49 32 64 128 256), losses := [] }

theorem u36748 : Upper (D 6) (R 6) [34,72,144,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36749 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 148 268 50 101 69 197 325), lower := (rows 35 74 148 268 50 32 64 128 256), losses := [] }

theorem u36749 : Upper (D 6) (R 6) [34,72,144,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36750 : Route 9 := (fun mask => (mask,id))

def c36750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36750 : Upper (D 6) (R 6) [34,72,144,260,36] 13 := by
  apply FastRouting.sound _ _ [34,72,144,260,36] 13 (by decide) (choices 1) [1,2,64] r36750 c36750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21336
  · exact u21337
  · exact u21338

def r36751 : Route 9 := (fun mask => (mask,id))

def c36751 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36751 : Upper (D 6) (R 6) [34,72,144,260,65] 13 := by
  apply FastRouting.sound _ _ [34,72,144,260,65] 13 (by decide) (choices 1) [1,2,4] r36751 c36751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21339
  · exact u21340
  · exact u21341

def b36752 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 148 268 82 37 101 165 293), lower := (rows 35 74 148 268 82 32 64 128 256), losses := [] }

theorem u36752 : Upper (D 6) (R 6) [34,72,144,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36753 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 148 268 84 35 99 163 291), lower := (rows 35 74 148 268 84 32 64 128 256), losses := [] }

theorem u36753 : Upper (D 6) (R 6) [34,72,144,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36754 : Route 9 := (fun mask => (mask,id))

def c36754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36754 : Upper (D 6) (R 6) [34,72,144,260,96] 13 := by
  apply FastRouting.sound _ _ [34,72,144,260,96] 13 (by decide) (choices 1) [1,2,4] r36754 c36754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21342
  · exact u21343
  · exact u21344

def b36755 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 148 296 19 101 69 197 325), lower := (rows 35 74 148 296 19 32 64 128 256), losses := [] }

theorem u36755 : Upper (D 6) (R 6) [34,72,144,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36756 : Route 9 := (fun mask => (mask,id))

def c36756 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36756 : Upper (D 6) (R 6) [34,72,144,288,5] 13 := by
  apply FastRouting.sound _ _ [34,72,144,288,5] 13 (by decide) (choices 1) [1,2,4,64] r36756 c36756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21345
  · exact u21346
  · exact u21347
  · exact u21348

def r36757 : Route 9 := (fun mask => (mask,id))

def c36757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36757 : Upper (D 6) (R 6) [34,72,144,288,6] 13 := by
  apply FastRouting.sound _ _ [34,72,144,288,6] 13 (by decide) (choices 1) [1,4,64] r36757 c36757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21349
  · exact u21350
  · exact u21351

def r36758 : Route 9 := (fun mask => (mask,id))

def c36758 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36758 : Upper (D 6) (R 6) [34,72,144,288,65] 13 := by
  apply FastRouting.sound _ _ [34,72,144,288,65] 13 (by decide) (choices 1) [1,2,4] r36758 c36758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21352
  · exact u21353
  · exact u21354

def b36759 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 148 296 82 37 69 133 261), lower := (rows 35 74 148 296 82 32 64 128 256), losses := [] }

theorem u36759 : Upper (D 6) (R 6) [34,72,144,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36760 : Route 9 := (fun mask => (mask,id))

def c36760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36760 : Upper (D 6) (R 6) [34,72,144,288,68] 13 := by
  apply FastRouting.sound _ _ [34,72,144,288,68] 13 (by decide) (choices 1) [1,2,4] r36760 c36760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21355
  · exact u21356
  · exact u21357

def b36761 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 164 13 19 372 340 468 340), lower := (rows 35 74 164 13 19 32 64 128 256), losses := [] }

theorem u36761 : Upper (D 6) (R 6) [34,72,160,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36762 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 74 164 13 21 370 338 466 338), lower := (rows 35 74 164 13 21 32 64 128 256), losses := [] }

theorem u36762 : Upper (D 6) (R 6) [34,72,160,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36763 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 338, targets := 32 },{ cop := 4, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 74 164 13 22 369 337 465 337), lower := (rows 35 74 164 13 22 32 64 128 256), losses := [] }

theorem u36763 : Upper (D 6) (R 6) [34,72,160,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36764 : Route 9 := (fun mask => (mask,id))

def c36764 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36764 : Upper (D 6) (R 6) [34,72,160,5,65] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5,65] 13 (by decide) (choices 1) [2,4,16,256] r36764 c36764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21358
  · exact u21359
  · exact u21360
  · exact u21361

def b36765 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 164 13 82 309 341 405 277), lower := (rows 35 74 164 13 82 32 64 128 256), losses := [] }

theorem u36765 : Upper (D 6) (R 6) [34,72,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36766 : Route 9 := (fun mask => (mask,id))

def c36766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36766 : Upper (D 6) (R 6) [34,72,160,5,68] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5,68] 13 (by decide) (choices 1) [1,2,16,256] r36766 c36766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21362
  · exact u21363
  · exact u21364
  · exact u21365

def r36767 : Route 9 := (fun mask => (mask,id))

def c36767 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36767 : Upper (D 6) (R 6) [34,72,160,5,257] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5,257] 13 (by decide) (choices 1) [2,4,16,64] r36767 c36767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21366
  · exact u21367
  · exact u21368
  · exact u21369

def r36768 : Route 9 := (fun mask => (mask,id))

def c36768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36768 : Upper (D 6) (R 6) [34,72,160,5,258] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5,258] 13 (by decide) (choices 1) [1,4,16,64] r36768 c36768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21370
  · exact u21371
  · exact u21372
  · exact u21373

def r36769 : Route 9 := (fun mask => (mask,id))

def c36769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36769 : Upper (D 6) (R 6) [34,72,160,5,260] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5,260] 13 (by decide) (choices 1) [1,2,16,64] r36769 c36769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21374
  · exact u21375
  · exact u21376
  · exact u21377

def r36770 : Route 9 := (fun mask => (mask,id))

def c36770 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36770 : Upper (D 6) (R 6) [34,72,160,5,320] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5,320] 13 (by decide) (choices 1) [1,2,4,16] r36770 c36770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21378
  · exact u21379
  · exact u21380
  · exact u21381

def b36771 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 74 164 14 21 369 337 465 337), lower := (rows 35 74 164 14 21 32 64 128 256), losses := [] }

theorem u36771 : Upper (D 6) (R 6) [34,72,160,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36772 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 164 14 81 309 341 405 277), lower := (rows 35 74 164 14 81 32 64 128 256), losses := [] }

theorem u36772 : Upper (D 6) (R 6) [34,72,160,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36773 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 164 14 84 305 337 401 273), lower := (rows 35 74 164 14 84 32 64 128 256), losses := [] }

theorem u36773 : Upper (D 6) (R 6) [34,72,160,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36774 : Route 9 := (fun mask => (mask,id))

def c36774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36774 : Upper (D 6) (R 6) [34,72,160,6,257] 13 := by
  apply FastRouting.sound _ _ [34,72,160,6,257] 13 (by decide) (choices 1) [1,4,16,64] r36774 c36774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21382
  · exact u21383
  · exact u21384
  · exact u21385

def r36775 : Route 9 := (fun mask => (mask,id))

def c36775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36775 : Upper (D 6) (R 6) [34,72,160,6,260] 13 := by
  apply FastRouting.sound _ _ [34,72,160,6,260] 13 (by decide) (choices 1) [1,16,64] r36775 c36775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21386
  · exact u21387
  · exact u21388

def r36776 : Route 9 := (fun mask => (mask,id))

def c36776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36776 : Upper (D 6) (R 6) [34,72,160,6,320] 13 := by
  apply FastRouting.sound _ _ [34,72,160,6,320] 13 (by decide) (choices 1) [1,4,16] r36776 c36776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21389
  · exact u21390
  · exact u21391

def b36777 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 164 25 19 356 324 452 324), lower := (rows 35 74 164 25 19 32 64 128 256), losses := [] }

theorem u36777 : Upper (D 6) (R 6) [34,72,160,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36778 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 164 25 21 358 326 454 326), lower := (rows 35 74 164 25 21 32 64 128 256), losses := [] }

theorem u36778 : Upper (D 6) (R 6) [34,72,160,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36779 : Route 9 := (fun mask => (mask,id))

def c36779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36779 : Upper (D 6) (R 6) [34,72,160,17,6] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17,6] 13 (by decide) (choices 1) [1,4,64,256] r36779 c36779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21392
  · exact u21393
  · exact u21394
  · exact u21395

#print axioms u36779
end Delivery.IrregularNine14.P06
