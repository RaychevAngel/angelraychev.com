import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0605
import IrregularNine14P06C0606
import IrregularNine14P06C0607
import IrregularNine14P06C0608
import IrregularNine14P06C0609
import IrregularNine14P06C0610

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42660_3 : Upper (D 6) (R 6) [34,68,384,20,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36315

theorem m42660_9 : Upper (D 6) (R 6) [34,68,384,20,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36337

theorem m42660_10 : Upper (D 6) (R 6) [34,68,384,20,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36347

def r42660 : Route 9 := (fun mask => (mask,id))

def c42660 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42660 : Upper (D 6) (R 6) [34,68,384,20] 13 := by
  apply FastRouting.sound _ _ [34,68,384,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r42660 c42660
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42660_3
  · exact m42660_9
  · exact m42660_10
  · exact u36355
  · exact u36356
  · exact u36357
  · exact u36358
  · exact u36359
  · exact u36360
  · exact u36361

def b42661 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 388 41 95 127 95 223 351), lower := (rows 35 70 388 41 16 32 64 128 256), losses := [] }

theorem u42661 : Upper (D 6) (R 6) [34,68,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42662 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 388 42 93 125 93 221 349), lower := (rows 35 70 388 42 16 32 64 128 256), losses := [] }

theorem u42662 : Upper (D 6) (R 6) [34,68,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42663_3 : Upper (D 6) (R 6) [34,68,384,36,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36316

theorem m42663_9 : Upper (D 6) (R 6) [34,68,384,36,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36340

theorem m42663_10 : Upper (D 6) (R 6) [34,68,384,36,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36349

def r42663 : Route 9 := (fun mask => (mask,id))

def c42663 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42663 : Upper (D 6) (R 6) [34,68,384,36] 13 := by
  apply FastRouting.sound _ _ [34,68,384,36] 13 (by decide) (choices 2) [3,9,10,65,66,72] r42663 c42663
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42663_3
  · exact m42663_9
  · exact m42663_10
  · exact u36366
  · exact u36367
  · exact u36368

theorem m42664_3 : Upper (D 6) (R 6) [34,68,384,48,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36317

theorem m42664_5 : Upper (D 6) (R 6) [34,68,384,48,5] 13 :=
  permutation_upper _ _ _ [34,68,384,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36325

theorem m42664_6 : Upper (D 6) (R 6) [34,68,384,48,6] 13 :=
  permutation_upper _ _ _ [34,68,384,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36331

theorem m42664_9 : Upper (D 6) (R 6) [34,68,384,48,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36341

theorem m42664_10 : Upper (D 6) (R 6) [34,68,384,48,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36350

theorem m42664_12 : Upper (D 6) (R 6) [34,68,384,48,12] 13 :=
  permutation_upper _ _ _ [34,68,384,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36357

def r42664 : Route 9 := (fun mask => (mask,id))

def c42664 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42664 : Upper (D 6) (R 6) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42664 c42664
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42664_3
  · exact m42664_5
  · exact m42664_6
  · exact m42664_9
  · exact m42664_10
  · exact m42664_12
  · exact u36369
  · exact u36370
  · exact u36371
  · exact u36372

theorem m42665_3 : Upper (D 6) (R 6) [34,68,384,65,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36318

theorem m42665_5 : Upper (D 6) (R 6) [34,68,384,65,5] 13 :=
  permutation_upper _ _ _ [34,68,384,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36326

theorem m42665_6 : Upper (D 6) (R 6) [34,68,384,65,6] 13 :=
  permutation_upper _ _ _ [34,68,384,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36332

theorem m42665_9 : Upper (D 6) (R 6) [34,68,384,65,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36342

theorem m42665_10 : Upper (D 6) (R 6) [34,68,384,65,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36351

theorem m42665_12 : Upper (D 6) (R 6) [34,68,384,65,12] 13 :=
  permutation_upper _ _ _ [34,68,384,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36358

theorem m42665_33 : Upper (D 6) (R 6) [34,68,384,65,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36362

theorem m42665_34 : Upper (D 6) (R 6) [34,68,384,65,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36364

theorem m42665_36 : Upper (D 6) (R 6) [34,68,384,65,36] 13 :=
  permutation_upper _ _ _ [34,68,384,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36366

theorem m42665_40 : Upper (D 6) (R 6) [34,68,384,65,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36369

def r42665 : Route 9 := (fun mask => (mask,id))

def c42665 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42665 : Upper (D 6) (R 6) [34,68,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r42665 c42665
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42665_3
  · exact m42665_5
  · exact m42665_6
  · exact m42665_9
  · exact m42665_10
  · exact m42665_12
  · exact m42665_33
  · exact m42665_34
  · exact m42665_36
  · exact m42665_40

def b42666 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 388 74 61 61 125 189 317), lower := (rows 35 70 388 74 16 32 64 128 256), losses := [] }

theorem u42666 : Upper (D 6) (R 6) [34,68,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42667 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 388 76 59 59 123 187 315), lower := (rows 35 70 388 76 16 32 64 128 256), losses := [] }

theorem u42667 : Upper (D 6) (R 6) [34,68,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42668_3 : Upper (D 6) (R 6) [34,68,384,80,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36319

theorem m42668_5 : Upper (D 6) (R 6) [34,68,384,80,5] 13 :=
  permutation_upper _ _ _ [34,68,384,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36328

theorem m42668_6 : Upper (D 6) (R 6) [34,68,384,80,6] 13 :=
  permutation_upper _ _ _ [34,68,384,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36333

theorem m42668_9 : Upper (D 6) (R 6) [34,68,384,80,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36345

theorem m42668_10 : Upper (D 6) (R 6) [34,68,384,80,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36353

theorem m42668_12 : Upper (D 6) (R 6) [34,68,384,80,12] 13 :=
  permutation_upper _ _ _ [34,68,384,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36360

theorem m42668_33 : Upper (D 6) (R 6) [34,68,384,80,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36363

theorem m42668_34 : Upper (D 6) (R 6) [34,68,384,80,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36365

theorem m42668_36 : Upper (D 6) (R 6) [34,68,384,80,36] 13 :=
  permutation_upper _ _ _ [34,68,384,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36368

theorem m42668_40 : Upper (D 6) (R 6) [34,68,384,80,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36372

def r42668 : Route 9 := (fun mask => (mask,id))

def c42668 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42668 : Upper (D 6) (R 6) [34,68,384,80] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r42668 c42668
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42668_3
  · exact m42668_5
  · exact m42668_6
  · exact m42668_9
  · exact m42668_10
  · exact m42668_12
  · exact m42668_33
  · exact m42668_34
  · exact m42668_36
  · exact m42668_40

theorem m42669_3 : Upper (D 6) (R 6) [34,68,384,96,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36320

theorem m42669_5 : Upper (D 6) (R 6) [34,68,384,96,5] 13 :=
  permutation_upper _ _ _ [34,68,384,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36329

theorem m42669_6 : Upper (D 6) (R 6) [34,68,384,96,6] 13 :=
  permutation_upper _ _ _ [34,68,384,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36334

theorem m42669_9 : Upper (D 6) (R 6) [34,68,384,96,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36346

theorem m42669_10 : Upper (D 6) (R 6) [34,68,384,96,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36354

theorem m42669_12 : Upper (D 6) (R 6) [34,68,384,96,12] 13 :=
  permutation_upper _ _ _ [34,68,384,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36361

def r42669 : Route 9 := (fun mask => (mask,id))

def c42669 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42669 : Upper (D 6) (R 6) [34,68,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42669 c42669
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42669_3
  · exact m42669_5
  · exact m42669_6
  · exact m42669_9
  · exact m42669_10
  · exact m42669_12

def b42670 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 52 11 469 485 453 453 453), lower := (rows 35 74 52 11 16 32 64 128 256), losses := [] }

theorem u42670 : Upper (D 6) (R 6) [34,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42671 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42671 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42671 : Upper (D 6) (R 6) [34,72,48,5] 13 := by
  apply FastRouting.sound _ _ [34,72,48,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r42671 c42671
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36373
  · exact u36374
  · exact u36375
  · exact u36376
  · exact u36377
  · exact u36378
  · exact u36379
  · exact u36380
  · exact u36381
  · exact u36382
  · exact u36383

def r42672 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42672 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42672 : Upper (D 6) (R 6) [34,72,48,6] 13 := by
  apply FastRouting.sound _ _ [34,72,48,6] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r42672 c42672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36384
  · exact u36385
  · exact u36386
  · exact u36387
  · exact u36388
  · exact u36389
  · exact u36390

def b42673 : PairBound 9 := { available := 391, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 52 73 407 423 455 391 391), lower := (rows 35 74 52 73 16 32 64 128 256), losses := [] }

theorem u42673 : Upper (D 6) (R 6) [34,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42674 : PairBound 9 := { available := 389, camps := [{ cop := 6, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 52 74 405 421 453 389 389), lower := (rows 35 74 52 74 16 32 64 128 256), losses := [] }

theorem u42674 : Upper (D 6) (R 6) [34,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42675 : PairBound 9 := { available := 391, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 52 76 407 423 455 391 391), lower := (rows 35 74 52 76 16 32 64 128 256), losses := [] }

theorem u42675 : Upper (D 6) (R 6) [34,72,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42676 : Route 9 := (fun mask => (mask,id))

def c42676 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42676 : Upper (D 6) (R 6) [34,72,48,129] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42676 c42676
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36391
  · exact u36392
  · exact u36393
  · exact u36394
  · exact u36395
  · exact u36396
  · exact u36397
  · exact u36398
  · exact u36399
  · exact u36400

def r42677 : Route 9 := (fun mask => (mask,id))

def c42677 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42677 : Upper (D 6) (R 6) [34,72,48,130] 13 := by
  apply FastRouting.sound _ _ [34,72,48,130] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42677 c42677
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36401
  · exact u36402
  · exact u36403
  · exact u36404
  · exact u36405
  · exact u36406

def r42678 : Route 9 := (fun mask => (mask,id))

def c42678 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42678 : Upper (D 6) (R 6) [34,72,48,132] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42678 c42678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36407
  · exact u36408
  · exact u36409
  · exact u36410
  · exact u36411
  · exact u36412
  · exact u36413
  · exact u36414
  · exact u36415
  · exact u36416

def b42679 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 309, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 52 200 279 295 327 391 263), lower := (rows 35 74 52 200 16 32 64 128 256), losses := [] }

theorem u42679 : Upper (D 6) (R 6) [34,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42680 : Route 9 := (fun mask => (mask,id))

def c42680 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42680 : Upper (D 6) (R 6) [34,72,48,384] 13 := by
  apply FastRouting.sound _ _ [34,72,48,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42680 c42680
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36417
  · exact u36418
  · exact u36419
  · exact u36420
  · exact u36421
  · exact u36422

def b42681 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 84 11 437 421 485 421 421), lower := (rows 35 74 84 11 16 32 64 128 256), losses := [] }

theorem u42681 : Upper (D 6) (R 6) [34,72,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42682 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42682 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42682 : Upper (D 6) (R 6) [34,72,80,5] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r42682 c42682
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36423
  · exact u36424
  · exact u36425
  · exact u36426
  · exact u36427
  · exact u36428
  · exact u36429
  · exact u36430
  · exact u36431
  · exact u36432
  · exact u36433

def b42683 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 84 14 437 421 485 421 421), lower := (rows 35 74 84 14 16 32 64 128 256), losses := [] }

theorem u42683 : Upper (D 6) (R 6) [34,72,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42684 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 84 41 407 423 455 391 391), lower := (rows 35 74 84 41 16 32 64 128 256), losses := [] }

theorem u42684 : Upper (D 6) (R 6) [34,72,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42685 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 74 84 42 405 421 453 389 389), lower := (rows 35 74 84 42 16 32 64 128 256), losses := [] }

theorem u42685 : Upper (D 6) (R 6) [34,72,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42686 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42686 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42686 : Upper (D 6) (R 6) [34,72,80,36] 13 := by
  apply FastRouting.sound _ _ [34,72,80,36] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42686 c42686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36434
  · exact u36435
  · exact u36436
  · exact u36437
  · exact u36438
  · exact u36439
  · exact u36440

def r42687 : Route 9 := (fun mask => (mask,id))

def c42687 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42687 : Upper (D 6) (R 6) [34,72,80,129] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42687 c42687
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36441
  · exact u36442
  · exact u36443
  · exact u36444
  · exact u36445
  · exact u36446
  · exact u36447
  · exact u36448
  · exact u36449
  · exact u36450

def r42688 : Route 9 := (fun mask => (mask,id))

def c42688 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42688 : Upper (D 6) (R 6) [34,72,80,130] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130] 13 (by decide) (choices 2) [5,33,36,257,260,288] r42688 c42688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36451
  · exact u36452
  · exact u36453
  · exact u36454
  · exact u36455
  · exact u36456

def r42689 : Route 9 := (fun mask => (mask,id))

def c42689 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42689 : Upper (D 6) (R 6) [34,72,80,132] 13 := by
  apply FastRouting.sound _ _ [34,72,80,132] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42689 c42689
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36457
  · exact u36458
  · exact u36459
  · exact u36460
  · exact u36461
  · exact u36462
  · exact u36463
  · exact u36464
  · exact u36465
  · exact u36466

def r42690 : Route 9 := (fun mask => (mask,id))

def c42690 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42690 : Upper (D 6) (R 6) [34,72,80,160] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42690 c42690
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36467
  · exact u36468
  · exact u36469
  · exact u36470
  · exact u36471
  · exact u36472

def r42691 : Route 9 := (fun mask => (mask,id))

def c42691 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42691 : Upper (D 6) (R 6) [34,72,80,384] 13 := by
  apply FastRouting.sound _ _ [34,72,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42691 c42691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36473
  · exact u36474
  · exact u36475
  · exact u36476
  · exact u36477
  · exact u36478

def b42692 : PairBound 9 := { available := 405, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 11 405 437 469 405 405), lower := (rows 35 74 100 11 16 32 64 128 256), losses := [] }

theorem u42692 : Upper (D 6) (R 6) [34,72,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42693 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42693 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42693 : Upper (D 6) (R 6) [34,72,96,5] 13 := by
  apply FastRouting.sound _ _ [34,72,96,5] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42693 c42693
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36479
  · exact u36480
  · exact u36481
  · exact u36482
  · exact u36483
  · exact u36484
  · exact u36485

def b42694 : PairBound 9 := { available := 405, camps := [{ cop := 2, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 14 405 437 469 405 405), lower := (rows 35 74 100 14 16 32 64 128 256), losses := [] }

theorem u42694 : Upper (D 6) (R 6) [34,72,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42695 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42695 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42695 : Upper (D 6) (R 6) [34,72,96,17] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42695 c42695
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36486
  · exact u36487
  · exact u36488
  · exact u36489
  · exact u36490
  · exact u36491
  · exact u36492

def r42696 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42696 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42696 : Upper (D 6) (R 6) [34,72,96,18] 13 := by
  apply FastRouting.sound _ _ [34,72,96,18] 13 (by decide) (choices 2) [5,129,132,384] r42696 c42696
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u36493
  · exact u36494
  · exact u36495
  · exact u36496

def r42697 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42697 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42697 : Upper (D 6) (R 6) [34,72,96,20] 13 := by
  apply FastRouting.sound _ _ [34,72,96,20] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42697 c42697
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36497
  · exact u36498
  · exact u36499
  · exact u36500
  · exact u36501
  · exact u36502
  · exact u36503

def r42698 : Route 9 := (fun mask => (mask,id))

def c42698 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42698 : Upper (D 6) (R 6) [34,72,96,129] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42698 c42698
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36504
  · exact u36505
  · exact u36506
  · exact u36507
  · exact u36508
  · exact u36509

def r42699 : Route 9 := (fun mask => (mask,id))

def c42699 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42699 : Upper (D 6) (R 6) [34,72,96,130] 13 := by
  apply FastRouting.sound _ _ [34,72,96,130] 13 (by decide) (choices 2) [5,257,260] r42699 c42699
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36510
  · exact u36511
  · exact u36512

def r42700 : Route 9 := (fun mask => (mask,id))

def c42700 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42700 : Upper (D 6) (R 6) [34,72,96,132] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42700 c42700
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36513
  · exact u36514
  · exact u36515
  · exact u36516
  · exact u36517
  · exact u36518

def r42701 : Route 9 := (fun mask => (mask,id))

def c42701 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42701 : Upper (D 6) (R 6) [34,72,96,144] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42701 c42701
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36519
  · exact u36520
  · exact u36521
  · exact u36522
  · exact u36523
  · exact u36524

def r42702 : Route 9 := (fun mask => (mask,id))

def c42702 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42702 : Upper (D 6) (R 6) [34,72,96,384] 13 := by
  apply FastRouting.sound _ _ [34,72,96,384] 13 (by decide) (choices 2) [3,5,6] r42702 c42702
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36525
  · exact u36526
  · exact u36527

def b42703 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 133 11 372 372 372 500 372), lower := (rows 35 74 133 11 16 32 64 128 256), losses := [] }

theorem u42703 : Upper (D 6) (R 6) [34,72,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42704 : PairBound 9 := { available := 374, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 74 133 13 374 374 374 502 374), lower := (rows 35 74 133 13 16 32 64 128 256), losses := [] }

theorem u42704 : Upper (D 6) (R 6) [34,72,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42705 : Route 9 := (fun mask => (mask,id))

def c42705 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42705 : Upper (D 6) (R 6) [34,72,129,6] 13 := by
  apply FastRouting.sound _ _ [34,72,129,6] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42705 c42705
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36528
  · exact u36529
  · exact u36530
  · exact u36531
  · exact u36532
  · exact u36533
  · exact u36534
  · exact u36535
  · exact u36536
  · exact u36537

def r42706 : Route 9 := (fun mask => (mask,id))

def c42706 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42706 : Upper (D 6) (R 6) [34,72,129,17] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42706 c42706
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36538
  · exact u36539
  · exact u36540
  · exact u36541
  · exact u36542
  · exact u36543
  · exact u36544
  · exact u36545
  · exact u36546
  · exact u36547

def r42707 : Route 9 := (fun mask => (mask,id))

def c42707 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42707 : Upper (D 6) (R 6) [34,72,129,18] 13 := by
  apply FastRouting.sound _ _ [34,72,129,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42707 c42707
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36548
  · exact u36549
  · exact u36550
  · exact u36551
  · exact u36552
  · exact u36553
  · exact u36554
  · exact u36555
  · exact u36556
  · exact u36557

def r42708 : Route 9 := (fun mask => (mask,id))

def c42708 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42708 : Upper (D 6) (R 6) [34,72,129,20] 13 := by
  apply FastRouting.sound _ _ [34,72,129,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42708 c42708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36558
  · exact u36559
  · exact u36560
  · exact u36561
  · exact u36562
  · exact u36563
  · exact u36564
  · exact u36565
  · exact u36566
  · exact u36567
  · exact u36568
  · exact u36569
  · exact u36570
  · exact u36571
  · exact u36572

def b42709 : PairBound 9 := { available := 342, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 133 41 342 374 342 470 342), lower := (rows 35 74 133 41 16 32 64 128 256), losses := [] }

theorem u42709 : Upper (D 6) (R 6) [34,72,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42710 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 74 133 42 341 373 341 469 341), lower := (rows 35 74 133 42 16 32 64 128 256), losses := [] }

theorem u42710 : Upper (D 6) (R 6) [34,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42711 : Route 9 := (fun mask => (mask,id))

def c42711 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42711 : Upper (D 6) (R 6) [34,72,129,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42711 c42711
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36573
  · exact u36574
  · exact u36575
  · exact u36576
  · exact u36577
  · exact u36578
  · exact u36579
  · exact u36580
  · exact u36581
  · exact u36582

def r42712 : Route 9 := (fun mask => (mask,id))

def c42712 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42712 : Upper (D 6) (R 6) [34,72,129,48] 13 := by
  apply FastRouting.sound _ _ [34,72,129,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42712 c42712
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36583
  · exact u36584
  · exact u36585
  · exact u36586
  · exact u36587
  · exact u36588
  · exact u36589
  · exact u36590
  · exact u36591
  · exact u36592

def b42713 : PairBound 9 := { available := 310, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 133 73 310 310 374 438 310), lower := (rows 35 74 133 73 16 32 64 128 256), losses := [] }

theorem u42713 : Upper (D 6) (R 6) [34,72,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42714 : PairBound 9 := { available := 309, camps := [{ cop := 6, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 74 309 309 373 437 309), lower := (rows 35 74 133 74 16 32 64 128 256), losses := [] }

theorem u42714 : Upper (D 6) (R 6) [34,72,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42715 : PairBound 9 := { available := 311, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 133 76 311 311 375 439 311), lower := (rows 35 74 133 76 16 32 64 128 256), losses := [] }

theorem u42715 : Upper (D 6) (R 6) [34,72,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42716 : PairBound 9 := { available := 295, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 133 88 311 295 359 423 295), lower := (rows 35 74 133 88 16 32 64 128 256), losses := [] }

theorem u42716 : Upper (D 6) (R 6) [34,72,129,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42717 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 133 104 279 311 343 407 279), lower := (rows 35 74 133 104 16 32 64 128 256), losses := [] }

theorem u42717 : Upper (D 6) (R 6) [34,72,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42718 : Route 9 := (fun mask => (mask,id))

def c42718 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42718 : Upper (D 6) (R 6) [34,72,129,257] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42718 c42718
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36593
  · exact u36594
  · exact u36595
  · exact u36596
  · exact u36597
  · exact u36598

def r42719 : Route 9 := (fun mask => (mask,id))

def c42719 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42719 : Upper (D 6) (R 6) [34,72,129,258] 13 := by
  apply FastRouting.sound _ _ [34,72,129,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42719 c42719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36599
  · exact u36600
  · exact u36601
  · exact u36602
  · exact u36603
  · exact u36604

#print axioms u42719
end Delivery.IrregularNine14.P06
