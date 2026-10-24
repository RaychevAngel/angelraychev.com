import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0438
import IrregularNine14P06C0439
import IrregularNine14P06C0440

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m39720_4 : Upper (D 6) (R 6) [40,129,257,6,96,4] 13 :=
  permutation_upper _ _ _ [40,129,257,6,96,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26327

def r39720 : Route 9 := (fun mask => (mask,id))

def c39720 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39720 : Upper (D 6) (R 6) [40,129,257,6,96] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6,96] 13 (by decide) (choices 1) [2,4,16,64] r39720 c39720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26327
  · exact m39720_4
  · exact u26328
  · exact u26329

def b39721 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 261 26 22 100 100 228 356), lower := (rows 41 131 261 26 22 32 64 128 256), losses := [] }

theorem u39721 : Upper (D 6) (R 6) [40,129,257,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39722 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 131 261 26 50 100 68 196 324), lower := (rows 41 131 261 26 50 32 64 128 256), losses := [] }

theorem u39722 : Upper (D 6) (R 6) [40,129,257,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39723 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 261 26 52 102 70 198 326), lower := (rows 41 131 261 26 52 32 64 128 256), losses := [{ target := 5, region := (rows 1 7 7 24 16 0 95 159 287), good := (rows 463 455 455 478 478 0 64 128 256) }] }

theorem u39723 : Upper (D 6) (R 6) [40,129,257,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39724 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 261 26 82 100 100 228 356), lower := (rows 41 131 261 26 82 32 64 128 256), losses := [] }

theorem u39724 : Upper (D 6) (R 6) [40,129,257,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39725 : Route 9 := (fun mask => (mask,id))

def c39725 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39725 : Upper (D 6) (R 6) [40,129,257,18,68] 13 := by
  apply FastRouting.sound _ _ [40,129,257,18,68] 13 (by decide) (choices 1) [2,4,64] r39725 c39725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26330
  · exact u26331
  · exact u26332

def r39726 : Route 9 := (fun mask => (mask,id))

def c39726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39726 : Upper (D 6) (R 6) [40,129,257,18,96] 13 := by
  apply FastRouting.sound _ _ [40,129,257,18,96] 13 (by decide) (choices 1) [2,4,64] r39726 c39726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26333
  · exact u26334
  · exact u26335

def r39727 : Route 9 := (fun mask => (mask,id))

def c39727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39727 : Upper (D 6) (R 6) [40,129,257,66,6] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,6] 13 (by decide) (choices 1) [4,16,64] r39727 c39727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26336
  · exact u26337
  · exact u26338

def r39728 : Route 9 := (fun mask => (mask,id))

def c39728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39728 : Upper (D 6) (R 6) [40,129,257,66,34] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,34] 13 (by decide) (choices 1) [4,16,64] r39728 c39728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26339
  · exact u26340
  · exact u26341

def r39729 : Route 9 := (fun mask => (mask,id))

def c39729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39729 : Upper (D 6) (R 6) [40,129,257,66,36] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,36] 13 (by decide) (choices 1) [2,4,16,64] r39729 c39729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26342
  · exact u26343
  · exact u26344
  · exact u26345

def b39730 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 131 261 74 82 52 116 180 308), lower := (rows 41 131 261 74 82 32 64 128 256), losses := [] }

theorem u39730 : Upper (D 6) (R 6) [40,129,257,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39731 : Route 9 := (fun mask => (mask,id))

def c39731 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39731 : Upper (D 6) (R 6) [40,129,257,66,68] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,68] 13 (by decide) (choices 1) [2,4,16] r39731 c39731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26346
  · exact u26347
  · exact u26348

def r39732 : Route 9 := (fun mask => (mask,id))

def c39732 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39732 : Upper (D 6) (R 6) [40,129,257,66,96] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,96] 13 (by decide) (choices 1) [2,4,16] r39732 c39732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26349
  · exact u26350
  · exact u26351

theorem m39733_4 : Upper (D 6) (R 6) [40,129,257,80,6,4] 13 :=
  permutation_upper _ _ _ [40,129,257,80,6,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26352

def r39733 : Route 9 := (fun mask => (mask,id))

def c39733 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39733 : Upper (D 6) (R 6) [40,129,257,80,6] 13 := by
  apply FastRouting.sound _ _ [40,129,257,80,6] 13 (by decide) (choices 1) [2,4,64] r39733 c39733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26352
  · exact m39733_4
  · exact u26353

def b39734 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 261 88 50 102 70 198 326), lower := (rows 41 131 261 88 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 7 7 24 16 0 87 151 279), good := (rows 463 455 455 472 478 0 64 128 256) }] }

theorem u39734 : Upper (D 6) (R 6) [40,129,257,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39735 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 261 88 82 38 102 166 294), lower := (rows 41 131 261 88 82 32 64 128 256), losses := [] }

theorem u39735 : Upper (D 6) (R 6) [40,129,257,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39736 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 261 88 112 38 70 134 262), lower := (rows 41 131 261 88 112 32 64 128 256), losses := [] }

theorem u39736 : Upper (D 6) (R 6) [40,129,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39737 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 41 131 262 13 22 112 112 240 368), lower := (rows 41 131 262 13 22 32 64 128 256), losses := [] }

theorem u39737 : Upper (D 6) (R 6) [40,129,258,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39738 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 262 13 50 116 84 212 340), lower := (rows 41 131 262 13 50 32 64 128 256), losses := [] }

theorem u39738 : Upper (D 6) (R 6) [40,129,258,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39739 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 262 13 52 114 82 210 338), lower := (rows 41 131 262 13 52 32 64 128 256), losses := [] }

theorem u39739 : Upper (D 6) (R 6) [40,129,258,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39740 : Route 9 := (fun mask => (mask,id))

def c39740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39740 : Upper (D 6) (R 6) [40,129,258,5,66] 13 := by
  apply FastRouting.sound _ _ [40,129,258,5,66] 13 (by decide) (choices 1) [4,16,64] r39740 c39740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26354
  · exact u26355
  · exact u26356

def r39741 : Route 9 := (fun mask => (mask,id))

def c39741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39741 : Upper (D 6) (R 6) [40,129,258,5,68] 13 := by
  apply FastRouting.sound _ _ [40,129,258,5,68] 13 (by decide) (choices 1) [2,16,64] r39741 c39741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26357
  · exact u26358
  · exact u26359

def r39742 : Route 9 := (fun mask => (mask,id))

def c39742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39742 : Upper (D 6) (R 6) [40,129,258,5,96] 13 := by
  apply FastRouting.sound _ _ [40,129,258,5,96] 13 (by decide) (choices 1) [2,4,16,64] r39742 c39742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26360
  · exact u26361
  · exact u26362
  · exact u26363

def b39743 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 41 131 262 25 22 100 100 228 356), lower := (rows 41 131 262 25 22 32 64 128 256), losses := [] }

theorem u39743 : Upper (D 6) (R 6) [40,129,258,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39744 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 25 50 100 68 196 324), lower := (rows 41 131 262 25 50 32 64 128 256), losses := [] }

theorem u39744 : Upper (D 6) (R 6) [40,129,258,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39745 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 25 52 102 70 198 326), lower := (rows 41 131 262 25 52 32 64 128 256), losses := [] }

theorem u39745 : Upper (D 6) (R 6) [40,129,258,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39746 : Route 9 := (fun mask => (mask,id))

def c39746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39746 : Upper (D 6) (R 6) [40,129,258,17,66] 13 := by
  apply FastRouting.sound _ _ [40,129,258,17,66] 13 (by decide) (choices 1) [4,64] r39746 c39746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26364
  · exact u26365

def r39747 : Route 9 := (fun mask => (mask,id))

def c39747 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39747 : Upper (D 6) (R 6) [40,129,258,17,68] 13 := by
  apply FastRouting.sound _ _ [40,129,258,17,68] 13 (by decide) (choices 1) [2,4,64] r39747 c39747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26366
  · exact u26367
  · exact u26368

def b39748 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 25 112 102 70 198 326), lower := (rows 41 131 262 25 112 32 64 128 256), losses := [] }

theorem u39748 : Upper (D 6) (R 6) [40,129,258,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39749 : Route 9 := (fun mask => (mask,id))

def c39749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39749 : Upper (D 6) (R 6) [40,129,258,18,5] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,5] 13 (by decide) (choices 1) [4,64] r39749 c39749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26369
  · exact u26370

def b39750 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 262 26 49 100 68 196 324), lower := (rows 41 131 262 26 49 32 64 128 256), losses := [] }

theorem u39750 : Upper (D 6) (R 6) [40,129,258,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39751 : Route 9 := (fun mask => (mask,id))

def c39751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39751 : Upper (D 6) (R 6) [40,129,258,18,36] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,36] 13 (by decide) (choices 1) [1,4,64] r39751 c39751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26371
  · exact u26372
  · exact u26373

def r39752 : Route 9 := (fun mask => (mask,id))

def c39752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39752 : Upper (D 6) (R 6) [40,129,258,18,65] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,65] 13 (by decide) (choices 1) [4,64] r39752 c39752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26374
  · exact u26375

def r39753 : Route 9 := (fun mask => (mask,id))

def c39753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39753 : Upper (D 6) (R 6) [40,129,258,18,68] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,68] 13 (by decide) (choices 1) [1,4,64] r39753 c39753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26376
  · exact u26377
  · exact u26378

def r39754 : Route 9 := (fun mask => (mask,id))

def c39754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39754 : Upper (D 6) (R 6) [40,129,258,18,96] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,96] 13 (by decide) (choices 1) [1,4,64] r39754 c39754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26379
  · exact u26380
  · exact u26381

def b39755 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 262 28 19 100 100 228 356), lower := (rows 41 131 262 28 19 32 64 128 256), losses := [] }

theorem u39755 : Upper (D 6) (R 6) [40,129,258,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39756 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 262 28 21 98 98 226 354), lower := (rows 41 131 262 28 21 32 64 128 256), losses := [] }

theorem u39756 : Upper (D 6) (R 6) [40,129,258,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39757 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 131 262 28 22 97 97 225 353), lower := (rows 41 131 262 28 22 32 64 128 256), losses := [] }

theorem u39757 : Upper (D 6) (R 6) [40,129,258,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39758 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 262 28 49 102 70 198 326), lower := (rows 41 131 262 28 49 32 64 128 256), losses := [] }

theorem u39758 : Upper (D 6) (R 6) [40,129,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39759 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 41 131 262 28 50 101 69 197 325), lower := (rows 41 131 262 28 50 32 64 128 256), losses := [] }

theorem u39759 : Upper (D 6) (R 6) [40,129,258,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39760 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 262 28 52 99 67 195 323), lower := (rows 41 131 262 28 52 32 64 128 256), losses := [] }

theorem u39760 : Upper (D 6) (R 6) [40,129,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39761 : Route 9 := (fun mask => (mask,id))

def c39761 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39761 : Upper (D 6) (R 6) [40,129,258,20,65] 13 := by
  apply FastRouting.sound _ _ [40,129,258,20,65] 13 (by decide) (choices 1) [2,4,64] r39761 c39761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26382
  · exact u26383
  · exact u26384

def r39762 : Route 9 := (fun mask => (mask,id))

def c39762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39762 : Upper (D 6) (R 6) [40,129,258,20,66] 13 := by
  apply FastRouting.sound _ _ [40,129,258,20,66] 13 (by decide) (choices 1) [1,4,64] r39762 c39762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26385
  · exact u26386
  · exact u26387

def b39763 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 262 28 84 99 99 227 355), lower := (rows 41 131 262 28 84 32 64 128 256), losses := [] }

theorem u39763 : Upper (D 6) (R 6) [40,129,258,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39764 : Route 9 := (fun mask => (mask,id))

def c39764 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39764 : Upper (D 6) (R 6) [40,129,258,20,96] 13 := by
  apply FastRouting.sound _ _ [40,129,258,20,96] 13 (by decide) (choices 1) [1,2,4,64] r39764 c39764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26388
  · exact u26389
  · exact u26390
  · exact u26391

def b39765 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 41 131 262 73 22 116 116 244 372), lower := (rows 41 131 262 73 22 32 64 128 256), losses := [] }

theorem u39765 : Upper (D 6) (R 6) [40,129,258,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39766 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 262 73 50 116 84 212 340), lower := (rows 41 131 262 73 50 32 64 128 256), losses := [] }

theorem u39766 : Upper (D 6) (R 6) [40,129,258,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39767 : Route 9 := (fun mask => (mask,id))

def c39767 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39767 : Upper (D 6) (R 6) [40,129,258,65,36] 13 := by
  apply FastRouting.sound _ _ [40,129,258,65,36] 13 (by decide) (choices 1) [2,4,16,64] r39767 c39767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26392
  · exact u26393
  · exact u26394
  · exact u26395

def b39768 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 41 131 262 73 82 52 116 180 308), lower := (rows 41 131 262 73 82 32 64 128 256), losses := [] }

theorem u39768 : Upper (D 6) (R 6) [40,129,258,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39769 : Route 9 := (fun mask => (mask,id))

def c39769 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39769 : Upper (D 6) (R 6) [40,129,258,65,68] 13 := by
  apply FastRouting.sound _ _ [40,129,258,65,68] 13 (by decide) (choices 1) [2,4,16] r39769 c39769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26396
  · exact u26397
  · exact u26398

def b39770 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 262 73 112 54 86 150 278), lower := (rows 41 131 262 73 112 32 64 128 256), losses := [] }

theorem u39770 : Upper (D 6) (R 6) [40,129,258,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39771 : Route 9 := (fun mask => (mask,id))

def c39771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39771 : Upper (D 6) (R 6) [40,129,258,66,5] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,5] 13 (by decide) (choices 1) [4,16,64] r39771 c39771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26399
  · exact u26400
  · exact u26401

def b39772 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 262 74 49 116 84 212 340), lower := (rows 41 131 262 74 49 32 64 128 256), losses := [] }

theorem u39772 : Upper (D 6) (R 6) [40,129,258,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39773 : Route 9 := (fun mask => (mask,id))

def c39773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39773 : Upper (D 6) (R 6) [40,129,258,66,36] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,36] 13 (by decide) (choices 1) [1,4,16,64] r39773 c39773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26402
  · exact u26403
  · exact u26404
  · exact u26405

def r39774 : Route 9 := (fun mask => (mask,id))

def c39774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39774 : Upper (D 6) (R 6) [40,129,258,66,65] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,65] 13 (by decide) (choices 1) [4,16] r39774 c39774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26406
  · exact u26407

def r39775 : Route 9 := (fun mask => (mask,id))

def c39775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39775 : Upper (D 6) (R 6) [40,129,258,66,68] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,68] 13 (by decide) (choices 1) [1,4,16] r39775 c39775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26408
  · exact u26409
  · exact u26410

def r39776 : Route 9 := (fun mask => (mask,id))

def c39776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39776 : Upper (D 6) (R 6) [40,129,258,66,96] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,96] 13 (by decide) (choices 1) [1,4,16] r39776 c39776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26411
  · exact u26412
  · exact u26413

def b39777 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 262 76 19 116 116 244 372), lower := (rows 41 131 262 76 19 32 64 128 256), losses := [] }

theorem u39777 : Upper (D 6) (R 6) [40,129,258,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39778 : Route 9 := (fun mask => (mask,id))

def c39778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39778 : Upper (D 6) (R 6) [40,129,258,68,5] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68,5] 13 (by decide) (choices 1) [2,16,64] r39778 c39778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26414
  · exact u26415
  · exact u26416

def b39779 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 131 262 76 22 113 113 241 369), lower := (rows 41 131 262 76 22 32 64 128 256), losses := [] }

theorem u39779 : Upper (D 6) (R 6) [40,129,258,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39779
end Delivery.IrregularNine14.P06
