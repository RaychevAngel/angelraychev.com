import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0274
import IrregularNine14P08C0275
import IrregularNine14P08C0276
import IrregularNine14P08C0277

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22680 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 56 245 229 229 229 485), lower := (rows 259 67 44 56 16 32 64 128 256), losses := [] }

theorem u22680 : Upper (D 8) (R 8) [258,65,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22681 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 67 44 73 180 180 244 180 436), lower := (rows 259 67 44 73 16 32 64 128 256), losses := [] }

theorem u22681 : Upper (D 8) (R 8) [258,65,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22682 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 44 76 177 177 241 177 433), lower := (rows 259 67 44 76 16 32 64 128 256), losses := [] }

theorem u22682 : Upper (D 8) (R 8) [258,65,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22683_5 : Upper (D 8) (R 8) [258,65,40,80,5] 13 :=
  permutation_upper _ _ _ [258,65,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16460

theorem m22683_33 : Upper (D 8) (R 8) [258,65,40,80,33] 13 :=
  permutation_upper _ _ _ [258,65,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16512

theorem m22683_36 : Upper (D 8) (R 8) [258,65,40,80,36] 13 :=
  permutation_upper _ _ _ [258,65,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16529

def r22683 : Route 9 := (fun mask => (mask,id))

def c22683 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22683 : Upper (D 8) (R 8) [258,65,40,80] 13 := by
  apply FastRouting.sound _ _ [258,65,40,80] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22683 c22683
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22683_5
  · exact m22683_33
  · exact m22683_36
  · exact u16537
  · exact u16538
  · exact u16539

def b22684 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 104 181 181 245 181 437), lower := (rows 259 67 44 104 16 32 64 128 256), losses := [] }

theorem u22684 : Upper (D 8) (R 8) [258,65,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22685 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 137 244 244 244 244 500), lower := (rows 259 67 44 137 16 32 64 128 256), losses := [] }

theorem u22685 : Upper (D 8) (R 8) [258,65,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22686_33 : Upper (D 8) (R 8) [258,65,40,132,33] 13 :=
  permutation_upper _ _ _ [258,65,33,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16514

def r22686 : Route 9 := (fun mask => (mask,id))

def c22686 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22686 : Upper (D 8) (R 8) [258,65,40,132] 13 := by
  apply FastRouting.sound _ _ [258,65,40,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22686 c22686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22686_33
  · exact u16547
  · exact u16548
  · exact u16549
  · exact u16550
  · exact u16551

theorem m22687_5 : Upper (D 8) (R 8) [258,65,40,144,5] 13 :=
  permutation_upper _ _ _ [258,65,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16461

theorem m22687_33 : Upper (D 8) (R 8) [258,65,40,144,33] 13 :=
  permutation_upper _ _ _ [258,65,33,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16513

theorem m22687_36 : Upper (D 8) (R 8) [258,65,40,144,36] 13 :=
  permutation_upper _ _ _ [258,65,40,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16531

def r22687 : Route 9 := (fun mask => (mask,id))

def c22687 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22687 : Upper (D 8) (R 8) [258,65,40,144] 13 := by
  apply FastRouting.sound _ _ [258,65,40,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22687 c22687
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22687_5
  · exact m22687_33
  · exact m22687_36
  · exact u16552
  · exact u16553
  · exact u16554
  · exact u16555
  · exact u16556
  · exact u16557
  · exact u16558

def b22688 : PairBound 9 := { available := 245, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 168 245 245 245 245 501), lower := (rows 259 67 44 168 16 32 64 128 256), losses := [] }

theorem u22688 : Upper (D 8) (R 8) [258,65,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22689_5 : Upper (D 8) (R 8) [258,65,40,192,5] 13 :=
  permutation_upper _ _ _ [258,65,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16462

theorem m22689_33 : Upper (D 8) (R 8) [258,65,40,192,33] 13 :=
  permutation_upper _ _ _ [258,65,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16515

theorem m22689_36 : Upper (D 8) (R 8) [258,65,40,192,36] 13 :=
  permutation_upper _ _ _ [258,65,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16533

def r22689 : Route 9 := (fun mask => (mask,id))

def c22689 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22689 : Upper (D 8) (R 8) [258,65,40,192] 13 := by
  apply FastRouting.sound _ _ [258,65,40,192] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22689 c22689
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22689_5
  · exact m22689_33
  · exact m22689_36
  · exact u16564
  · exact u16565
  · exact u16566

theorem m22690_9 : Upper (D 8) (R 8) [258,65,48,68,9] 13 :=
  permutation_upper _ _ _ [258,65,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16464

theorem m22690_33 : Upper (D 8) (R 8) [258,65,48,68,33] 13 :=
  permutation_upper _ _ _ [258,65,33,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16507

theorem m22690_40 : Upper (D 8) (R 8) [258,65,48,68,40] 13 :=
  permutation_upper _ _ _ [258,65,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16529

theorem m22690_129 : Upper (D 8) (R 8) [258,65,48,68,129] 13 :=
  permutation_upper _ _ _ [258,65,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16542

theorem m22690_136 : Upper (D 8) (R 8) [258,65,48,68,136] 13 :=
  permutation_upper _ _ _ [258,65,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16553

theorem m22690_160 : Upper (D 8) (R 8) [258,65,48,68,160] 13 :=
  permutation_upper _ _ _ [258,65,40,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16559

def r22690 : Route 9 := (fun mask => (mask,id))

def c22690 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22690 : Upper (D 8) (R 8) [258,65,48,68] 13 := by
  apply FastRouting.sound _ _ [258,65,48,68] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22690 c22690
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22690_9
  · exact m22690_33
  · exact m22690_40
  · exact m22690_129
  · exact m22690_136
  · exact m22690_160

theorem m22691_5 : Upper (D 8) (R 8) [258,65,48,96,5] 13 :=
  permutation_upper _ _ _ [258,65,9,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16457

theorem m22691_9 : Upper (D 8) (R 8) [258,65,48,96,9] 13 :=
  permutation_upper _ _ _ [258,65,9,96,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16467

theorem m22691_12 : Upper (D 8) (R 8) [258,65,48,96,12] 13 :=
  permutation_upper _ _ _ [258,65,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16490

theorem m22691_33 : Upper (D 8) (R 8) [258,65,48,96,33] 13 :=
  permutation_upper _ _ _ [258,65,33,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16508

theorem m22691_36 : Upper (D 8) (R 8) [258,65,48,96,36] 13 :=
  permutation_upper _ _ _ [258,65,40,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16526

theorem m22691_40 : Upper (D 8) (R 8) [258,65,48,96,40] 13 :=
  permutation_upper _ _ _ [258,65,40,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16530

theorem m22691_129 : Upper (D 8) (R 8) [258,65,48,96,129] 13 :=
  permutation_upper _ _ _ [258,65,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16543

theorem m22691_132 : Upper (D 8) (R 8) [258,65,48,96,132] 13 :=
  permutation_upper _ _ _ [258,65,40,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16548

theorem m22691_136 : Upper (D 8) (R 8) [258,65,48,96,136] 13 :=
  permutation_upper _ _ _ [258,65,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16554

theorem m22691_160 : Upper (D 8) (R 8) [258,65,48,96,160] 13 :=
  permutation_upper _ _ _ [258,65,40,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16560

def r22691 : Route 9 := (fun mask => (mask,id))

def c22691 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22691 : Upper (D 8) (R 8) [258,65,48,96] 13 := by
  apply FastRouting.sound _ _ [258,65,48,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22691 c22691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22691_5
  · exact m22691_9
  · exact m22691_12
  · exact m22691_33
  · exact m22691_36
  · exact m22691_40
  · exact m22691_129
  · exact m22691_132
  · exact m22691_136
  · exact m22691_160

theorem m22692_9 : Upper (D 8) (R 8) [258,65,48,132,9] 13 :=
  permutation_upper _ _ _ [258,65,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16473

theorem m22692_33 : Upper (D 8) (R 8) [258,65,48,132,33] 13 :=
  permutation_upper _ _ _ [258,65,33,36,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16509

theorem m22692_40 : Upper (D 8) (R 8) [258,65,48,132,40] 13 :=
  permutation_upper _ _ _ [258,65,40,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16531

theorem m22692_65 : Upper (D 8) (R 8) [258,65,48,132,65] 13 :=
  permutation_upper _ _ _ [258,65,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16534

theorem m22692_72 : Upper (D 8) (R 8) [258,65,48,132,72] 13 :=
  permutation_upper _ _ _ [258,65,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16538

theorem m22692_96 : Upper (D 8) (R 8) [258,65,48,132,96] 13 :=
  permutation_upper _ _ _ [258,65,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16540

theorem m22692_129 : Upper (D 8) (R 8) [258,65,48,132,129] 13 :=
  permutation_upper _ _ _ [258,65,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16544

theorem m22692_136 : Upper (D 8) (R 8) [258,65,48,132,136] 13 :=
  permutation_upper _ _ _ [258,65,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16556

theorem m22692_160 : Upper (D 8) (R 8) [258,65,48,132,160] 13 :=
  permutation_upper _ _ _ [258,65,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16561

theorem m22692_192 : Upper (D 8) (R 8) [258,65,48,132,192] 13 :=
  permutation_upper _ _ _ [258,65,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16565

def r22692 : Route 9 := (fun mask => (mask,id))

def c22692 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22692 : Upper (D 8) (R 8) [258,65,48,132] 13 := by
  apply FastRouting.sound _ _ [258,65,48,132] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22692 c22692
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22692_9
  · exact m22692_33
  · exact m22692_40
  · exact m22692_65
  · exact m22692_72
  · exact m22692_96
  · exact m22692_129
  · exact m22692_136
  · exact m22692_160
  · exact m22692_192

theorem m22693_5 : Upper (D 8) (R 8) [258,65,48,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16458

theorem m22693_9 : Upper (D 8) (R 8) [258,65,48,160,9] 13 :=
  permutation_upper _ _ _ [258,65,9,160,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16476

theorem m22693_12 : Upper (D 8) (R 8) [258,65,48,160,12] 13 :=
  permutation_upper _ _ _ [258,65,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16492

theorem m22693_33 : Upper (D 8) (R 8) [258,65,48,160,33] 13 :=
  permutation_upper _ _ _ [258,65,33,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16510

theorem m22693_36 : Upper (D 8) (R 8) [258,65,48,160,36] 13 :=
  permutation_upper _ _ _ [258,65,40,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16527

theorem m22693_40 : Upper (D 8) (R 8) [258,65,48,160,40] 13 :=
  permutation_upper _ _ _ [258,65,40,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16532

theorem m22693_65 : Upper (D 8) (R 8) [258,65,48,160,65] 13 :=
  permutation_upper _ _ _ [258,65,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16535

theorem m22693_68 : Upper (D 8) (R 8) [258,65,48,160,68] 13 :=
  permutation_upper _ _ _ [258,65,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16536

theorem m22693_72 : Upper (D 8) (R 8) [258,65,48,160,72] 13 :=
  permutation_upper _ _ _ [258,65,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16539

theorem m22693_96 : Upper (D 8) (R 8) [258,65,48,160,96] 13 :=
  permutation_upper _ _ _ [258,65,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16541

theorem m22693_129 : Upper (D 8) (R 8) [258,65,48,160,129] 13 :=
  permutation_upper _ _ _ [258,65,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16545

theorem m22693_132 : Upper (D 8) (R 8) [258,65,48,160,132] 13 :=
  permutation_upper _ _ _ [258,65,40,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16550

theorem m22693_136 : Upper (D 8) (R 8) [258,65,48,160,136] 13 :=
  permutation_upper _ _ _ [258,65,40,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16557

theorem m22693_160 : Upper (D 8) (R 8) [258,65,48,160,160] 13 :=
  permutation_upper _ _ _ [258,65,40,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16562

theorem m22693_192 : Upper (D 8) (R 8) [258,65,48,160,192] 13 :=
  permutation_upper _ _ _ [258,65,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16566

def r22693 : Route 9 := (fun mask => (mask,id))

def c22693 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22693 : Upper (D 8) (R 8) [258,65,48,160] 13 := by
  apply FastRouting.sound _ _ [258,65,48,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r22693 c22693
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22693_5
  · exact m22693_9
  · exact m22693_12
  · exact m22693_33
  · exact m22693_36
  · exact m22693_40
  · exact m22693_65
  · exact m22693_68
  · exact m22693_72
  · exact m22693_96
  · exact m22693_129
  · exact m22693_132
  · exact m22693_136
  · exact m22693_160
  · exact m22693_192

theorem m22694_5 : Upper (D 8) (R 8) [258,65,48,192,5] 13 :=
  permutation_upper _ _ _ [258,65,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16459

theorem m22694_9 : Upper (D 8) (R 8) [258,65,48,192,9] 13 :=
  permutation_upper _ _ _ [258,65,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16481

theorem m22694_12 : Upper (D 8) (R 8) [258,65,48,192,12] 13 :=
  permutation_upper _ _ _ [258,65,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16493

theorem m22694_33 : Upper (D 8) (R 8) [258,65,48,192,33] 13 :=
  permutation_upper _ _ _ [258,65,33,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16511

theorem m22694_36 : Upper (D 8) (R 8) [258,65,48,192,36] 13 :=
  permutation_upper _ _ _ [258,65,40,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16528

theorem m22694_40 : Upper (D 8) (R 8) [258,65,48,192,40] 13 :=
  permutation_upper _ _ _ [258,65,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16533

theorem m22694_129 : Upper (D 8) (R 8) [258,65,48,192,129] 13 :=
  permutation_upper _ _ _ [258,65,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16546

theorem m22694_132 : Upper (D 8) (R 8) [258,65,48,192,132] 13 :=
  permutation_upper _ _ _ [258,65,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16551

theorem m22694_136 : Upper (D 8) (R 8) [258,65,48,192,136] 13 :=
  permutation_upper _ _ _ [258,65,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16558

theorem m22694_160 : Upper (D 8) (R 8) [258,65,48,192,160] 13 :=
  permutation_upper _ _ _ [258,65,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16563

def r22694 : Route 9 := (fun mask => (mask,id))

def c22694 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22694 : Upper (D 8) (R 8) [258,65,48,192] 13 := by
  apply FastRouting.sound _ _ [258,65,48,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22694 c22694
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22694_5
  · exact m22694_9
  · exact m22694_12
  · exact m22694_33
  · exact m22694_36
  · exact m22694_40
  · exact m22694_129
  · exact m22694_132
  · exact m22694_136
  · exact m22694_160

def b22695 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 69 140 184 184 248 184 440), lower := (rows 259 67 69 140 16 32 64 128 256), losses := [] }

theorem u22695 : Upper (D 8) (R 8) [258,65,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22696 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 69 168 188 188 252 188 444), lower := (rows 259 67 69 168 16 32 64 128 256), losses := [] }

theorem u22696 : Upper (D 8) (R 8) [258,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22697 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 76 137 180 180 244 180 436), lower := (rows 259 67 76 137 16 32 64 128 256), losses := [] }

theorem u22697 : Upper (D 8) (R 8) [258,65,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22698 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 76 140 177 177 241 177 433), lower := (rows 259 67 76 140 16 32 64 128 256), losses := [] }

theorem u22698 : Upper (D 8) (R 8) [258,65,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22699_5 : Upper (D 8) (R 8) [258,65,72,144,5] 13 :=
  permutation_upper _ _ _ [258,65,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16465

theorem m22699_33 : Upper (D 8) (R 8) [258,65,72,144,33] 13 :=
  permutation_upper _ _ _ [258,65,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16518

theorem m22699_36 : Upper (D 8) (R 8) [258,65,72,144,36] 13 :=
  permutation_upper _ _ _ [258,65,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16538

def r22699 : Route 9 := (fun mask => (mask,id))

def c22699 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22699 : Upper (D 8) (R 8) [258,65,72,144] 13 := by
  apply FastRouting.sound _ _ [258,65,72,144] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22699 c22699
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22699_5
  · exact m22699_33
  · exact m22699_36
  · exact u16571
  · exact u16572
  · exact u16573

theorem m22700_5 : Upper (D 8) (R 8) [258,65,72,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16466

theorem m22700_33 : Upper (D 8) (R 8) [258,65,72,160,33] 13 :=
  permutation_upper _ _ _ [258,65,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16519

theorem m22700_36 : Upper (D 8) (R 8) [258,65,72,160,36] 13 :=
  permutation_upper _ _ _ [258,65,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16539

def r22700 : Route 9 := (fun mask => (mask,id))

def c22700 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22700 : Upper (D 8) (R 8) [258,65,72,160] 13 := by
  apply FastRouting.sound _ _ [258,65,72,160] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22700 c22700
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22700_5
  · exact m22700_33
  · exact m22700_36
  · exact u16574
  · exact u16575
  · exact u16576

theorem m22701_9 : Upper (D 8) (R 8) [258,65,80,132,9] 13 :=
  permutation_upper _ _ _ [258,65,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16474

theorem m22701_33 : Upper (D 8) (R 8) [258,65,80,132,33] 13 :=
  permutation_upper _ _ _ [258,65,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16516

theorem m22701_40 : Upper (D 8) (R 8) [258,65,80,132,40] 13 :=
  permutation_upper _ _ _ [258,65,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16553

theorem m22701_129 : Upper (D 8) (R 8) [258,65,80,132,129] 13 :=
  permutation_upper _ _ _ [258,65,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16568

theorem m22701_136 : Upper (D 8) (R 8) [258,65,80,132,136] 13 :=
  permutation_upper _ _ _ [258,65,72,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16572

theorem m22701_160 : Upper (D 8) (R 8) [258,65,80,132,160] 13 :=
  permutation_upper _ _ _ [258,65,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16575

def r22701 : Route 9 := (fun mask => (mask,id))

def c22701 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22701 : Upper (D 8) (R 8) [258,65,80,132] 13 := by
  apply FastRouting.sound _ _ [258,65,80,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22701 c22701
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22701_9
  · exact m22701_33
  · exact m22701_40
  · exact m22701_129
  · exact m22701_136
  · exact m22701_160

theorem m22702_5 : Upper (D 8) (R 8) [258,65,80,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16463

theorem m22702_9 : Upper (D 8) (R 8) [258,65,80,160,9] 13 :=
  permutation_upper _ _ _ [258,65,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16477

theorem m22702_12 : Upper (D 8) (R 8) [258,65,80,160,12] 13 :=
  permutation_upper _ _ _ [258,65,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16496

theorem m22702_33 : Upper (D 8) (R 8) [258,65,80,160,33] 13 :=
  permutation_upper _ _ _ [258,65,33,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16517

theorem m22702_36 : Upper (D 8) (R 8) [258,65,80,160,36] 13 :=
  permutation_upper _ _ _ [258,65,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16536

theorem m22702_40 : Upper (D 8) (R 8) [258,65,80,160,40] 13 :=
  permutation_upper _ _ _ [258,65,40,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16559

theorem m22702_129 : Upper (D 8) (R 8) [258,65,80,160,129] 13 :=
  permutation_upper _ _ _ [258,65,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16569

theorem m22702_132 : Upper (D 8) (R 8) [258,65,80,160,132] 13 :=
  permutation_upper _ _ _ [258,65,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16570

theorem m22702_136 : Upper (D 8) (R 8) [258,65,80,160,136] 13 :=
  permutation_upper _ _ _ [258,65,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16573

theorem m22702_160 : Upper (D 8) (R 8) [258,65,80,160,160] 13 :=
  permutation_upper _ _ _ [258,65,72,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16576

def r22702 : Route 9 := (fun mask => (mask,id))

def c22702 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22702 : Upper (D 8) (R 8) [258,65,80,160] 13 := by
  apply FastRouting.sound _ _ [258,65,80,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22702 c22702
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22702_5
  · exact m22702_9
  · exact m22702_12
  · exact m22702_33
  · exact m22702_36
  · exact m22702_40
  · exact m22702_129
  · exact m22702_132
  · exact m22702_136
  · exact m22702_160

def b22703 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 100 137 188 188 252 188 444), lower := (rows 259 67 100 137 16 32 64 128 256), losses := [] }

theorem u22703 : Upper (D 8) (R 8) [258,65,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22704_9 : Upper (D 8) (R 8) [258,65,96,132,9] 13 :=
  permutation_upper _ _ _ [258,65,9,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16475

theorem m22704_33 : Upper (D 8) (R 8) [258,65,96,132,33] 13 :=
  permutation_upper _ _ _ [258,65,33,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16521

theorem m22704_40 : Upper (D 8) (R 8) [258,65,96,132,40] 13 :=
  permutation_upper _ _ _ [258,65,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16554

theorem m22704_129 : Upper (D 8) (R 8) [258,65,96,132,129] 13 :=
  permutation_upper _ _ _ [258,65,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16577

def r22704 : Route 9 := (fun mask => (mask,id))

def c22704 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22704 : Upper (D 8) (R 8) [258,65,96,132] 13 := by
  apply FastRouting.sound _ _ [258,65,96,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22704 c22704
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22704_9
  · exact m22704_33
  · exact m22704_40
  · exact m22704_129
  · exact u16580
  · exact u16581

theorem m22705_5 : Upper (D 8) (R 8) [258,65,96,144,5] 13 :=
  permutation_upper _ _ _ [258,65,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16468

theorem m22705_9 : Upper (D 8) (R 8) [258,65,96,144,9] 13 :=
  permutation_upper _ _ _ [258,65,9,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16470

theorem m22705_12 : Upper (D 8) (R 8) [258,65,96,144,12] 13 :=
  permutation_upper _ _ _ [258,65,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16498

theorem m22705_33 : Upper (D 8) (R 8) [258,65,96,144,33] 13 :=
  permutation_upper _ _ _ [258,65,33,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16520

theorem m22705_36 : Upper (D 8) (R 8) [258,65,96,144,36] 13 :=
  permutation_upper _ _ _ [258,65,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16540

theorem m22705_40 : Upper (D 8) (R 8) [258,65,96,144,40] 13 :=
  permutation_upper _ _ _ [258,65,40,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16548

theorem m22705_129 : Upper (D 8) (R 8) [258,65,96,144,129] 13 :=
  permutation_upper _ _ _ [258,65,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16578

theorem m22705_132 : Upper (D 8) (R 8) [258,65,96,144,132] 13 :=
  permutation_upper _ _ _ [258,65,96,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16580

def r22705 : Route 9 := (fun mask => (mask,id))

def c22705 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22705 : Upper (D 8) (R 8) [258,65,96,144] 13 := by
  apply FastRouting.sound _ _ [258,65,96,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22705 c22705
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22705_5
  · exact m22705_9
  · exact m22705_12
  · exact m22705_33
  · exact m22705_36
  · exact m22705_40
  · exact m22705_129
  · exact m22705_132
  · exact u16582
  · exact u16583

theorem m22706_5 : Upper (D 8) (R 8) [258,65,96,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16469

theorem m22706_9 : Upper (D 8) (R 8) [258,65,96,160,9] 13 :=
  permutation_upper _ _ _ [258,65,9,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16478

theorem m22706_12 : Upper (D 8) (R 8) [258,65,96,160,12] 13 :=
  permutation_upper _ _ _ [258,65,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16499

theorem m22706_33 : Upper (D 8) (R 8) [258,65,96,160,33] 13 :=
  permutation_upper _ _ _ [258,65,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16522

theorem m22706_36 : Upper (D 8) (R 8) [258,65,96,160,36] 13 :=
  permutation_upper _ _ _ [258,65,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16541

theorem m22706_40 : Upper (D 8) (R 8) [258,65,96,160,40] 13 :=
  permutation_upper _ _ _ [258,65,40,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16560

theorem m22706_129 : Upper (D 8) (R 8) [258,65,96,160,129] 13 :=
  permutation_upper _ _ _ [258,65,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16579

theorem m22706_132 : Upper (D 8) (R 8) [258,65,96,160,132] 13 :=
  permutation_upper _ _ _ [258,65,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16581

theorem m22706_136 : Upper (D 8) (R 8) [258,65,96,160,136] 13 :=
  permutation_upper _ _ _ [258,65,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16583

def r22706 : Route 9 := (fun mask => (mask,id))

def c22706 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22706 : Upper (D 8) (R 8) [258,65,96,160] 13 := by
  apply FastRouting.sound _ _ [258,65,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22706 c22706
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22706_5
  · exact m22706_9
  · exact m22706_12
  · exact m22706_33
  · exact m22706_36
  · exact m22706_40
  · exact m22706_129
  · exact m22706_132
  · exact m22706_136
  · exact u16584

def b22707 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 133 140 120 120 120 248 376), lower := (rows 259 67 133 140 16 32 64 128 256), losses := [] }

theorem u22707 : Upper (D 8) (R 8) [258,65,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22708 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 133 168 124 124 124 252 380), lower := (rows 259 67 133 168 16 32 64 128 256), losses := [] }

theorem u22708 : Upper (D 8) (R 8) [258,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22709 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 133 200 60 60 124 188 316), lower := (rows 259 67 133 200 16 32 64 128 256), losses := [] }

theorem u22709 : Upper (D 8) (R 8) [258,65,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22710 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 140 140 113 113 113 241 369), lower := (rows 259 67 140 140 16 32 64 128 256), losses := [] }

theorem u22710 : Upper (D 8) (R 8) [258,65,136,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22711 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 140 152 117 101 101 229 357), lower := (rows 259 67 140 152 16 32 64 128 256), losses := [] }

theorem u22711 : Upper (D 8) (R 8) [258,65,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22712 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 140 168 117 117 117 245 373), lower := (rows 259 67 140 168 16 32 64 128 256), losses := [] }

theorem u22712 : Upper (D 8) (R 8) [258,65,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22713 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 140 200 53 53 117 181 309), lower := (rows 259 67 140 200 16 32 64 128 256), losses := [] }

theorem u22713 : Upper (D 8) (R 8) [258,65,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22714_5 : Upper (D 8) (R 8) [258,65,144,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16471

theorem m22714_9 : Upper (D 8) (R 8) [258,65,144,160,9] 13 :=
  permutation_upper _ _ _ [258,65,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16479

theorem m22714_12 : Upper (D 8) (R 8) [258,65,144,160,12] 13 :=
  permutation_upper _ _ _ [258,65,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16503

theorem m22714_33 : Upper (D 8) (R 8) [258,65,144,160,33] 13 :=
  permutation_upper _ _ _ [258,65,33,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16523

theorem m22714_36 : Upper (D 8) (R 8) [258,65,144,160,36] 13 :=
  permutation_upper _ _ _ [258,65,40,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16550

theorem m22714_40 : Upper (D 8) (R 8) [258,65,144,160,40] 13 :=
  permutation_upper _ _ _ [258,65,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16561

theorem m22714_65 : Upper (D 8) (R 8) [258,65,144,160,65] 13 :=
  permutation_upper _ _ _ [258,65,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16567

theorem m22714_68 : Upper (D 8) (R 8) [258,65,144,160,68] 13 :=
  permutation_upper _ _ _ [258,65,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16570

theorem m22714_72 : Upper (D 8) (R 8) [258,65,144,160,72] 13 :=
  permutation_upper _ _ _ [258,65,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16575

theorem m22714_96 : Upper (D 8) (R 8) [258,65,144,160,96] 13 :=
  permutation_upper _ _ _ [258,65,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16581

def r22714 : Route 9 := (fun mask => (mask,id))

def c22714 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u22714 : Upper (D 8) (R 8) [258,65,144,160] 13 := by
  apply FastRouting.sound _ _ [258,65,144,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r22714 c22714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22714_5
  · exact m22714_9
  · exact m22714_12
  · exact m22714_33
  · exact m22714_36
  · exact m22714_40
  · exact m22714_65
  · exact m22714_68
  · exact m22714_72
  · exact m22714_96

theorem m22715_5 : Upper (D 8) (R 8) [258,65,144,192,5] 13 :=
  permutation_upper _ _ _ [258,65,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16472

theorem m22715_9 : Upper (D 8) (R 8) [258,65,144,192,9] 13 :=
  permutation_upper _ _ _ [258,65,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16482

theorem m22715_12 : Upper (D 8) (R 8) [258,65,144,192,12] 13 :=
  permutation_upper _ _ _ [258,65,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16504

theorem m22715_33 : Upper (D 8) (R 8) [258,65,144,192,33] 13 :=
  permutation_upper _ _ _ [258,65,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16524

theorem m22715_36 : Upper (D 8) (R 8) [258,65,144,192,36] 13 :=
  permutation_upper _ _ _ [258,65,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16551

theorem m22715_40 : Upper (D 8) (R 8) [258,65,144,192,40] 13 :=
  permutation_upper _ _ _ [258,65,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16565

def r22715 : Route 9 := (fun mask => (mask,id))

def c22715 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22715 : Upper (D 8) (R 8) [258,65,144,192] 13 := by
  apply FastRouting.sound _ _ [258,65,144,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22715 c22715
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22715_5
  · exact m22715_9
  · exact m22715_12
  · exact m22715_33
  · exact m22715_36
  · exact m22715_40

def b22716 : PairBound 9 := { available := 125, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 164 168 125 125 125 253 381), lower := (rows 259 67 164 168 16 32 64 128 256), losses := [] }

theorem u22716 : Upper (D 8) (R 8) [258,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22717_5 : Upper (D 8) (R 8) [258,65,160,192,5] 13 :=
  permutation_upper _ _ _ [258,65,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16480

theorem m22717_9 : Upper (D 8) (R 8) [258,65,160,192,9] 13 :=
  permutation_upper _ _ _ [258,65,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16483

theorem m22717_12 : Upper (D 8) (R 8) [258,65,160,192,12] 13 :=
  permutation_upper _ _ _ [258,65,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16506

theorem m22717_33 : Upper (D 8) (R 8) [258,65,160,192,33] 13 :=
  permutation_upper _ _ _ [258,65,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16525

theorem m22717_36 : Upper (D 8) (R 8) [258,65,160,192,36] 13 :=
  permutation_upper _ _ _ [258,65,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16563

theorem m22717_40 : Upper (D 8) (R 8) [258,65,160,192,40] 13 :=
  permutation_upper _ _ _ [258,65,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16566

def r22717 : Route 9 := (fun mask => (mask,id))

def c22717 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22717 : Upper (D 8) (R 8) [258,65,160,192] 13 := by
  apply FastRouting.sound _ _ [258,65,160,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22717 c22717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22717_5
  · exact m22717_9
  · exact m22717_12
  · exact m22717_33
  · exact m22717_36
  · exact m22717_40

def b22718 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 70 13 25 240 224 224 224 480), lower := (rows 259 70 13 25 16 32 64 128 256), losses := [] }

theorem u22718 : Upper (D 8) (R 8) [258,68,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22719 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 70 13 41 240 240 240 240 496), lower := (rows 259 70 13 41 16 32 64 128 256), losses := [] }

theorem u22719 : Upper (D 8) (R 8) [258,68,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22720 : Route 9 := (fun mask => (mask,id))

def c22720 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22720 : Upper (D 8) (R 8) [258,68,9,48] 13 := by
  apply FastRouting.sound _ _ [258,68,9,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22720 c22720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16585
  · exact u16586
  · exact u16587
  · exact u16588
  · exact u16589
  · exact u16590

def b22721 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 259 70 13 73 176 176 240 176 432), lower := (rows 259 70 13 73 16 32 64 128 256), losses := [] }

theorem u22721 : Upper (D 8) (R 8) [258,68,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22722 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 13 88 177 161 225 161 417), lower := (rows 259 70 13 88 16 32 64 128 256), losses := [] }

theorem u22722 : Upper (D 8) (R 8) [258,68,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22723 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 13 104 177 177 241 177 433), lower := (rows 259 70 13 104 16 32 64 128 256), losses := [] }

theorem u22723 : Upper (D 8) (R 8) [258,68,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22724 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 70 13 137 240 240 240 240 496), lower := (rows 259 70 13 137 16 32 64 128 256), losses := [] }

theorem u22724 : Upper (D 8) (R 8) [258,68,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22725 : Route 9 := (fun mask => (mask,id))

def c22725 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22725 : Upper (D 8) (R 8) [258,68,9,144] 13 := by
  apply FastRouting.sound _ _ [258,68,9,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22725 c22725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16591
  · exact u16592
  · exact u16593
  · exact u16594
  · exact u16595
  · exact u16596

def r22726 : Route 9 := (fun mask => (mask,id))

def c22726 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22726 : Upper (D 8) (R 8) [258,68,9,160] 13 := by
  apply FastRouting.sound _ _ [258,68,9,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22726 c22726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16597
  · exact u16598
  · exact u16599
  · exact u16600
  · exact u16601
  · exact u16602

def b22727 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 13 200 177 177 241 177 433), lower := (rows 259 70 13 200 16 32 64 128 256), losses := [] }

theorem u22727 : Upper (D 8) (R 8) [258,68,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22728 : Route 9 := (fun mask => (mask,id))

def c22728 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22728 : Upper (D 8) (R 8) [258,68,24,33] 13 := by
  apply FastRouting.sound _ _ [258,68,24,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22728 c22728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16603
  · exact u16604
  · exact u16605
  · exact u16606
  · exact u16607
  · exact u16608

def b22729 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 73 177 161 225 161 417), lower := (rows 259 70 28 73 16 32 64 128 256), losses := [] }

theorem u22729 : Upper (D 8) (R 8) [258,68,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22730 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 104 177 161 225 161 417), lower := (rows 259 70 28 104 16 32 64 128 256), losses := [] }

theorem u22730 : Upper (D 8) (R 8) [258,68,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22731_33 : Upper (D 8) (R 8) [258,68,24,129,33] 13 :=
  permutation_upper _ _ _ [258,68,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16606

theorem m22731_65 : Upper (D 8) (R 8) [258,68,24,129,65] 13 :=
  permutation_upper _ _ _ [258,68,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16609

theorem m22731_96 : Upper (D 8) (R 8) [258,68,24,129,96] 13 :=
  permutation_upper _ _ _ [258,68,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16611

def r22731 : Route 9 := (fun mask => (mask,id))

def c22731 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22731 : Upper (D 8) (R 8) [258,68,24,129] 13 := by
  apply FastRouting.sound _ _ [258,68,24,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22731 c22731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22731_33
  · exact m22731_65
  · exact m22731_96
  · exact u16613
  · exact u16614
  · exact u16615

theorem m22732_33 : Upper (D 8) (R 8) [258,68,24,160,33] 13 :=
  permutation_upper _ _ _ [258,68,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16607

theorem m22732_65 : Upper (D 8) (R 8) [258,68,24,160,65] 13 :=
  permutation_upper _ _ _ [258,68,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16610

theorem m22732_96 : Upper (D 8) (R 8) [258,68,24,160,96] 13 :=
  permutation_upper _ _ _ [258,68,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16612

theorem m22732_129 : Upper (D 8) (R 8) [258,68,24,160,129] 13 :=
  permutation_upper _ _ _ [258,68,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16614

def r22732 : Route 9 := (fun mask => (mask,id))

def c22732 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22732 : Upper (D 8) (R 8) [258,68,24,160] 13 := by
  apply FastRouting.sound _ _ [258,68,24,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22732 c22732
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22732_33
  · exact m22732_65
  · exact m22732_96
  · exact m22732_129
  · exact u16616
  · exact u16617

def b22733 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 200 177 161 225 161 417), lower := (rows 259 70 28 200 16 32 64 128 256), losses := [] }

theorem u22733 : Upper (D 8) (R 8) [258,68,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22734 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 25 248 232 232 232 488), lower := (rows 259 70 37 25 16 32 64 128 256), losses := [] }

theorem u22734 : Upper (D 8) (R 8) [258,68,33,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22735 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 248 248 248 248 504), lower := (rows 259 70 37 41 16 32 64 128 256), losses := [] }

theorem u22735 : Upper (D 8) (R 8) [258,68,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22736_9 : Upper (D 8) (R 8) [258,68,33,48,9] 13 :=
  permutation_upper _ _ _ [258,68,33,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16618

theorem m22736_33 : Upper (D 8) (R 8) [258,68,33,48,33] 13 :=
  permutation_upper _ _ _ [258,68,33,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16624

def r22736 : Route 9 := (fun mask => (mask,id))

def c22736 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22736 : Upper (D 8) (R 8) [258,68,33,48] 13 := by
  apply FastRouting.sound _ _ [258,68,33,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22736 c22736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22736_9
  · exact m22736_33
  · exact u16630
  · exact u16631
  · exact u16632
  · exact u16633
  · exact u16634
  · exact u16635
  · exact u16636
  · exact u16637

def b22737 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 37 73 184 184 248 184 440), lower := (rows 259 70 37 73 16 32 64 128 256), losses := [] }

theorem u22737 : Upper (D 8) (R 8) [258,68,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22738_9 : Upper (D 8) (R 8) [258,68,33,80,9] 13 :=
  permutation_upper _ _ _ [258,68,33,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16619

theorem m22738_33 : Upper (D 8) (R 8) [258,68,33,80,33] 13 :=
  permutation_upper _ _ _ [258,68,33,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16625

theorem m22738_40 : Upper (D 8) (R 8) [258,68,33,80,40] 13 :=
  permutation_upper _ _ _ [258,68,33,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16632

def r22738 : Route 9 := (fun mask => (mask,id))

def c22738 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22738 : Upper (D 8) (R 8) [258,68,33,80] 13 := by
  apply FastRouting.sound _ _ [258,68,33,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22738 c22738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22738_9
  · exact m22738_33
  · exact m22738_40
  · exact u16640
  · exact u16641
  · exact u16642

theorem m22739_9 : Upper (D 8) (R 8) [258,68,33,96,9] 13 :=
  permutation_upper _ _ _ [258,68,33,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16620

theorem m22739_33 : Upper (D 8) (R 8) [258,68,33,96,33] 13 :=
  permutation_upper _ _ _ [258,68,33,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16626

theorem m22739_40 : Upper (D 8) (R 8) [258,68,33,96,40] 13 :=
  permutation_upper _ _ _ [258,68,33,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16633

def r22739 : Route 9 := (fun mask => (mask,id))

def c22739 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22739 : Upper (D 8) (R 8) [258,68,33,96] 13 := by
  apply FastRouting.sound _ _ [258,68,33,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22739 c22739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22739_9
  · exact m22739_33
  · exact m22739_40
  · exact u16643
  · exact u16644
  · exact u16645

#print axioms u22739
end Delivery.IrregularNine14.P08
