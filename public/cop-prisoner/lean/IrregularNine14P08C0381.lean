import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0280
import IrregularNine14P08C0281
import IrregularNine14P08C0282
import IrregularNine14P08C0283
import IrregularNine14P08C0284

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m22860_5 : Upper (D 8) (R 8) [258,96,129,192,5] 13 :=
  permutation_upper _ _ _ [258,96,9,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16805

theorem m22860_9 : Upper (D 8) (R 8) [258,96,129,192,9] 13 :=
  permutation_upper _ _ _ [258,96,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16832

theorem m22860_12 : Upper (D 8) (R 8) [258,96,129,192,12] 13 :=
  permutation_upper _ _ _ [258,96,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16860

theorem m22860_33 : Upper (D 8) (R 8) [258,96,129,192,33] 13 :=
  permutation_upper _ _ _ [258,96,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16895

theorem m22860_36 : Upper (D 8) (R 8) [258,96,129,192,36] 13 :=
  permutation_upper _ _ _ [258,96,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16925

theorem m22860_40 : Upper (D 8) (R 8) [258,96,129,192,40] 13 :=
  permutation_upper _ _ _ [258,96,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16942

def r22860 : Route 9 := (fun mask => (mask,id))

def c22860 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22860 : Upper (D 8) (R 8) [258,96,129,192] 13 := by
  apply FastRouting.sound _ _ [258,96,129,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22860 c22860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22860_5
  · exact m22860_9
  · exact m22860_12
  · exact m22860_33
  · exact m22860_36
  · exact m22860_40

def b22861 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 140 140 113 113 113 241 369), lower := (rows 259 98 140 140 16 32 64 128 256), losses := [] }

theorem u22861 : Upper (D 8) (R 8) [258,96,136,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22862 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 140 152 117 101 101 229 357), lower := (rows 259 98 140 152 16 32 64 128 256), losses := [] }

theorem u22862 : Upper (D 8) (R 8) [258,96,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22863 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 140 168 117 117 117 245 373), lower := (rows 259 98 140 168 16 32 64 128 256), losses := [] }

theorem u22863 : Upper (D 8) (R 8) [258,96,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22864 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 140 200 53 53 117 181 309), lower := (rows 259 98 140 200 16 32 64 128 256), losses := [] }

theorem u22864 : Upper (D 8) (R 8) [258,96,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22865_5 : Upper (D 8) (R 8) [258,96,144,160,5] 13 :=
  permutation_upper _ _ _ [258,96,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16810

theorem m22865_9 : Upper (D 8) (R 8) [258,96,144,160,9] 13 :=
  permutation_upper _ _ _ [258,96,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16827

theorem m22865_12 : Upper (D 8) (R 8) [258,96,144,160,12] 13 :=
  permutation_upper _ _ _ [258,96,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16861

theorem m22865_33 : Upper (D 8) (R 8) [258,96,144,160,33] 13 :=
  permutation_upper _ _ _ [258,96,33,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16897

theorem m22865_36 : Upper (D 8) (R 8) [258,96,144,160,36] 13 :=
  permutation_upper _ _ _ [258,96,40,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16929

theorem m22865_40 : Upper (D 8) (R 8) [258,96,144,160,40] 13 :=
  permutation_upper _ _ _ [258,96,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16940

theorem m22865_65 : Upper (D 8) (R 8) [258,96,144,160,65] 13 :=
  permutation_upper _ _ _ [258,96,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16947

theorem m22865_68 : Upper (D 8) (R 8) [258,96,144,160,68] 13 :=
  permutation_upper _ _ _ [258,96,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16952

theorem m22865_72 : Upper (D 8) (R 8) [258,96,144,160,72] 13 :=
  permutation_upper _ _ _ [258,96,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16957

theorem m22865_96 : Upper (D 8) (R 8) [258,96,144,160,96] 13 :=
  permutation_upper _ _ _ [258,96,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16961

def r22865 : Route 9 := (fun mask => (mask,id))

def c22865 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u22865 : Upper (D 8) (R 8) [258,96,144,160] 13 := by
  apply FastRouting.sound _ _ [258,96,144,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r22865 c22865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22865_5
  · exact m22865_9
  · exact m22865_12
  · exact m22865_33
  · exact m22865_36
  · exact m22865_40
  · exact m22865_65
  · exact m22865_68
  · exact m22865_72
  · exact m22865_96

theorem m22866_5 : Upper (D 8) (R 8) [258,96,144,192,5] 13 :=
  permutation_upper _ _ _ [258,96,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16811

theorem m22866_9 : Upper (D 8) (R 8) [258,96,144,192,9] 13 :=
  permutation_upper _ _ _ [258,96,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16833

theorem m22866_12 : Upper (D 8) (R 8) [258,96,144,192,12] 13 :=
  permutation_upper _ _ _ [258,96,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16862

theorem m22866_33 : Upper (D 8) (R 8) [258,96,144,192,33] 13 :=
  permutation_upper _ _ _ [258,96,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16898

theorem m22866_36 : Upper (D 8) (R 8) [258,96,144,192,36] 13 :=
  permutation_upper _ _ _ [258,96,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16930

theorem m22866_40 : Upper (D 8) (R 8) [258,96,144,192,40] 13 :=
  permutation_upper _ _ _ [258,96,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16943

def r22866 : Route 9 := (fun mask => (mask,id))

def c22866 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22866 : Upper (D 8) (R 8) [258,96,144,192] 13 := by
  apply FastRouting.sound _ _ [258,96,144,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22866 c22866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22866_5
  · exact m22866_9
  · exact m22866_12
  · exact m22866_33
  · exact m22866_36
  · exact m22866_40

def b22867 : PairBound 9 := { available := 93, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 164 168 93 125 93 221 349), lower := (rows 259 98 164 168 16 32 64 128 256), losses := [] }

theorem u22867 : Upper (D 8) (R 8) [258,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22868_5 : Upper (D 8) (R 8) [258,96,160,192,5] 13 :=
  permutation_upper _ _ _ [258,96,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16829

theorem m22868_9 : Upper (D 8) (R 8) [258,96,160,192,9] 13 :=
  permutation_upper _ _ _ [258,96,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16834

theorem m22868_12 : Upper (D 8) (R 8) [258,96,160,192,12] 13 :=
  permutation_upper _ _ _ [258,96,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16864

theorem m22868_33 : Upper (D 8) (R 8) [258,96,160,192,33] 13 :=
  permutation_upper _ _ _ [258,96,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16902

theorem m22868_36 : Upper (D 8) (R 8) [258,96,160,192,36] 13 :=
  permutation_upper _ _ _ [258,96,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16941

theorem m22868_40 : Upper (D 8) (R 8) [258,96,160,192,40] 13 :=
  permutation_upper _ _ _ [258,96,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16944

def r22868 : Route 9 := (fun mask => (mask,id))

def c22868 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22868 : Upper (D 8) (R 8) [258,96,160,192] 13 := by
  apply FastRouting.sound _ _ [258,96,160,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22868 c22868
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22868_5
  · exact m22868_9
  · exact m22868_12
  · exact m22868_33
  · exact m22868_36
  · exact m22868_40

def b22869 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 13 240 240 240 240 496), lower := (rows 259 194 13 13 16 32 64 128 256), losses := [] }

theorem u22869 : Upper (D 8) (R 8) [258,192,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22870 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 25 244 228 228 228 484), lower := (rows 259 194 13 25 16 32 64 128 256), losses := [] }

theorem u22870 : Upper (D 8) (R 8) [258,192,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22871 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22871 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22871 : Upper (D 8) (R 8) [258,192,9,20] 13 := by
  apply FastRouting.sound _ _ [258,192,9,20] 13 (by decide) (choices 2) [33,65,96,192] r22871 c22871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16966
  · exact u16967
  · exact u16968
  · exact u16969

def b22872 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 41 244 244 244 244 500), lower := (rows 259 194 13 41 16 32 64 128 256), losses := [] }

theorem u22872 : Upper (D 8) (R 8) [258,192,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22873 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22873 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22873 : Upper (D 8) (R 8) [258,192,9,36] 13 := by
  apply FastRouting.sound _ _ [258,192,9,36] 13 (by decide) (choices 2) [33,65,96,192] r22873 c22873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16973
  · exact u16974
  · exact u16975
  · exact u16976

theorem m22874_5 : Upper (D 8) (R 8) [258,192,9,48,5] 13 :=
  permutation_upper _ _ _ [258,192,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16963

def r22874 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22874 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22874 : Upper (D 8) (R 8) [258,192,9,48] 13 := by
  apply FastRouting.sound _ _ [258,192,9,48] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r22874 c22874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22874_5
  · exact u16977
  · exact u16978
  · exact u16979
  · exact u16980
  · exact u16981
  · exact u16982

def b22875 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 73 180 180 244 180 436), lower := (rows 259 194 13 73 16 32 64 128 256), losses := [] }

theorem u22875 : Upper (D 8) (R 8) [258,192,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22876 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 76 177 177 241 177 433), lower := (rows 259 194 13 76 16 32 64 128 256), losses := [] }

theorem u22876 : Upper (D 8) (R 8) [258,192,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22877 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 88 181 165 229 165 421), lower := (rows 259 194 13 88 16 32 64 128 256), losses := [] }

theorem u22877 : Upper (D 8) (R 8) [258,192,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22878 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 104 181 181 245 181 437), lower := (rows 259 194 13 104 16 32 64 128 256), losses := [] }

theorem u22878 : Upper (D 8) (R 8) [258,192,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22879 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 13 200 53 53 117 181 309), lower := (rows 259 194 13 200 16 32 64 128 256), losses := [] }

theorem u22879 : Upper (D 8) (R 8) [258,192,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22880_12 : Upper (D 8) (R 8) [258,192,17,33,12] 13 :=
  permutation_upper _ _ _ [258,192,9,20,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16966

theorem m22880_36 : Upper (D 8) (R 8) [258,192,17,33,36] 13 :=
  permutation_upper _ _ _ [258,192,9,36,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16973

theorem m22880_40 : Upper (D 8) (R 8) [258,192,17,33,40] 13 :=
  permutation_upper _ _ _ [258,192,9,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16977

theorem m22880_68 : Upper (D 8) (R 8) [258,192,17,33,68] 13 :=
  permutation_upper _ _ _ [258,192,9,68,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16986

theorem m22880_72 : Upper (D 8) (R 8) [258,192,17,33,72] 13 :=
  permutation_upper _ _ _ [258,192,9,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16988

theorem m22880_96 : Upper (D 8) (R 8) [258,192,17,33,96] 13 :=
  permutation_upper _ _ _ [258,192,9,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16992

theorem m22880_192 : Upper (D 8) (R 8) [258,192,17,33,192] 13 :=
  permutation_upper _ _ _ [258,192,9,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16996

def r22880 : Route 9 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22880 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22880 : Upper (D 8) (R 8) [258,192,17,33] 13 := by
  apply FastRouting.sound _ _ [258,192,17,33] 13 (by decide) (choices 2) [12,36,40,68,72,96,192] r22880 c22880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22880_12
  · exact m22880_36
  · exact m22880_40
  · exact m22880_68
  · exact m22880_72
  · exact m22880_96
  · exact m22880_192

theorem m22881_9 : Upper (D 8) (R 8) [258,192,17,36,9] 13 :=
  permutation_upper _ _ _ [258,192,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16963

theorem m22881_33 : Upper (D 8) (R 8) [258,192,17,36,33] 13 :=
  permutation_upper _ _ _ [258,192,9,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16970

theorem m22881_40 : Upper (D 8) (R 8) [258,192,17,36,40] 13 :=
  permutation_upper _ _ _ [258,192,9,48,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16978

theorem m22881_65 : Upper (D 8) (R 8) [258,192,17,36,65] 13 :=
  permutation_upper _ _ _ [258,192,9,65,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16983

theorem m22881_72 : Upper (D 8) (R 8) [258,192,17,36,72] 13 :=
  permutation_upper _ _ _ [258,192,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16989

theorem m22881_96 : Upper (D 8) (R 8) [258,192,17,36,96] 13 :=
  permutation_upper _ _ _ [258,192,9,96,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16993

theorem m22881_192 : Upper (D 8) (R 8) [258,192,17,36,192] 13 :=
  permutation_upper _ _ _ [258,192,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16997

def r22881 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22881 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22881 : Upper (D 8) (R 8) [258,192,17,36] 13 := by
  apply FastRouting.sound _ _ [258,192,17,36] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22881 c22881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22881_9
  · exact m22881_33
  · exact m22881_40
  · exact m22881_65
  · exact m22881_72
  · exact m22881_96
  · exact m22881_192

theorem m22882_9 : Upper (D 8) (R 8) [258,192,17,68,9] 13 :=
  permutation_upper _ _ _ [258,192,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16964

theorem m22882_33 : Upper (D 8) (R 8) [258,192,17,68,33] 13 :=
  permutation_upper _ _ _ [258,192,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16971

theorem m22882_40 : Upper (D 8) (R 8) [258,192,17,68,40] 13 :=
  permutation_upper _ _ _ [258,192,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16980

theorem m22882_129 : Upper (D 8) (R 8) [258,192,17,68,129] 13 :=
  permutation_upper _ _ _ [258,192,9,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16984

theorem m22882_136 : Upper (D 8) (R 8) [258,192,17,68,136] 13 :=
  permutation_upper _ _ _ [258,192,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16990

theorem m22882_160 : Upper (D 8) (R 8) [258,192,17,68,160] 13 :=
  permutation_upper _ _ _ [258,192,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16994

def r22882 : Route 9 := (fun mask => (mask,id))

def c22882 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22882 : Upper (D 8) (R 8) [258,192,17,68] 13 := by
  apply FastRouting.sound _ _ [258,192,17,68] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22882 c22882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22882_9
  · exact m22882_33
  · exact m22882_40
  · exact m22882_129
  · exact m22882_136
  · exact m22882_160

theorem m22883_5 : Upper (D 8) (R 8) [258,192,17,96,5] 13 :=
  permutation_upper _ _ _ [258,192,9,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16962

theorem m22883_9 : Upper (D 8) (R 8) [258,192,17,96,9] 13 :=
  permutation_upper _ _ _ [258,192,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16965

theorem m22883_12 : Upper (D 8) (R 8) [258,192,17,96,12] 13 :=
  permutation_upper _ _ _ [258,192,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16968

theorem m22883_33 : Upper (D 8) (R 8) [258,192,17,96,33] 13 :=
  permutation_upper _ _ _ [258,192,9,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16972

theorem m22883_36 : Upper (D 8) (R 8) [258,192,17,96,36] 13 :=
  permutation_upper _ _ _ [258,192,9,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16975

theorem m22883_40 : Upper (D 8) (R 8) [258,192,17,96,40] 13 :=
  permutation_upper _ _ _ [258,192,9,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16981

theorem m22883_129 : Upper (D 8) (R 8) [258,192,17,96,129] 13 :=
  permutation_upper _ _ _ [258,192,9,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16985

theorem m22883_132 : Upper (D 8) (R 8) [258,192,17,96,132] 13 :=
  permutation_upper _ _ _ [258,192,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16987

theorem m22883_136 : Upper (D 8) (R 8) [258,192,17,96,136] 13 :=
  permutation_upper _ _ _ [258,192,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16991

theorem m22883_160 : Upper (D 8) (R 8) [258,192,17,96,160] 13 :=
  permutation_upper _ _ _ [258,192,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16995

def r22883 : Route 9 := (fun mask => (mask,id))

def c22883 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22883 : Upper (D 8) (R 8) [258,192,17,96] 13 := by
  apply FastRouting.sound _ _ [258,192,17,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22883 c22883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22883_5
  · exact m22883_9
  · exact m22883_12
  · exact m22883_33
  · exact m22883_36
  · exact m22883_40
  · exact m22883_129
  · exact m22883_132
  · exact m22883_136
  · exact m22883_160

theorem m22884_5 : Upper (D 8) (R 8) [258,192,24,33,5] 13 :=
  permutation_upper _ _ _ [258,192,9,20,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16966

def r22884 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22884 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22884 : Upper (D 8) (R 8) [258,192,24,33] 13 := by
  apply FastRouting.sound _ _ [258,192,24,33] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r22884 c22884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22884_5
  · exact u16998
  · exact u16999
  · exact u17000
  · exact u17001
  · exact u17002
  · exact u17003

theorem m22885_33 : Upper (D 8) (R 8) [258,192,24,36,33] 13 :=
  permutation_upper _ _ _ [258,192,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16999

def r22885 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22885 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22885 : Upper (D 8) (R 8) [258,192,24,36] 13 := by
  apply FastRouting.sound _ _ [258,192,24,36] 13 (by decide) (choices 2) [33,65,96,192] r22885 c22885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22885_33
  · exact u17004
  · exact u17005
  · exact u17006

def b22886 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 28 73 181 165 229 165 421), lower := (rows 259 194 28 73 16 32 64 128 256), losses := [] }

theorem u22886 : Upper (D 8) (R 8) [258,192,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22887 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 28 76 177 161 225 161 417), lower := (rows 259 194 28 76 16 32 64 128 256), losses := [] }

theorem u22887 : Upper (D 8) (R 8) [258,192,24,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22888_5 : Upper (D 8) (R 8) [258,192,24,96,5] 13 :=
  permutation_upper _ _ _ [258,192,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16968

theorem m22888_33 : Upper (D 8) (R 8) [258,192,24,96,33] 13 :=
  permutation_upper _ _ _ [258,192,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17002

theorem m22888_36 : Upper (D 8) (R 8) [258,192,24,96,36] 13 :=
  permutation_upper _ _ _ [258,192,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17005

theorem m22888_129 : Upper (D 8) (R 8) [258,192,24,96,129] 13 :=
  permutation_upper _ _ _ [258,192,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17007

theorem m22888_132 : Upper (D 8) (R 8) [258,192,24,96,132] 13 :=
  permutation_upper _ _ _ [258,192,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17008

def r22888 : Route 9 := (fun mask => (mask,id))

def c22888 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22888 : Upper (D 8) (R 8) [258,192,24,96] 13 := by
  apply FastRouting.sound _ _ [258,192,24,96] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22888 c22888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22888_5
  · exact m22888_33
  · exact m22888_36
  · exact m22888_129
  · exact m22888_132
  · exact u17009

def b22889 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 28 200 53 37 101 165 293), lower := (rows 259 194 28 200 16 32 64 128 256), losses := [] }

theorem u22889 : Upper (D 8) (R 8) [258,192,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22890 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 194 37 41 252 252 252 252 508), lower := (rows 259 194 37 41 16 32 64 128 256), losses := [] }

theorem u22890 : Upper (D 8) (R 8) [258,192,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22891 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 44 249 249 249 249 505), lower := (rows 259 194 37 44 16 32 64 128 256), losses := [] }

theorem u22891 : Upper (D 8) (R 8) [258,192,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22892_5 : Upper (D 8) (R 8) [258,192,33,48,5] 13 :=
  permutation_upper _ _ _ [258,192,9,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16970

theorem m22892_9 : Upper (D 8) (R 8) [258,192,33,48,9] 13 :=
  permutation_upper _ _ _ [258,192,9,36,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16973

theorem m22892_12 : Upper (D 8) (R 8) [258,192,33,48,12] 13 :=
  permutation_upper _ _ _ [258,192,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16999

theorem m22892_33 : Upper (D 8) (R 8) [258,192,33,48,33] 13 :=
  permutation_upper _ _ _ [258,192,33,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17010

theorem m22892_36 : Upper (D 8) (R 8) [258,192,33,48,36] 13 :=
  permutation_upper _ _ _ [258,192,33,36,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17013

def r22892 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22892 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22892 : Upper (D 8) (R 8) [258,192,33,48] 13 := by
  apply FastRouting.sound _ _ [258,192,33,48] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,192] r22892 c22892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22892_5
  · exact m22892_9
  · exact m22892_12
  · exact m22892_33
  · exact m22892_36
  · exact u17016
  · exact u17017
  · exact u17018
  · exact u17019
  · exact u17020
  · exact u17021

def b22893 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 37 73 188 188 252 188 444), lower := (rows 259 194 37 73 16 32 64 128 256), losses := [] }

theorem u22893 : Upper (D 8) (R 8) [258,192,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22894_9 : Upper (D 8) (R 8) [258,192,33,68,9] 13 :=
  permutation_upper _ _ _ [258,192,9,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16988

theorem m22894_33 : Upper (D 8) (R 8) [258,192,33,68,33] 13 :=
  permutation_upper _ _ _ [258,192,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17011

theorem m22894_40 : Upper (D 8) (R 8) [258,192,33,68,40] 13 :=
  permutation_upper _ _ _ [258,192,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17018

theorem m22894_129 : Upper (D 8) (R 8) [258,192,33,68,129] 13 :=
  permutation_upper _ _ _ [258,192,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17022

def r22894 : Route 9 := (fun mask => (mask,id))

def c22894 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22894 : Upper (D 8) (R 8) [258,192,33,68] 13 := by
  apply FastRouting.sound _ _ [258,192,33,68] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22894 c22894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22894_9
  · exact m22894_33
  · exact m22894_40
  · exact m22894_129
  · exact u17025
  · exact u17026

theorem m22895_5 : Upper (D 8) (R 8) [258,192,33,80,5] 13 :=
  permutation_upper _ _ _ [258,192,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16971

theorem m22895_9 : Upper (D 8) (R 8) [258,192,33,80,9] 13 :=
  permutation_upper _ _ _ [258,192,9,68,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16986

theorem m22895_12 : Upper (D 8) (R 8) [258,192,33,80,12] 13 :=
  permutation_upper _ _ _ [258,192,24,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17001

theorem m22895_33 : Upper (D 8) (R 8) [258,192,33,80,33] 13 :=
  permutation_upper _ _ _ [258,192,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17011

theorem m22895_36 : Upper (D 8) (R 8) [258,192,33,80,36] 13 :=
  permutation_upper _ _ _ [258,192,33,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17014

theorem m22895_40 : Upper (D 8) (R 8) [258,192,33,80,40] 13 :=
  permutation_upper _ _ _ [258,192,33,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17019

theorem m22895_129 : Upper (D 8) (R 8) [258,192,33,80,129] 13 :=
  permutation_upper _ _ _ [258,192,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17023

theorem m22895_132 : Upper (D 8) (R 8) [258,192,33,80,132] 13 :=
  permutation_upper _ _ _ [258,192,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17025

def r22895 : Route 9 := (fun mask => (mask,id))

def c22895 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22895 : Upper (D 8) (R 8) [258,192,33,80] 13 := by
  apply FastRouting.sound _ _ [258,192,33,80] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22895 c22895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22895_5
  · exact m22895_9
  · exact m22895_12
  · exact m22895_33
  · exact m22895_36
  · exact m22895_40
  · exact m22895_129
  · exact m22895_132
  · exact u17027
  · exact u17028

theorem m22896_5 : Upper (D 8) (R 8) [258,192,33,96,5] 13 :=
  permutation_upper _ _ _ [258,192,9,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16972

theorem m22896_9 : Upper (D 8) (R 8) [258,192,33,96,9] 13 :=
  permutation_upper _ _ _ [258,192,9,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16992

theorem m22896_12 : Upper (D 8) (R 8) [258,192,33,96,12] 13 :=
  permutation_upper _ _ _ [258,192,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17002

theorem m22896_33 : Upper (D 8) (R 8) [258,192,33,96,33] 13 :=
  permutation_upper _ _ _ [258,192,33,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17012

theorem m22896_36 : Upper (D 8) (R 8) [258,192,33,96,36] 13 :=
  permutation_upper _ _ _ [258,192,33,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17015

theorem m22896_40 : Upper (D 8) (R 8) [258,192,33,96,40] 13 :=
  permutation_upper _ _ _ [258,192,33,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17020

theorem m22896_129 : Upper (D 8) (R 8) [258,192,33,96,129] 13 :=
  permutation_upper _ _ _ [258,192,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17024

theorem m22896_132 : Upper (D 8) (R 8) [258,192,33,96,132] 13 :=
  permutation_upper _ _ _ [258,192,33,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17026

theorem m22896_136 : Upper (D 8) (R 8) [258,192,33,96,136] 13 :=
  permutation_upper _ _ _ [258,192,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17028

def r22896 : Route 9 := (fun mask => (mask,id))

def c22896 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22896 : Upper (D 8) (R 8) [258,192,33,96] 13 := by
  apply FastRouting.sound _ _ [258,192,33,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22896 c22896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22896_5
  · exact m22896_9
  · exact m22896_12
  · exact m22896_33
  · exact m22896_36
  · exact m22896_40
  · exact m22896_129
  · exact m22896_132
  · exact m22896_136
  · exact u17029

def b22897 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 200 61 61 125 189 317), lower := (rows 259 194 37 200 16 32 64 128 256), losses := [] }

theorem u22897 : Upper (D 8) (R 8) [258,192,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22898 : PairBound 9 := { available := 241, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 44 241 241 241 241 497), lower := (rows 259 194 44 44 16 32 64 128 256), losses := [] }

theorem u22898 : Upper (D 8) (R 8) [258,192,40,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22899 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 56 245 229 229 229 485), lower := (rows 259 194 44 56 16 32 64 128 256), losses := [] }

theorem u22899 : Upper (D 8) (R 8) [258,192,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22900 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 44 73 181 181 245 181 437), lower := (rows 259 194 44 73 16 32 64 128 256), losses := [] }

theorem u22900 : Upper (D 8) (R 8) [258,192,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22901 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 44 76 177 177 241 177 433), lower := (rows 259 194 44 76 16 32 64 128 256), losses := [] }

theorem u22901 : Upper (D 8) (R 8) [258,192,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22902_5 : Upper (D 8) (R 8) [258,192,40,80,5] 13 :=
  permutation_upper _ _ _ [258,192,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16980

theorem m22902_33 : Upper (D 8) (R 8) [258,192,40,80,33] 13 :=
  permutation_upper _ _ _ [258,192,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17018

theorem m22902_36 : Upper (D 8) (R 8) [258,192,40,80,36] 13 :=
  permutation_upper _ _ _ [258,192,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17031

def r22902 : Route 9 := (fun mask => (mask,id))

def c22902 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22902 : Upper (D 8) (R 8) [258,192,40,80] 13 := by
  apply FastRouting.sound _ _ [258,192,40,80] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22902 c22902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22902_5
  · exact m22902_33
  · exact m22902_36
  · exact u17036
  · exact u17037
  · exact u17038

def b22903 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 104 181 181 245 181 437), lower := (rows 259 194 44 104 16 32 64 128 256), losses := [] }

theorem u22903 : Upper (D 8) (R 8) [258,192,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22904 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 44 200 53 53 117 181 309), lower := (rows 259 194 44 200 16 32 64 128 256), losses := [] }

theorem u22904 : Upper (D 8) (R 8) [258,192,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22905_9 : Upper (D 8) (R 8) [258,192,48,68,9] 13 :=
  permutation_upper _ _ _ [258,192,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16989

theorem m22905_33 : Upper (D 8) (R 8) [258,192,48,68,33] 13 :=
  permutation_upper _ _ _ [258,192,33,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17014

theorem m22905_40 : Upper (D 8) (R 8) [258,192,48,68,40] 13 :=
  permutation_upper _ _ _ [258,192,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17031

theorem m22905_129 : Upper (D 8) (R 8) [258,192,48,68,129] 13 :=
  permutation_upper _ _ _ [258,192,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17033

theorem m22905_136 : Upper (D 8) (R 8) [258,192,48,68,136] 13 :=
  permutation_upper _ _ _ [258,192,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17037

theorem m22905_160 : Upper (D 8) (R 8) [258,192,48,68,160] 13 :=
  permutation_upper _ _ _ [258,192,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17039

def r22905 : Route 9 := (fun mask => (mask,id))

def c22905 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22905 : Upper (D 8) (R 8) [258,192,48,68] 13 := by
  apply FastRouting.sound _ _ [258,192,48,68] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22905 c22905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22905_9
  · exact m22905_33
  · exact m22905_40
  · exact m22905_129
  · exact m22905_136
  · exact m22905_160

theorem m22906_5 : Upper (D 8) (R 8) [258,192,48,96,5] 13 :=
  permutation_upper _ _ _ [258,192,9,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16975

theorem m22906_9 : Upper (D 8) (R 8) [258,192,48,96,9] 13 :=
  permutation_upper _ _ _ [258,192,9,96,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16993

theorem m22906_12 : Upper (D 8) (R 8) [258,192,48,96,12] 13 :=
  permutation_upper _ _ _ [258,192,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17005

theorem m22906_33 : Upper (D 8) (R 8) [258,192,48,96,33] 13 :=
  permutation_upper _ _ _ [258,192,33,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17015

theorem m22906_36 : Upper (D 8) (R 8) [258,192,48,96,36] 13 :=
  permutation_upper _ _ _ [258,192,40,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17030

theorem m22906_40 : Upper (D 8) (R 8) [258,192,48,96,40] 13 :=
  permutation_upper _ _ _ [258,192,40,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17032

theorem m22906_129 : Upper (D 8) (R 8) [258,192,48,96,129] 13 :=
  permutation_upper _ _ _ [258,192,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17034

theorem m22906_132 : Upper (D 8) (R 8) [258,192,48,96,132] 13 :=
  permutation_upper _ _ _ [258,192,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17035

theorem m22906_136 : Upper (D 8) (R 8) [258,192,48,96,136] 13 :=
  permutation_upper _ _ _ [258,192,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17038

theorem m22906_160 : Upper (D 8) (R 8) [258,192,48,96,160] 13 :=
  permutation_upper _ _ _ [258,192,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17040

def r22906 : Route 9 := (fun mask => (mask,id))

def c22906 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22906 : Upper (D 8) (R 8) [258,192,48,96] 13 := by
  apply FastRouting.sound _ _ [258,192,48,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22906 c22906
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22906_5
  · exact m22906_9
  · exact m22906_12
  · exact m22906_33
  · exact m22906_36
  · exact m22906_40
  · exact m22906_129
  · exact m22906_132
  · exact m22906_136
  · exact m22906_160

def b22907 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 259 194 69 140 57 57 121 185 313), lower := (rows 259 194 69 140 16 32 64 128 256), losses := [] }

theorem u22907 : Upper (D 8) (R 8) [258,192,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22908 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 259 194 69 168 61 61 125 189 317), lower := (rows 259 194 69 168 16 32 64 128 256), losses := [] }

theorem u22908 : Upper (D 8) (R 8) [258,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22909 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 76 140 49 49 113 177 305), lower := (rows 259 194 76 140 16 32 64 128 256), losses := [] }

theorem u22909 : Upper (D 8) (R 8) [258,192,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22910_5 : Upper (D 8) (R 8) [258,192,72,144,5] 13 :=
  permutation_upper _ _ _ [258,192,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16990

theorem m22910_33 : Upper (D 8) (R 8) [258,192,72,144,33] 13 :=
  permutation_upper _ _ _ [258,192,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17025

theorem m22910_36 : Upper (D 8) (R 8) [258,192,72,144,36] 13 :=
  permutation_upper _ _ _ [258,192,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17037

def r22910 : Route 9 := (fun mask => (mask,id))

def c22910 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22910 : Upper (D 8) (R 8) [258,192,72,144] 13 := by
  apply FastRouting.sound _ _ [258,192,72,144] 13 (by decide) (choices 2) [5,33,36] r22910 c22910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22910_5
  · exact m22910_33
  · exact m22910_36

theorem m22911_5 : Upper (D 8) (R 8) [258,192,72,160,5] 13 :=
  permutation_upper _ _ _ [258,192,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16991

theorem m22911_33 : Upper (D 8) (R 8) [258,192,72,160,33] 13 :=
  permutation_upper _ _ _ [258,192,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17028

theorem m22911_36 : Upper (D 8) (R 8) [258,192,72,160,36] 13 :=
  permutation_upper _ _ _ [258,192,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17038

def r22911 : Route 9 := (fun mask => (mask,id))

def c22911 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22911 : Upper (D 8) (R 8) [258,192,72,160] 13 := by
  apply FastRouting.sound _ _ [258,192,72,160] 13 (by decide) (choices 2) [5,33,36] r22911 c22911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22911_5
  · exact m22911_33
  · exact m22911_36

theorem m22912_5 : Upper (D 8) (R 8) [258,192,80,160,5] 13 :=
  permutation_upper _ _ _ [258,192,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16987

theorem m22912_9 : Upper (D 8) (R 8) [258,192,80,160,9] 13 :=
  permutation_upper _ _ _ [258,192,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16994

theorem m22912_12 : Upper (D 8) (R 8) [258,192,80,160,12] 13 :=
  permutation_upper _ _ _ [258,192,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17008

theorem m22912_33 : Upper (D 8) (R 8) [258,192,80,160,33] 13 :=
  permutation_upper _ _ _ [258,192,33,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17026

theorem m22912_36 : Upper (D 8) (R 8) [258,192,80,160,36] 13 :=
  permutation_upper _ _ _ [258,192,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17035

theorem m22912_40 : Upper (D 8) (R 8) [258,192,80,160,40] 13 :=
  permutation_upper _ _ _ [258,192,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17039

def r22912 : Route 9 := (fun mask => (mask,id))

def c22912 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22912 : Upper (D 8) (R 8) [258,192,80,160] 13 := by
  apply FastRouting.sound _ _ [258,192,80,160] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22912 c22912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22912_5
  · exact m22912_9
  · exact m22912_12
  · exact m22912_33
  · exact m22912_36
  · exact m22912_40

theorem m22913_5 : Upper (D 8) (R 8) [258,192,96,160,5] 13 :=
  permutation_upper _ _ _ [258,192,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16995

theorem m22913_9 : Upper (D 8) (R 8) [258,192,96,160,9] 13 :=
  permutation_upper _ _ _ [258,192,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16995

theorem m22913_12 : Upper (D 8) (R 8) [258,192,96,160,12] 13 :=
  permutation_upper _ _ _ [258,192,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17009

theorem m22913_33 : Upper (D 8) (R 8) [258,192,96,160,33] 13 :=
  permutation_upper _ _ _ [258,192,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17029

theorem m22913_36 : Upper (D 8) (R 8) [258,192,96,160,36] 13 :=
  permutation_upper _ _ _ [258,192,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17040

theorem m22913_40 : Upper (D 8) (R 8) [258,192,96,160,40] 13 :=
  permutation_upper _ _ _ [258,192,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17040

def r22913 : Route 9 := (fun mask => (mask,id))

def c22913 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22913 : Upper (D 8) (R 8) [258,192,96,160] 13 := by
  apply FastRouting.sound _ _ [258,192,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40] r22913 c22913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22913_5
  · exact m22913_9
  · exact m22913_12
  · exact m22913_33
  · exact m22913_36
  · exact m22913_40

def b22914 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 104 248 248 248 248 504), lower := (rows 289 7 7 104 16 32 64 128 256), losses := [] }

theorem u22914 : Upper (D 8) (R 8) [288,5,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22915 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 200 248 248 248 248 504), lower := (rows 289 7 7 200 16 32 64 128 256), losses := [] }

theorem u22915 : Upper (D 8) (R 8) [288,5,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22916 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 26 240 224 224 224 480), lower := (rows 289 7 13 26 16 32 64 128 256), losses := [] }

theorem u22916 : Upper (D 8) (R 8) [288,5,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22917 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 42 240 240 240 240 496), lower := (rows 289 7 13 42 16 32 64 128 256), losses := [] }

theorem u22917 : Upper (D 8) (R 8) [288,5,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22918 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 240 240 240 240 496), lower := (rows 289 7 13 74 16 32 64 128 256), losses := [] }

theorem u22918 : Upper (D 8) (R 8) [288,5,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22919 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 242 242 242 242 498), lower := (rows 289 7 13 104 16 32 64 128 256), losses := [] }

theorem u22919 : Upper (D 8) (R 8) [288,5,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u22919
end Delivery.IrregularNine14.P08
