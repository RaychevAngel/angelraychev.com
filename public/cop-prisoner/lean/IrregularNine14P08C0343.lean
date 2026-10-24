import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0197
import IrregularNine14P08C0198
import IrregularNine14P08C0199
import IrregularNine14P08C0200
import IrregularNine14P08C0201

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20580 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 100 137 188 188 252 188 444), lower := (rows 67 259 100 137 16 32 64 128 256), losses := [] }

theorem u20580 : Upper (D 8) (R 8) [66,257,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20581_9 : Upper (D 8) (R 8) [66,257,96,132,9] 13 :=
  permutation_upper _ _ _ [66,257,9,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11849

theorem m20581_33 : Upper (D 8) (R 8) [66,257,96,132,33] 13 :=
  permutation_upper _ _ _ [66,257,33,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11895

theorem m20581_40 : Upper (D 8) (R 8) [66,257,96,132,40] 13 :=
  permutation_upper _ _ _ [66,257,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11928

theorem m20581_129 : Upper (D 8) (R 8) [66,257,96,132,129] 13 :=
  permutation_upper _ _ _ [66,257,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11951

def r20581 : Route 9 := (fun mask => (mask,id))

def c20581 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20581 : Upper (D 8) (R 8) [66,257,96,132] 13 := by
  apply FastRouting.sound _ _ [66,257,96,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20581 c20581
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20581_9
  · exact m20581_33
  · exact m20581_40
  · exact m20581_129
  · exact u11954
  · exact u11955

theorem m20582_5 : Upper (D 8) (R 8) [66,257,96,144,5] 13 :=
  permutation_upper _ _ _ [66,257,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11842

theorem m20582_9 : Upper (D 8) (R 8) [66,257,96,144,9] 13 :=
  permutation_upper _ _ _ [66,257,9,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11844

theorem m20582_12 : Upper (D 8) (R 8) [66,257,96,144,12] 13 :=
  permutation_upper _ _ _ [66,257,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11872

theorem m20582_33 : Upper (D 8) (R 8) [66,257,96,144,33] 13 :=
  permutation_upper _ _ _ [66,257,33,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11894

theorem m20582_36 : Upper (D 8) (R 8) [66,257,96,144,36] 13 :=
  permutation_upper _ _ _ [66,257,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11914

theorem m20582_40 : Upper (D 8) (R 8) [66,257,96,144,40] 13 :=
  permutation_upper _ _ _ [66,257,40,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11922

theorem m20582_129 : Upper (D 8) (R 8) [66,257,96,144,129] 13 :=
  permutation_upper _ _ _ [66,257,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11952

theorem m20582_132 : Upper (D 8) (R 8) [66,257,96,144,132] 13 :=
  permutation_upper _ _ _ [66,257,96,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11954

def r20582 : Route 9 := (fun mask => (mask,id))

def c20582 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20582 : Upper (D 8) (R 8) [66,257,96,144] 13 := by
  apply FastRouting.sound _ _ [66,257,96,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20582 c20582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20582_5
  · exact m20582_9
  · exact m20582_12
  · exact m20582_33
  · exact m20582_36
  · exact m20582_40
  · exact m20582_129
  · exact m20582_132
  · exact u11956
  · exact u11957

theorem m20583_5 : Upper (D 8) (R 8) [66,257,96,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11843

theorem m20583_9 : Upper (D 8) (R 8) [66,257,96,160,9] 13 :=
  permutation_upper _ _ _ [66,257,9,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11852

theorem m20583_12 : Upper (D 8) (R 8) [66,257,96,160,12] 13 :=
  permutation_upper _ _ _ [66,257,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11873

theorem m20583_33 : Upper (D 8) (R 8) [66,257,96,160,33] 13 :=
  permutation_upper _ _ _ [66,257,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11896

theorem m20583_36 : Upper (D 8) (R 8) [66,257,96,160,36] 13 :=
  permutation_upper _ _ _ [66,257,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11915

theorem m20583_40 : Upper (D 8) (R 8) [66,257,96,160,40] 13 :=
  permutation_upper _ _ _ [66,257,40,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11934

theorem m20583_129 : Upper (D 8) (R 8) [66,257,96,160,129] 13 :=
  permutation_upper _ _ _ [66,257,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11953

theorem m20583_132 : Upper (D 8) (R 8) [66,257,96,160,132] 13 :=
  permutation_upper _ _ _ [66,257,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11955

theorem m20583_136 : Upper (D 8) (R 8) [66,257,96,160,136] 13 :=
  permutation_upper _ _ _ [66,257,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11957

def r20583 : Route 9 := (fun mask => (mask,id))

def c20583 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20583 : Upper (D 8) (R 8) [66,257,96,160] 13 := by
  apply FastRouting.sound _ _ [66,257,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20583 c20583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20583_5
  · exact m20583_9
  · exact m20583_12
  · exact m20583_33
  · exact m20583_36
  · exact m20583_40
  · exact m20583_129
  · exact m20583_132
  · exact m20583_136
  · exact u11958

def b20584 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 133 140 120 120 120 248 376), lower := (rows 67 259 133 140 16 32 64 128 256), losses := [] }

theorem u20584 : Upper (D 8) (R 8) [66,257,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20585 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 133 168 124 124 124 252 380), lower := (rows 67 259 133 168 16 32 64 128 256), losses := [] }

theorem u20585 : Upper (D 8) (R 8) [66,257,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20586 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 133 200 60 60 124 188 316), lower := (rows 67 259 133 200 16 32 64 128 256), losses := [] }

theorem u20586 : Upper (D 8) (R 8) [66,257,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20587 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 140 140 113 113 113 241 369), lower := (rows 67 259 140 140 16 32 64 128 256), losses := [] }

theorem u20587 : Upper (D 8) (R 8) [66,257,136,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20588 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 140 152 117 101 101 229 357), lower := (rows 67 259 140 152 16 32 64 128 256), losses := [] }

theorem u20588 : Upper (D 8) (R 8) [66,257,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20589 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 140 168 117 117 117 245 373), lower := (rows 67 259 140 168 16 32 64 128 256), losses := [] }

theorem u20589 : Upper (D 8) (R 8) [66,257,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20590 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 140 200 53 53 117 181 309), lower := (rows 67 259 140 200 16 32 64 128 256), losses := [] }

theorem u20590 : Upper (D 8) (R 8) [66,257,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20591_5 : Upper (D 8) (R 8) [66,257,144,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11845

theorem m20591_9 : Upper (D 8) (R 8) [66,257,144,160,9] 13 :=
  permutation_upper _ _ _ [66,257,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11853

theorem m20591_12 : Upper (D 8) (R 8) [66,257,144,160,12] 13 :=
  permutation_upper _ _ _ [66,257,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11877

theorem m20591_33 : Upper (D 8) (R 8) [66,257,144,160,33] 13 :=
  permutation_upper _ _ _ [66,257,33,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11897

theorem m20591_36 : Upper (D 8) (R 8) [66,257,144,160,36] 13 :=
  permutation_upper _ _ _ [66,257,40,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11924

theorem m20591_40 : Upper (D 8) (R 8) [66,257,144,160,40] 13 :=
  permutation_upper _ _ _ [66,257,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11935

theorem m20591_65 : Upper (D 8) (R 8) [66,257,144,160,65] 13 :=
  permutation_upper _ _ _ [66,257,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11941

theorem m20591_68 : Upper (D 8) (R 8) [66,257,144,160,68] 13 :=
  permutation_upper _ _ _ [66,257,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11944

theorem m20591_72 : Upper (D 8) (R 8) [66,257,144,160,72] 13 :=
  permutation_upper _ _ _ [66,257,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11949

theorem m20591_96 : Upper (D 8) (R 8) [66,257,144,160,96] 13 :=
  permutation_upper _ _ _ [66,257,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11955

def r20591 : Route 9 := (fun mask => (mask,id))

def c20591 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20591 : Upper (D 8) (R 8) [66,257,144,160] 13 := by
  apply FastRouting.sound _ _ [66,257,144,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r20591 c20591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20591_5
  · exact m20591_9
  · exact m20591_12
  · exact m20591_33
  · exact m20591_36
  · exact m20591_40
  · exact m20591_65
  · exact m20591_68
  · exact m20591_72
  · exact m20591_96

theorem m20592_5 : Upper (D 8) (R 8) [66,257,144,192,5] 13 :=
  permutation_upper _ _ _ [66,257,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11846

theorem m20592_9 : Upper (D 8) (R 8) [66,257,144,192,9] 13 :=
  permutation_upper _ _ _ [66,257,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11856

theorem m20592_12 : Upper (D 8) (R 8) [66,257,144,192,12] 13 :=
  permutation_upper _ _ _ [66,257,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11878

theorem m20592_33 : Upper (D 8) (R 8) [66,257,144,192,33] 13 :=
  permutation_upper _ _ _ [66,257,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11898

theorem m20592_36 : Upper (D 8) (R 8) [66,257,144,192,36] 13 :=
  permutation_upper _ _ _ [66,257,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11925

theorem m20592_40 : Upper (D 8) (R 8) [66,257,144,192,40] 13 :=
  permutation_upper _ _ _ [66,257,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11939

def r20592 : Route 9 := (fun mask => (mask,id))

def c20592 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20592 : Upper (D 8) (R 8) [66,257,144,192] 13 := by
  apply FastRouting.sound _ _ [66,257,144,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20592 c20592
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20592_5
  · exact m20592_9
  · exact m20592_12
  · exact m20592_33
  · exact m20592_36
  · exact m20592_40

def b20593 : PairBound 9 := { available := 125, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 164 168 125 125 125 253 381), lower := (rows 67 259 164 168 16 32 64 128 256), losses := [] }

theorem u20593 : Upper (D 8) (R 8) [66,257,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20594_5 : Upper (D 8) (R 8) [66,257,160,192,5] 13 :=
  permutation_upper _ _ _ [66,257,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11854

theorem m20594_9 : Upper (D 8) (R 8) [66,257,160,192,9] 13 :=
  permutation_upper _ _ _ [66,257,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11857

theorem m20594_12 : Upper (D 8) (R 8) [66,257,160,192,12] 13 :=
  permutation_upper _ _ _ [66,257,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11880

theorem m20594_33 : Upper (D 8) (R 8) [66,257,160,192,33] 13 :=
  permutation_upper _ _ _ [66,257,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11899

theorem m20594_36 : Upper (D 8) (R 8) [66,257,160,192,36] 13 :=
  permutation_upper _ _ _ [66,257,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11937

theorem m20594_40 : Upper (D 8) (R 8) [66,257,160,192,40] 13 :=
  permutation_upper _ _ _ [66,257,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11940

def r20594 : Route 9 := (fun mask => (mask,id))

def c20594 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20594 : Upper (D 8) (R 8) [66,257,160,192] 13 := by
  apply FastRouting.sound _ _ [66,257,160,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20594 c20594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20594_5
  · exact m20594_9
  · exact m20594_12
  · exact m20594_33
  · exact m20594_36
  · exact m20594_40

def b20595 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 13 25 240 224 224 224 480), lower := (rows 67 262 13 25 16 32 64 128 256), losses := [] }

theorem u20595 : Upper (D 8) (R 8) [66,260,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20596 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 13 41 240 240 240 240 496), lower := (rows 67 262 13 41 16 32 64 128 256), losses := [] }

theorem u20596 : Upper (D 8) (R 8) [66,260,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20597 : Route 9 := (fun mask => (mask,id))

def c20597 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20597 : Upper (D 8) (R 8) [66,260,9,48] 13 := by
  apply FastRouting.sound _ _ [66,260,9,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20597 c20597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11959
  · exact u11960
  · exact u11961
  · exact u11962
  · exact u11963
  · exact u11964

def b20598 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 13 73 176 176 240 176 432), lower := (rows 67 262 13 73 16 32 64 128 256), losses := [] }

theorem u20598 : Upper (D 8) (R 8) [66,260,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20599 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 88 177 161 225 161 417), lower := (rows 67 262 13 88 16 32 64 128 256), losses := [] }

theorem u20599 : Upper (D 8) (R 8) [66,260,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20600 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 104 177 177 241 177 433), lower := (rows 67 262 13 104 16 32 64 128 256), losses := [] }

theorem u20600 : Upper (D 8) (R 8) [66,260,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20601 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 13 137 240 240 240 240 496), lower := (rows 67 262 13 137 16 32 64 128 256), losses := [] }

theorem u20601 : Upper (D 8) (R 8) [66,260,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20602 : Route 9 := (fun mask => (mask,id))

def c20602 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20602 : Upper (D 8) (R 8) [66,260,9,144] 13 := by
  apply FastRouting.sound _ _ [66,260,9,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20602 c20602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11965
  · exact u11966
  · exact u11967
  · exact u11968
  · exact u11969
  · exact u11970

def r20603 : Route 9 := (fun mask => (mask,id))

def c20603 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20603 : Upper (D 8) (R 8) [66,260,9,160] 13 := by
  apply FastRouting.sound _ _ [66,260,9,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20603 c20603
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11971
  · exact u11972
  · exact u11973
  · exact u11974
  · exact u11975
  · exact u11976

def b20604 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 200 177 177 241 177 433), lower := (rows 67 262 13 200 16 32 64 128 256), losses := [] }

theorem u20604 : Upper (D 8) (R 8) [66,260,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20605 : Route 9 := (fun mask => (mask,id))

def c20605 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20605 : Upper (D 8) (R 8) [66,260,24,33] 13 := by
  apply FastRouting.sound _ _ [66,260,24,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20605 c20605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11977
  · exact u11978
  · exact u11979
  · exact u11980
  · exact u11981
  · exact u11982

def b20606 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 28 73 177 161 225 161 417), lower := (rows 67 262 28 73 16 32 64 128 256), losses := [] }

theorem u20606 : Upper (D 8) (R 8) [66,260,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20607 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 28 104 177 161 225 161 417), lower := (rows 67 262 28 104 16 32 64 128 256), losses := [] }

theorem u20607 : Upper (D 8) (R 8) [66,260,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20608_33 : Upper (D 8) (R 8) [66,260,24,129,33] 13 :=
  permutation_upper _ _ _ [66,260,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11980

theorem m20608_65 : Upper (D 8) (R 8) [66,260,24,129,65] 13 :=
  permutation_upper _ _ _ [66,260,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11983

theorem m20608_96 : Upper (D 8) (R 8) [66,260,24,129,96] 13 :=
  permutation_upper _ _ _ [66,260,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11985

def r20608 : Route 9 := (fun mask => (mask,id))

def c20608 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20608 : Upper (D 8) (R 8) [66,260,24,129] 13 := by
  apply FastRouting.sound _ _ [66,260,24,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20608 c20608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20608_33
  · exact m20608_65
  · exact m20608_96
  · exact u11987
  · exact u11988
  · exact u11989

theorem m20609_33 : Upper (D 8) (R 8) [66,260,24,160,33] 13 :=
  permutation_upper _ _ _ [66,260,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11981

theorem m20609_65 : Upper (D 8) (R 8) [66,260,24,160,65] 13 :=
  permutation_upper _ _ _ [66,260,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11984

theorem m20609_96 : Upper (D 8) (R 8) [66,260,24,160,96] 13 :=
  permutation_upper _ _ _ [66,260,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11986

theorem m20609_129 : Upper (D 8) (R 8) [66,260,24,160,129] 13 :=
  permutation_upper _ _ _ [66,260,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11988

def r20609 : Route 9 := (fun mask => (mask,id))

def c20609 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20609 : Upper (D 8) (R 8) [66,260,24,160] 13 := by
  apply FastRouting.sound _ _ [66,260,24,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20609 c20609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20609_33
  · exact m20609_65
  · exact m20609_96
  · exact m20609_129
  · exact u11990
  · exact u11991

def b20610 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 28 200 177 161 225 161 417), lower := (rows 67 262 28 200 16 32 64 128 256), losses := [] }

theorem u20610 : Upper (D 8) (R 8) [66,260,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20611 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 37 25 248 232 232 232 488), lower := (rows 67 262 37 25 16 32 64 128 256), losses := [] }

theorem u20611 : Upper (D 8) (R 8) [66,260,33,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20612 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 248 248 248 248 504), lower := (rows 67 262 37 41 16 32 64 128 256), losses := [] }

theorem u20612 : Upper (D 8) (R 8) [66,260,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20613_9 : Upper (D 8) (R 8) [66,260,33,48,9] 13 :=
  permutation_upper _ _ _ [66,260,33,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11992

theorem m20613_33 : Upper (D 8) (R 8) [66,260,33,48,33] 13 :=
  permutation_upper _ _ _ [66,260,33,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11998

def r20613 : Route 9 := (fun mask => (mask,id))

def c20613 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20613 : Upper (D 8) (R 8) [66,260,33,48] 13 := by
  apply FastRouting.sound _ _ [66,260,33,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20613 c20613
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20613_9
  · exact m20613_33
  · exact u12004
  · exact u12005
  · exact u12006
  · exact u12007
  · exact u12008
  · exact u12009
  · exact u12010
  · exact u12011

def b20614 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 73 184 184 248 184 440), lower := (rows 67 262 37 73 16 32 64 128 256), losses := [] }

theorem u20614 : Upper (D 8) (R 8) [66,260,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20615_9 : Upper (D 8) (R 8) [66,260,33,80,9] 13 :=
  permutation_upper _ _ _ [66,260,33,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11993

theorem m20615_33 : Upper (D 8) (R 8) [66,260,33,80,33] 13 :=
  permutation_upper _ _ _ [66,260,33,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11999

theorem m20615_40 : Upper (D 8) (R 8) [66,260,33,80,40] 13 :=
  permutation_upper _ _ _ [66,260,33,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12006

def r20615 : Route 9 := (fun mask => (mask,id))

def c20615 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20615 : Upper (D 8) (R 8) [66,260,33,80] 13 := by
  apply FastRouting.sound _ _ [66,260,33,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20615 c20615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20615_9
  · exact m20615_33
  · exact m20615_40
  · exact u12014
  · exact u12015
  · exact u12016

theorem m20616_9 : Upper (D 8) (R 8) [66,260,33,96,9] 13 :=
  permutation_upper _ _ _ [66,260,33,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11994

theorem m20616_33 : Upper (D 8) (R 8) [66,260,33,96,33] 13 :=
  permutation_upper _ _ _ [66,260,33,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12000

theorem m20616_40 : Upper (D 8) (R 8) [66,260,33,96,40] 13 :=
  permutation_upper _ _ _ [66,260,33,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12007

def r20616 : Route 9 := (fun mask => (mask,id))

def c20616 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20616 : Upper (D 8) (R 8) [66,260,33,96] 13 := by
  apply FastRouting.sound _ _ [66,260,33,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20616 c20616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20616_9
  · exact m20616_33
  · exact m20616_40
  · exact u12017
  · exact u12018
  · exact u12019

def b20617 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 37 137 248 248 248 248 504), lower := (rows 67 262 37 137 16 32 64 128 256), losses := [] }

theorem u20617 : Upper (D 8) (R 8) [66,260,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20618_9 : Upper (D 8) (R 8) [66,260,33,144,9] 13 :=
  permutation_upper _ _ _ [66,260,33,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11995

theorem m20618_33 : Upper (D 8) (R 8) [66,260,33,144,33] 13 :=
  permutation_upper _ _ _ [66,260,33,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12001

theorem m20618_40 : Upper (D 8) (R 8) [66,260,33,144,40] 13 :=
  permutation_upper _ _ _ [66,260,33,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12009

theorem m20618_65 : Upper (D 8) (R 8) [66,260,33,144,65] 13 :=
  permutation_upper _ _ _ [66,260,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12012

theorem m20618_72 : Upper (D 8) (R 8) [66,260,33,144,72] 13 :=
  permutation_upper _ _ _ [66,260,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12015

theorem m20618_96 : Upper (D 8) (R 8) [66,260,33,144,96] 13 :=
  permutation_upper _ _ _ [66,260,33,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12018

theorem m20618_129 : Upper (D 8) (R 8) [66,260,33,144,129] 13 :=
  permutation_upper _ _ _ [66,260,33,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12020

def r20618 : Route 9 := (fun mask => (mask,id))

def c20618 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20618 : Upper (D 8) (R 8) [66,260,33,144] 13 := by
  apply FastRouting.sound _ _ [66,260,33,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20618 c20618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20618_9
  · exact m20618_33
  · exact m20618_40
  · exact m20618_65
  · exact m20618_72
  · exact m20618_96
  · exact m20618_129
  · exact u12023
  · exact u12024
  · exact u12025

theorem m20619_9 : Upper (D 8) (R 8) [66,260,33,160,9] 13 :=
  permutation_upper _ _ _ [66,260,33,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11996

theorem m20619_33 : Upper (D 8) (R 8) [66,260,33,160,33] 13 :=
  permutation_upper _ _ _ [66,260,33,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12002

theorem m20619_40 : Upper (D 8) (R 8) [66,260,33,160,40] 13 :=
  permutation_upper _ _ _ [66,260,33,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12010

theorem m20619_65 : Upper (D 8) (R 8) [66,260,33,160,65] 13 :=
  permutation_upper _ _ _ [66,260,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12013

theorem m20619_72 : Upper (D 8) (R 8) [66,260,33,160,72] 13 :=
  permutation_upper _ _ _ [66,260,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12016

theorem m20619_96 : Upper (D 8) (R 8) [66,260,33,160,96] 13 :=
  permutation_upper _ _ _ [66,260,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12019

theorem m20619_129 : Upper (D 8) (R 8) [66,260,33,160,129] 13 :=
  permutation_upper _ _ _ [66,260,33,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12021

theorem m20619_136 : Upper (D 8) (R 8) [66,260,33,160,136] 13 :=
  permutation_upper _ _ _ [66,260,33,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12024

def r20619 : Route 9 := (fun mask => (mask,id))

def c20619 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20619 : Upper (D 8) (R 8) [66,260,33,160] 13 := by
  apply FastRouting.sound _ _ [66,260,33,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20619 c20619
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20619_9
  · exact m20619_33
  · exact m20619_40
  · exact m20619_65
  · exact m20619_72
  · exact m20619_96
  · exact m20619_129
  · exact m20619_136
  · exact u12026
  · exact u12027

theorem m20620_9 : Upper (D 8) (R 8) [66,260,33,192,9] 13 :=
  permutation_upper _ _ _ [66,260,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11997

theorem m20620_33 : Upper (D 8) (R 8) [66,260,33,192,33] 13 :=
  permutation_upper _ _ _ [66,260,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12003

theorem m20620_40 : Upper (D 8) (R 8) [66,260,33,192,40] 13 :=
  permutation_upper _ _ _ [66,260,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12011

theorem m20620_129 : Upper (D 8) (R 8) [66,260,33,192,129] 13 :=
  permutation_upper _ _ _ [66,260,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12022

theorem m20620_136 : Upper (D 8) (R 8) [66,260,33,192,136] 13 :=
  permutation_upper _ _ _ [66,260,33,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12025

theorem m20620_160 : Upper (D 8) (R 8) [66,260,33,192,160] 13 :=
  permutation_upper _ _ _ [66,260,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12027

def r20620 : Route 9 := (fun mask => (mask,id))

def c20620 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20620 : Upper (D 8) (R 8) [66,260,33,192] 13 := by
  apply FastRouting.sound _ _ [66,260,33,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20620 c20620
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20620_9
  · exact m20620_33
  · exact m20620_40
  · exact m20620_129
  · exact m20620_136
  · exact m20620_160

def r20621 : Route 9 := (fun mask => (mask,id))

def c20621 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20621 : Upper (D 8) (R 8) [66,260,40,17] 13 := by
  apply FastRouting.sound _ _ [66,260,40,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20621 c20621
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12028
  · exact u12029
  · exact u12030
  · exact u12031
  · exact u12032
  · exact u12033

def b20622 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 44 41 241 241 241 241 497), lower := (rows 67 262 44 41 16 32 64 128 256), losses := [] }

theorem u20622 : Upper (D 8) (R 8) [66,260,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20623 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 44 56 241 225 225 225 481), lower := (rows 67 262 44 56 16 32 64 128 256), losses := [] }

theorem u20623 : Upper (D 8) (R 8) [66,260,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20624 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 73 177 177 241 177 433), lower := (rows 67 262 44 73 16 32 64 128 256), losses := [] }

theorem u20624 : Upper (D 8) (R 8) [66,260,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20625 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 44 88 177 161 225 161 417), lower := (rows 67 262 44 88 16 32 64 128 256), losses := [] }

theorem u20625 : Upper (D 8) (R 8) [66,260,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20626 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 44 104 177 177 241 177 433), lower := (rows 67 262 44 104 16 32 64 128 256), losses := [] }

theorem u20626 : Upper (D 8) (R 8) [66,260,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20627 : Route 9 := (fun mask => (mask,id))

def c20627 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20627 : Upper (D 8) (R 8) [66,260,40,129] 13 := by
  apply FastRouting.sound _ _ [66,260,40,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20627 c20627
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12034
  · exact u12035
  · exact u12036
  · exact u12037
  · exact u12038
  · exact u12039

def r20628 : Route 9 := (fun mask => (mask,id))

def c20628 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20628 : Upper (D 8) (R 8) [66,260,40,144] 13 := by
  apply FastRouting.sound _ _ [66,260,40,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20628 c20628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12040
  · exact u12041
  · exact u12042
  · exact u12043
  · exact u12044
  · exact u12045

def b20629 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 44 168 241 241 241 241 497), lower := (rows 67 262 44 168 16 32 64 128 256), losses := [] }

theorem u20629 : Upper (D 8) (R 8) [66,260,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20630 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 44 200 177 177 241 177 433), lower := (rows 67 262 44 200 16 32 64 128 256), losses := [] }

theorem u20630 : Upper (D 8) (R 8) [66,260,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20631 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 25 248 232 232 232 488), lower := (rows 67 262 133 25 16 32 64 128 256), losses := [] }

theorem u20631 : Upper (D 8) (R 8) [66,260,129,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20632 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 41 248 248 248 248 504), lower := (rows 67 262 133 41 16 32 64 128 256), losses := [] }

theorem u20632 : Upper (D 8) (R 8) [66,260,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20633_9 : Upper (D 8) (R 8) [66,260,129,48,9] 13 :=
  permutation_upper _ _ _ [66,260,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12046

theorem m20633_33 : Upper (D 8) (R 8) [66,260,129,48,33] 13 :=
  permutation_upper _ _ _ [66,260,129,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12052

def r20633 : Route 9 := (fun mask => (mask,id))

def c20633 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20633 : Upper (D 8) (R 8) [66,260,129,48] 13 := by
  apply FastRouting.sound _ _ [66,260,129,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20633 c20633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20633_9
  · exact m20633_33
  · exact u12058
  · exact u12059
  · exact u12060
  · exact u12061
  · exact u12062
  · exact u12063
  · exact u12064
  · exact u12065

def b20634 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 73 184 184 248 184 440), lower := (rows 67 262 133 73 16 32 64 128 256), losses := [] }

theorem u20634 : Upper (D 8) (R 8) [66,260,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20635_9 : Upper (D 8) (R 8) [66,260,129,80,9] 13 :=
  permutation_upper _ _ _ [66,260,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12047

theorem m20635_33 : Upper (D 8) (R 8) [66,260,129,80,33] 13 :=
  permutation_upper _ _ _ [66,260,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12053

theorem m20635_40 : Upper (D 8) (R 8) [66,260,129,80,40] 13 :=
  permutation_upper _ _ _ [66,260,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12060

def r20635 : Route 9 := (fun mask => (mask,id))

def c20635 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20635 : Upper (D 8) (R 8) [66,260,129,80] 13 := by
  apply FastRouting.sound _ _ [66,260,129,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20635 c20635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20635_9
  · exact m20635_33
  · exact m20635_40
  · exact u12068
  · exact u12069
  · exact u12070

theorem m20636_9 : Upper (D 8) (R 8) [66,260,129,96,9] 13 :=
  permutation_upper _ _ _ [66,260,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12048

theorem m20636_33 : Upper (D 8) (R 8) [66,260,129,96,33] 13 :=
  permutation_upper _ _ _ [66,260,129,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12054

theorem m20636_40 : Upper (D 8) (R 8) [66,260,129,96,40] 13 :=
  permutation_upper _ _ _ [66,260,129,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12061

def r20636 : Route 9 := (fun mask => (mask,id))

def c20636 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20636 : Upper (D 8) (R 8) [66,260,129,96] 13 := by
  apply FastRouting.sound _ _ [66,260,129,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20636 c20636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20636_9
  · exact m20636_33
  · exact m20636_40
  · exact u12071
  · exact u12072
  · exact u12073

def b20637 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 133 137 120 120 120 248 376), lower := (rows 67 262 133 137 16 32 64 128 256), losses := [] }

theorem u20637 : Upper (D 8) (R 8) [66,260,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20638_9 : Upper (D 8) (R 8) [66,260,129,144,9] 13 :=
  permutation_upper _ _ _ [66,260,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12049

theorem m20638_33 : Upper (D 8) (R 8) [66,260,129,144,33] 13 :=
  permutation_upper _ _ _ [66,260,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12055

theorem m20638_40 : Upper (D 8) (R 8) [66,260,129,144,40] 13 :=
  permutation_upper _ _ _ [66,260,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12063

theorem m20638_65 : Upper (D 8) (R 8) [66,260,129,144,65] 13 :=
  permutation_upper _ _ _ [66,260,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12066

theorem m20638_72 : Upper (D 8) (R 8) [66,260,129,144,72] 13 :=
  permutation_upper _ _ _ [66,260,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12069

theorem m20638_96 : Upper (D 8) (R 8) [66,260,129,144,96] 13 :=
  permutation_upper _ _ _ [66,260,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12072

def r20638 : Route 9 := (fun mask => (mask,id))

def c20638 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20638 : Upper (D 8) (R 8) [66,260,129,144] 13 := by
  apply FastRouting.sound _ _ [66,260,129,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20638 c20638
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20638_9
  · exact m20638_33
  · exact m20638_40
  · exact m20638_65
  · exact m20638_72
  · exact m20638_96

theorem m20639_9 : Upper (D 8) (R 8) [66,260,129,160,9] 13 :=
  permutation_upper _ _ _ [66,260,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12050

theorem m20639_33 : Upper (D 8) (R 8) [66,260,129,160,33] 13 :=
  permutation_upper _ _ _ [66,260,129,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12056

theorem m20639_40 : Upper (D 8) (R 8) [66,260,129,160,40] 13 :=
  permutation_upper _ _ _ [66,260,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12064

theorem m20639_65 : Upper (D 8) (R 8) [66,260,129,160,65] 13 :=
  permutation_upper _ _ _ [66,260,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12067

theorem m20639_72 : Upper (D 8) (R 8) [66,260,129,160,72] 13 :=
  permutation_upper _ _ _ [66,260,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12070

theorem m20639_96 : Upper (D 8) (R 8) [66,260,129,160,96] 13 :=
  permutation_upper _ _ _ [66,260,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12073

def r20639 : Route 9 := (fun mask => (mask,id))

def c20639 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20639 : Upper (D 8) (R 8) [66,260,129,160] 13 := by
  apply FastRouting.sound _ _ [66,260,129,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20639 c20639
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20639_9
  · exact m20639_33
  · exact m20639_40
  · exact m20639_65
  · exact m20639_72
  · exact m20639_96

#print axioms u20639
end Delivery.IrregularNine14.P08
