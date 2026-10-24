import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0192
import IrregularNine14P08C0193
import IrregularNine14P08C0195
import IrregularNine14P08C0196
import IrregularNine14P08C0197
import IrregularNine14P08C0198
import IrregularNine14P08C0199

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20520 : PairBound 9 := { available := 125, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 164 265 125 125 125 253 381), lower := (rows 67 162 164 265 16 32 64 128 256), losses := [] }

theorem u20520 : Upper (D 8) (R 8) [66,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20521 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 164 268 121 121 121 249 377), lower := (rows 67 162 164 268 16 32 64 128 256), losses := [] }

theorem u20521 : Upper (D 8) (R 8) [66,160,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20522 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 164 296 93 125 93 221 349), lower := (rows 67 162 164 296 16 32 64 128 256), losses := [] }

theorem u20522 : Upper (D 8) (R 8) [66,160,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20523 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 164 328 61 61 125 189 317), lower := (rows 67 162 164 328 16 32 64 128 256), losses := [] }

theorem u20523 : Upper (D 8) (R 8) [66,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20524_5 : Upper (D 8) (R 8) [66,160,192,257,5] 13 :=
  permutation_upper _ _ _ [66,160,9,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11541

theorem m20524_9 : Upper (D 8) (R 8) [66,160,192,257,9] 13 :=
  permutation_upper _ _ _ [66,160,9,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11548

theorem m20524_12 : Upper (D 8) (R 8) [66,160,192,257,12] 13 :=
  permutation_upper _ _ _ [66,160,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11628

theorem m20524_33 : Upper (D 8) (R 8) [66,160,192,257,33] 13 :=
  permutation_upper _ _ _ [66,160,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11702

theorem m20524_36 : Upper (D 8) (R 8) [66,160,192,257,36] 13 :=
  permutation_upper _ _ _ [66,160,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11757

theorem m20524_40 : Upper (D 8) (R 8) [66,160,192,257,40] 13 :=
  permutation_upper _ _ _ [66,160,40,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11766

def r20524 : Route 9 := (fun mask => (mask,id))

def c20524 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20524 : Upper (D 8) (R 8) [66,160,192,257] 13 := by
  apply FastRouting.sound _ _ [66,160,192,257] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20524 c20524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20524_5
  · exact m20524_9
  · exact m20524_12
  · exact m20524_33
  · exact m20524_36
  · exact m20524_40

theorem m20525_9 : Upper (D 8) (R 8) [66,160,192,260,9] 13 :=
  permutation_upper _ _ _ [66,160,9,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11563

theorem m20525_33 : Upper (D 8) (R 8) [66,160,192,260,33] 13 :=
  permutation_upper _ _ _ [66,160,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11704

theorem m20525_40 : Upper (D 8) (R 8) [66,160,192,260,40] 13 :=
  permutation_upper _ _ _ [66,160,40,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11778

def r20525 : Route 9 := (fun mask => (mask,id))

def c20525 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20525 : Upper (D 8) (R 8) [66,160,192,260] 13 := by
  apply FastRouting.sound _ _ [66,160,192,260] 13 (by decide) (choices 2) [9,33,40] r20525 c20525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m20525_9
  · exact m20525_33
  · exact m20525_40

theorem m20526_5 : Upper (D 8) (R 8) [66,160,192,272,5] 13 :=
  permutation_upper _ _ _ [66,160,9,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11542

theorem m20526_9 : Upper (D 8) (R 8) [66,160,192,272,9] 13 :=
  permutation_upper _ _ _ [66,160,9,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11554

theorem m20526_12 : Upper (D 8) (R 8) [66,160,192,272,12] 13 :=
  permutation_upper _ _ _ [66,160,24,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11629

theorem m20526_33 : Upper (D 8) (R 8) [66,160,192,272,33] 13 :=
  permutation_upper _ _ _ [66,160,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11703

theorem m20526_36 : Upper (D 8) (R 8) [66,160,192,272,36] 13 :=
  permutation_upper _ _ _ [66,160,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11758

theorem m20526_40 : Upper (D 8) (R 8) [66,160,192,272,40] 13 :=
  permutation_upper _ _ _ [66,160,40,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11771

def r20526 : Route 9 := (fun mask => (mask,id))

def c20526 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20526 : Upper (D 8) (R 8) [66,160,192,272] 13 := by
  apply FastRouting.sound _ _ [66,160,192,272] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20526 c20526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20526_5
  · exact m20526_9
  · exact m20526_12
  · exact m20526_33
  · exact m20526_36
  · exact m20526_40

theorem m20527_5 : Upper (D 8) (R 8) [66,160,192,288,5] 13 :=
  permutation_upper _ _ _ [66,160,9,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11543

theorem m20527_9 : Upper (D 8) (R 8) [66,160,192,288,9] 13 :=
  permutation_upper _ _ _ [66,160,9,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11572

theorem m20527_12 : Upper (D 8) (R 8) [66,160,192,288,12] 13 :=
  permutation_upper _ _ _ [66,160,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11630

theorem m20527_33 : Upper (D 8) (R 8) [66,160,192,288,33] 13 :=
  permutation_upper _ _ _ [66,160,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11705

theorem m20527_36 : Upper (D 8) (R 8) [66,160,192,288,36] 13 :=
  permutation_upper _ _ _ [66,160,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11759

theorem m20527_40 : Upper (D 8) (R 8) [66,160,192,288,40] 13 :=
  permutation_upper _ _ _ [66,160,40,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11781

def r20527 : Route 9 := (fun mask => (mask,id))

def c20527 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20527 : Upper (D 8) (R 8) [66,160,192,288] 13 := by
  apply FastRouting.sound _ _ [66,160,192,288] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20527 c20527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20527_5
  · exact m20527_9
  · exact m20527_12
  · exact m20527_33
  · exact m20527_36
  · exact m20527_40

def b20528 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 28 240 224 224 224 480), lower := (rows 67 259 13 28 16 32 64 128 256), losses := [] }

theorem u20528 : Upper (D 8) (R 8) [66,257,9,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20529 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 44 240 240 240 240 496), lower := (rows 67 259 13 44 16 32 64 128 256), losses := [] }

theorem u20529 : Upper (D 8) (R 8) [66,257,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20530 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 259 13 76 176 176 240 176 432), lower := (rows 67 259 13 76 16 32 64 128 256), losses := [] }

theorem u20530 : Upper (D 8) (R 8) [66,257,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20531 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 104 180 180 244 180 436), lower := (rows 67 259 13 104 16 32 64 128 256), losses := [] }

theorem u20531 : Upper (D 8) (R 8) [66,257,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20532 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 140 240 240 240 240 496), lower := (rows 67 259 13 140 16 32 64 128 256), losses := [] }

theorem u20532 : Upper (D 8) (R 8) [66,257,9,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20533 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 168 244 244 244 244 500), lower := (rows 67 259 13 168 16 32 64 128 256), losses := [] }

theorem u20533 : Upper (D 8) (R 8) [66,257,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20534 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 200 180 180 244 180 436), lower := (rows 67 259 13 200 16 32 64 128 256), losses := [] }

theorem u20534 : Upper (D 8) (R 8) [66,257,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20535 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 21 44 248 232 232 232 488), lower := (rows 67 259 21 44 16 32 64 128 256), losses := [] }

theorem u20535 : Upper (D 8) (R 8) [66,257,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20536 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 21 76 184 168 232 168 424), lower := (rows 67 259 21 76 16 32 64 128 256), losses := [] }

theorem u20536 : Upper (D 8) (R 8) [66,257,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20537 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 21 104 188 172 236 172 428), lower := (rows 67 259 21 104 16 32 64 128 256), losses := [] }

theorem u20537 : Upper (D 8) (R 8) [66,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20538 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 21 140 248 232 232 232 488), lower := (rows 67 259 21 140 16 32 64 128 256), losses := [] }

theorem u20538 : Upper (D 8) (R 8) [66,257,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20539 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 21 168 252 236 236 236 492), lower := (rows 67 259 21 168 16 32 64 128 256), losses := [] }

theorem u20539 : Upper (D 8) (R 8) [66,257,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20540 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 21 200 188 172 236 172 428), lower := (rows 67 259 21 200 16 32 64 128 256), losses := [] }

theorem u20540 : Upper (D 8) (R 8) [66,257,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20541 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 41 244 228 228 228 484), lower := (rows 67 259 28 41 16 32 64 128 256), losses := [] }

theorem u20541 : Upper (D 8) (R 8) [66,257,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20542_33 : Upper (D 8) (R 8) [66,257,24,36,33] 13 :=
  permutation_upper _ _ _ [66,257,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11858

def r20542 : Route 9 := (fun mask => (mask,id))

def c20542 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20542 : Upper (D 8) (R 8) [66,257,24,36] 13 := by
  apply FastRouting.sound _ _ [66,257,24,36] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20542 c20542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20542_33
  · exact u11863
  · exact u11864
  · exact u11865
  · exact u11866
  · exact u11867

def b20543 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 73 180 164 228 164 420), lower := (rows 67 259 28 73 16 32 64 128 256), losses := [] }

theorem u20543 : Upper (D 8) (R 8) [66,257,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20544 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 76 177 161 225 161 417), lower := (rows 67 259 28 76 16 32 64 128 256), losses := [] }

theorem u20544 : Upper (D 8) (R 8) [66,257,24,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20545_5 : Upper (D 8) (R 8) [66,257,24,96,5] 13 :=
  permutation_upper _ _ _ [66,257,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11828

theorem m20545_33 : Upper (D 8) (R 8) [66,257,24,96,33] 13 :=
  permutation_upper _ _ _ [66,257,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11859

theorem m20545_36 : Upper (D 8) (R 8) [66,257,24,96,36] 13 :=
  permutation_upper _ _ _ [66,257,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11864

def r20545 : Route 9 := (fun mask => (mask,id))

def c20545 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20545 : Upper (D 8) (R 8) [66,257,24,96] 13 := by
  apply FastRouting.sound _ _ [66,257,24,96] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20545 c20545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20545_5
  · exact m20545_33
  · exact m20545_36
  · exact u11871
  · exact u11872
  · exact u11873

def b20546 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 137 244 228 228 228 484), lower := (rows 67 259 28 137 16 32 64 128 256), losses := [] }

theorem u20546 : Upper (D 8) (R 8) [66,257,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20547_33 : Upper (D 8) (R 8) [66,257,24,132,33] 13 :=
  permutation_upper _ _ _ [66,257,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11860

theorem m20547_65 : Upper (D 8) (R 8) [66,257,24,132,65] 13 :=
  permutation_upper _ _ _ [66,257,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11868

theorem m20547_96 : Upper (D 8) (R 8) [66,257,24,132,96] 13 :=
  permutation_upper _ _ _ [66,257,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11872

theorem m20547_129 : Upper (D 8) (R 8) [66,257,24,132,129] 13 :=
  permutation_upper _ _ _ [66,257,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11874

def r20547 : Route 9 := (fun mask => (mask,id))

def c20547 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20547 : Upper (D 8) (R 8) [66,257,24,132] 13 := by
  apply FastRouting.sound _ _ [66,257,24,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20547 c20547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20547_33
  · exact m20547_65
  · exact m20547_96
  · exact m20547_129
  · exact u11877
  · exact u11878

theorem m20548_5 : Upper (D 8) (R 8) [66,257,24,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11829

theorem m20548_33 : Upper (D 8) (R 8) [66,257,24,160,33] 13 :=
  permutation_upper _ _ _ [66,257,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11861

theorem m20548_36 : Upper (D 8) (R 8) [66,257,24,160,36] 13 :=
  permutation_upper _ _ _ [66,257,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11866

theorem m20548_65 : Upper (D 8) (R 8) [66,257,24,160,65] 13 :=
  permutation_upper _ _ _ [66,257,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11869

theorem m20548_68 : Upper (D 8) (R 8) [66,257,24,160,68] 13 :=
  permutation_upper _ _ _ [66,257,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11870

theorem m20548_96 : Upper (D 8) (R 8) [66,257,24,160,96] 13 :=
  permutation_upper _ _ _ [66,257,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11873

theorem m20548_129 : Upper (D 8) (R 8) [66,257,24,160,129] 13 :=
  permutation_upper _ _ _ [66,257,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11875

theorem m20548_132 : Upper (D 8) (R 8) [66,257,24,160,132] 13 :=
  permutation_upper _ _ _ [66,257,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11877

def r20548 : Route 9 := (fun mask => (mask,id))

def c20548 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20548 : Upper (D 8) (R 8) [66,257,24,160] 13 := by
  apply FastRouting.sound _ _ [66,257,24,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r20548 c20548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20548_5
  · exact m20548_33
  · exact m20548_36
  · exact m20548_65
  · exact m20548_68
  · exact m20548_96
  · exact m20548_129
  · exact m20548_132
  · exact u11879
  · exact u11880

theorem m20549_5 : Upper (D 8) (R 8) [66,257,24,192,5] 13 :=
  permutation_upper _ _ _ [66,257,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11830

theorem m20549_33 : Upper (D 8) (R 8) [66,257,24,192,33] 13 :=
  permutation_upper _ _ _ [66,257,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11862

theorem m20549_36 : Upper (D 8) (R 8) [66,257,24,192,36] 13 :=
  permutation_upper _ _ _ [66,257,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11867

theorem m20549_129 : Upper (D 8) (R 8) [66,257,24,192,129] 13 :=
  permutation_upper _ _ _ [66,257,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11876

theorem m20549_132 : Upper (D 8) (R 8) [66,257,24,192,132] 13 :=
  permutation_upper _ _ _ [66,257,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11878

theorem m20549_160 : Upper (D 8) (R 8) [66,257,24,192,160] 13 :=
  permutation_upper _ _ _ [66,257,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11880

def r20549 : Route 9 := (fun mask => (mask,id))

def c20549 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20549 : Upper (D 8) (R 8) [66,257,24,192] 13 := by
  apply FastRouting.sound _ _ [66,257,24,192] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20549 c20549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20549_5
  · exact m20549_33
  · exact m20549_36
  · exact m20549_129
  · exact m20549_132
  · exact m20549_160

def b20550 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 44 248 248 248 248 504), lower := (rows 67 259 37 44 16 32 64 128 256), losses := [] }

theorem u20550 : Upper (D 8) (R 8) [66,257,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20551 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 76 184 184 248 184 440), lower := (rows 67 259 37 76 16 32 64 128 256), losses := [] }

theorem u20551 : Upper (D 8) (R 8) [66,257,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20552 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 104 188 188 252 188 444), lower := (rows 67 259 37 104 16 32 64 128 256), losses := [] }

theorem u20552 : Upper (D 8) (R 8) [66,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20553 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 140 248 248 248 248 504), lower := (rows 67 259 37 140 16 32 64 128 256), losses := [] }

theorem u20553 : Upper (D 8) (R 8) [66,257,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20554 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 168 252 252 252 252 508), lower := (rows 67 259 37 168 16 32 64 128 256), losses := [] }

theorem u20554 : Upper (D 8) (R 8) [66,257,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20555 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 200 188 188 252 188 444), lower := (rows 67 259 37 200 16 32 64 128 256), losses := [] }

theorem u20555 : Upper (D 8) (R 8) [66,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20556 : PairBound 9 := { available := 241, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 44 241 241 241 241 497), lower := (rows 67 259 44 44 16 32 64 128 256), losses := [] }

theorem u20556 : Upper (D 8) (R 8) [66,257,40,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20557 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 56 245 229 229 229 485), lower := (rows 67 259 44 56 16 32 64 128 256), losses := [] }

theorem u20557 : Upper (D 8) (R 8) [66,257,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20558 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 73 180 180 244 180 436), lower := (rows 67 259 44 73 16 32 64 128 256), losses := [] }

theorem u20558 : Upper (D 8) (R 8) [66,257,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20559 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 76 177 177 241 177 433), lower := (rows 67 259 44 76 16 32 64 128 256), losses := [] }

theorem u20559 : Upper (D 8) (R 8) [66,257,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20560_5 : Upper (D 8) (R 8) [66,257,40,80,5] 13 :=
  permutation_upper _ _ _ [66,257,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11834

theorem m20560_33 : Upper (D 8) (R 8) [66,257,40,80,33] 13 :=
  permutation_upper _ _ _ [66,257,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11886

theorem m20560_36 : Upper (D 8) (R 8) [66,257,40,80,36] 13 :=
  permutation_upper _ _ _ [66,257,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11903

def r20560 : Route 9 := (fun mask => (mask,id))

def c20560 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20560 : Upper (D 8) (R 8) [66,257,40,80] 13 := by
  apply FastRouting.sound _ _ [66,257,40,80] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20560 c20560
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20560_5
  · exact m20560_33
  · exact m20560_36
  · exact u11911
  · exact u11912
  · exact u11913

def b20561 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 104 181 181 245 181 437), lower := (rows 67 259 44 104 16 32 64 128 256), losses := [] }

theorem u20561 : Upper (D 8) (R 8) [66,257,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20562 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 137 244 244 244 244 500), lower := (rows 67 259 44 137 16 32 64 128 256), losses := [] }

theorem u20562 : Upper (D 8) (R 8) [66,257,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20563_33 : Upper (D 8) (R 8) [66,257,40,132,33] 13 :=
  permutation_upper _ _ _ [66,257,33,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11888

def r20563 : Route 9 := (fun mask => (mask,id))

def c20563 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20563 : Upper (D 8) (R 8) [66,257,40,132] 13 := by
  apply FastRouting.sound _ _ [66,257,40,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20563 c20563
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20563_33
  · exact u11921
  · exact u11922
  · exact u11923
  · exact u11924
  · exact u11925

theorem m20564_5 : Upper (D 8) (R 8) [66,257,40,144,5] 13 :=
  permutation_upper _ _ _ [66,257,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11835

theorem m20564_33 : Upper (D 8) (R 8) [66,257,40,144,33] 13 :=
  permutation_upper _ _ _ [66,257,33,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11887

theorem m20564_36 : Upper (D 8) (R 8) [66,257,40,144,36] 13 :=
  permutation_upper _ _ _ [66,257,40,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11905

def r20564 : Route 9 := (fun mask => (mask,id))

def c20564 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20564 : Upper (D 8) (R 8) [66,257,40,144] 13 := by
  apply FastRouting.sound _ _ [66,257,40,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r20564 c20564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20564_5
  · exact m20564_33
  · exact m20564_36
  · exact u11926
  · exact u11927
  · exact u11928
  · exact u11929
  · exact u11930
  · exact u11931
  · exact u11932

def b20565 : PairBound 9 := { available := 245, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 168 245 245 245 245 501), lower := (rows 67 259 44 168 16 32 64 128 256), losses := [] }

theorem u20565 : Upper (D 8) (R 8) [66,257,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20566_5 : Upper (D 8) (R 8) [66,257,40,192,5] 13 :=
  permutation_upper _ _ _ [66,257,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11836

theorem m20566_33 : Upper (D 8) (R 8) [66,257,40,192,33] 13 :=
  permutation_upper _ _ _ [66,257,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11889

theorem m20566_36 : Upper (D 8) (R 8) [66,257,40,192,36] 13 :=
  permutation_upper _ _ _ [66,257,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11907

def r20566 : Route 9 := (fun mask => (mask,id))

def c20566 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20566 : Upper (D 8) (R 8) [66,257,40,192] 13 := by
  apply FastRouting.sound _ _ [66,257,40,192] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20566 c20566
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20566_5
  · exact m20566_33
  · exact m20566_36
  · exact u11938
  · exact u11939
  · exact u11940

theorem m20567_9 : Upper (D 8) (R 8) [66,257,48,68,9] 13 :=
  permutation_upper _ _ _ [66,257,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11838

theorem m20567_33 : Upper (D 8) (R 8) [66,257,48,68,33] 13 :=
  permutation_upper _ _ _ [66,257,33,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11881

theorem m20567_40 : Upper (D 8) (R 8) [66,257,48,68,40] 13 :=
  permutation_upper _ _ _ [66,257,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11903

theorem m20567_129 : Upper (D 8) (R 8) [66,257,48,68,129] 13 :=
  permutation_upper _ _ _ [66,257,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11916

theorem m20567_136 : Upper (D 8) (R 8) [66,257,48,68,136] 13 :=
  permutation_upper _ _ _ [66,257,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11927

theorem m20567_160 : Upper (D 8) (R 8) [66,257,48,68,160] 13 :=
  permutation_upper _ _ _ [66,257,40,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11933

def r20567 : Route 9 := (fun mask => (mask,id))

def c20567 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20567 : Upper (D 8) (R 8) [66,257,48,68] 13 := by
  apply FastRouting.sound _ _ [66,257,48,68] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20567 c20567
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20567_9
  · exact m20567_33
  · exact m20567_40
  · exact m20567_129
  · exact m20567_136
  · exact m20567_160

theorem m20568_5 : Upper (D 8) (R 8) [66,257,48,96,5] 13 :=
  permutation_upper _ _ _ [66,257,9,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11831

theorem m20568_9 : Upper (D 8) (R 8) [66,257,48,96,9] 13 :=
  permutation_upper _ _ _ [66,257,9,96,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11841

theorem m20568_12 : Upper (D 8) (R 8) [66,257,48,96,12] 13 :=
  permutation_upper _ _ _ [66,257,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11864

theorem m20568_33 : Upper (D 8) (R 8) [66,257,48,96,33] 13 :=
  permutation_upper _ _ _ [66,257,33,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11882

theorem m20568_36 : Upper (D 8) (R 8) [66,257,48,96,36] 13 :=
  permutation_upper _ _ _ [66,257,40,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11900

theorem m20568_40 : Upper (D 8) (R 8) [66,257,48,96,40] 13 :=
  permutation_upper _ _ _ [66,257,40,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11904

theorem m20568_129 : Upper (D 8) (R 8) [66,257,48,96,129] 13 :=
  permutation_upper _ _ _ [66,257,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11917

theorem m20568_132 : Upper (D 8) (R 8) [66,257,48,96,132] 13 :=
  permutation_upper _ _ _ [66,257,40,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11922

theorem m20568_136 : Upper (D 8) (R 8) [66,257,48,96,136] 13 :=
  permutation_upper _ _ _ [66,257,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11928

theorem m20568_160 : Upper (D 8) (R 8) [66,257,48,96,160] 13 :=
  permutation_upper _ _ _ [66,257,40,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11934

def r20568 : Route 9 := (fun mask => (mask,id))

def c20568 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20568 : Upper (D 8) (R 8) [66,257,48,96] 13 := by
  apply FastRouting.sound _ _ [66,257,48,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20568 c20568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20568_5
  · exact m20568_9
  · exact m20568_12
  · exact m20568_33
  · exact m20568_36
  · exact m20568_40
  · exact m20568_129
  · exact m20568_132
  · exact m20568_136
  · exact m20568_160

theorem m20569_9 : Upper (D 8) (R 8) [66,257,48,132,9] 13 :=
  permutation_upper _ _ _ [66,257,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11847

theorem m20569_33 : Upper (D 8) (R 8) [66,257,48,132,33] 13 :=
  permutation_upper _ _ _ [66,257,33,36,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11883

theorem m20569_40 : Upper (D 8) (R 8) [66,257,48,132,40] 13 :=
  permutation_upper _ _ _ [66,257,40,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11905

theorem m20569_65 : Upper (D 8) (R 8) [66,257,48,132,65] 13 :=
  permutation_upper _ _ _ [66,257,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11908

theorem m20569_72 : Upper (D 8) (R 8) [66,257,48,132,72] 13 :=
  permutation_upper _ _ _ [66,257,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11912

theorem m20569_96 : Upper (D 8) (R 8) [66,257,48,132,96] 13 :=
  permutation_upper _ _ _ [66,257,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11914

theorem m20569_129 : Upper (D 8) (R 8) [66,257,48,132,129] 13 :=
  permutation_upper _ _ _ [66,257,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11918

theorem m20569_136 : Upper (D 8) (R 8) [66,257,48,132,136] 13 :=
  permutation_upper _ _ _ [66,257,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11930

theorem m20569_160 : Upper (D 8) (R 8) [66,257,48,132,160] 13 :=
  permutation_upper _ _ _ [66,257,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11935

theorem m20569_192 : Upper (D 8) (R 8) [66,257,48,132,192] 13 :=
  permutation_upper _ _ _ [66,257,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11939

def r20569 : Route 9 := (fun mask => (mask,id))

def c20569 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20569 : Upper (D 8) (R 8) [66,257,48,132] 13 := by
  apply FastRouting.sound _ _ [66,257,48,132] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20569 c20569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20569_9
  · exact m20569_33
  · exact m20569_40
  · exact m20569_65
  · exact m20569_72
  · exact m20569_96
  · exact m20569_129
  · exact m20569_136
  · exact m20569_160
  · exact m20569_192

theorem m20570_5 : Upper (D 8) (R 8) [66,257,48,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11832

theorem m20570_9 : Upper (D 8) (R 8) [66,257,48,160,9] 13 :=
  permutation_upper _ _ _ [66,257,9,160,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11850

theorem m20570_12 : Upper (D 8) (R 8) [66,257,48,160,12] 13 :=
  permutation_upper _ _ _ [66,257,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11866

theorem m20570_33 : Upper (D 8) (R 8) [66,257,48,160,33] 13 :=
  permutation_upper _ _ _ [66,257,33,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11884

theorem m20570_36 : Upper (D 8) (R 8) [66,257,48,160,36] 13 :=
  permutation_upper _ _ _ [66,257,40,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11901

theorem m20570_40 : Upper (D 8) (R 8) [66,257,48,160,40] 13 :=
  permutation_upper _ _ _ [66,257,40,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11906

theorem m20570_65 : Upper (D 8) (R 8) [66,257,48,160,65] 13 :=
  permutation_upper _ _ _ [66,257,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11909

theorem m20570_68 : Upper (D 8) (R 8) [66,257,48,160,68] 13 :=
  permutation_upper _ _ _ [66,257,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11910

theorem m20570_72 : Upper (D 8) (R 8) [66,257,48,160,72] 13 :=
  permutation_upper _ _ _ [66,257,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11913

theorem m20570_96 : Upper (D 8) (R 8) [66,257,48,160,96] 13 :=
  permutation_upper _ _ _ [66,257,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11915

theorem m20570_129 : Upper (D 8) (R 8) [66,257,48,160,129] 13 :=
  permutation_upper _ _ _ [66,257,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11919

theorem m20570_132 : Upper (D 8) (R 8) [66,257,48,160,132] 13 :=
  permutation_upper _ _ _ [66,257,40,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11924

theorem m20570_136 : Upper (D 8) (R 8) [66,257,48,160,136] 13 :=
  permutation_upper _ _ _ [66,257,40,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11931

theorem m20570_160 : Upper (D 8) (R 8) [66,257,48,160,160] 13 :=
  permutation_upper _ _ _ [66,257,40,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11936

theorem m20570_192 : Upper (D 8) (R 8) [66,257,48,160,192] 13 :=
  permutation_upper _ _ _ [66,257,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11940

def r20570 : Route 9 := (fun mask => (mask,id))

def c20570 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20570 : Upper (D 8) (R 8) [66,257,48,160] 13 := by
  apply FastRouting.sound _ _ [66,257,48,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r20570 c20570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20570_5
  · exact m20570_9
  · exact m20570_12
  · exact m20570_33
  · exact m20570_36
  · exact m20570_40
  · exact m20570_65
  · exact m20570_68
  · exact m20570_72
  · exact m20570_96
  · exact m20570_129
  · exact m20570_132
  · exact m20570_136
  · exact m20570_160
  · exact m20570_192

theorem m20571_5 : Upper (D 8) (R 8) [66,257,48,192,5] 13 :=
  permutation_upper _ _ _ [66,257,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11833

theorem m20571_9 : Upper (D 8) (R 8) [66,257,48,192,9] 13 :=
  permutation_upper _ _ _ [66,257,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11855

theorem m20571_12 : Upper (D 8) (R 8) [66,257,48,192,12] 13 :=
  permutation_upper _ _ _ [66,257,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11867

theorem m20571_33 : Upper (D 8) (R 8) [66,257,48,192,33] 13 :=
  permutation_upper _ _ _ [66,257,33,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11885

theorem m20571_36 : Upper (D 8) (R 8) [66,257,48,192,36] 13 :=
  permutation_upper _ _ _ [66,257,40,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11902

theorem m20571_40 : Upper (D 8) (R 8) [66,257,48,192,40] 13 :=
  permutation_upper _ _ _ [66,257,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11907

theorem m20571_129 : Upper (D 8) (R 8) [66,257,48,192,129] 13 :=
  permutation_upper _ _ _ [66,257,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11920

theorem m20571_132 : Upper (D 8) (R 8) [66,257,48,192,132] 13 :=
  permutation_upper _ _ _ [66,257,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11925

theorem m20571_136 : Upper (D 8) (R 8) [66,257,48,192,136] 13 :=
  permutation_upper _ _ _ [66,257,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11932

theorem m20571_160 : Upper (D 8) (R 8) [66,257,48,192,160] 13 :=
  permutation_upper _ _ _ [66,257,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11937

def r20571 : Route 9 := (fun mask => (mask,id))

def c20571 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20571 : Upper (D 8) (R 8) [66,257,48,192] 13 := by
  apply FastRouting.sound _ _ [66,257,48,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20571 c20571
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20571_5
  · exact m20571_9
  · exact m20571_12
  · exact m20571_33
  · exact m20571_36
  · exact m20571_40
  · exact m20571_129
  · exact m20571_132
  · exact m20571_136
  · exact m20571_160

def b20572 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 69 140 184 184 248 184 440), lower := (rows 67 259 69 140 16 32 64 128 256), losses := [] }

theorem u20572 : Upper (D 8) (R 8) [66,257,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20573 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 69 168 188 188 252 188 444), lower := (rows 67 259 69 168 16 32 64 128 256), losses := [] }

theorem u20573 : Upper (D 8) (R 8) [66,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20574 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 76 137 180 180 244 180 436), lower := (rows 67 259 76 137 16 32 64 128 256), losses := [] }

theorem u20574 : Upper (D 8) (R 8) [66,257,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20575 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 76 140 177 177 241 177 433), lower := (rows 67 259 76 140 16 32 64 128 256), losses := [] }

theorem u20575 : Upper (D 8) (R 8) [66,257,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20576_5 : Upper (D 8) (R 8) [66,257,72,144,5] 13 :=
  permutation_upper _ _ _ [66,257,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11839

theorem m20576_33 : Upper (D 8) (R 8) [66,257,72,144,33] 13 :=
  permutation_upper _ _ _ [66,257,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11892

theorem m20576_36 : Upper (D 8) (R 8) [66,257,72,144,36] 13 :=
  permutation_upper _ _ _ [66,257,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11912

def r20576 : Route 9 := (fun mask => (mask,id))

def c20576 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20576 : Upper (D 8) (R 8) [66,257,72,144] 13 := by
  apply FastRouting.sound _ _ [66,257,72,144] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20576 c20576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20576_5
  · exact m20576_33
  · exact m20576_36
  · exact u11945
  · exact u11946
  · exact u11947

theorem m20577_5 : Upper (D 8) (R 8) [66,257,72,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11840

theorem m20577_33 : Upper (D 8) (R 8) [66,257,72,160,33] 13 :=
  permutation_upper _ _ _ [66,257,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11893

theorem m20577_36 : Upper (D 8) (R 8) [66,257,72,160,36] 13 :=
  permutation_upper _ _ _ [66,257,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11913

def r20577 : Route 9 := (fun mask => (mask,id))

def c20577 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20577 : Upper (D 8) (R 8) [66,257,72,160] 13 := by
  apply FastRouting.sound _ _ [66,257,72,160] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20577 c20577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20577_5
  · exact m20577_33
  · exact m20577_36
  · exact u11948
  · exact u11949
  · exact u11950

theorem m20578_9 : Upper (D 8) (R 8) [66,257,80,132,9] 13 :=
  permutation_upper _ _ _ [66,257,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11848

theorem m20578_33 : Upper (D 8) (R 8) [66,257,80,132,33] 13 :=
  permutation_upper _ _ _ [66,257,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11890

theorem m20578_40 : Upper (D 8) (R 8) [66,257,80,132,40] 13 :=
  permutation_upper _ _ _ [66,257,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11927

theorem m20578_129 : Upper (D 8) (R 8) [66,257,80,132,129] 13 :=
  permutation_upper _ _ _ [66,257,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11942

theorem m20578_136 : Upper (D 8) (R 8) [66,257,80,132,136] 13 :=
  permutation_upper _ _ _ [66,257,72,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11946

theorem m20578_160 : Upper (D 8) (R 8) [66,257,80,132,160] 13 :=
  permutation_upper _ _ _ [66,257,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11949

def r20578 : Route 9 := (fun mask => (mask,id))

def c20578 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20578 : Upper (D 8) (R 8) [66,257,80,132] 13 := by
  apply FastRouting.sound _ _ [66,257,80,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20578 c20578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20578_9
  · exact m20578_33
  · exact m20578_40
  · exact m20578_129
  · exact m20578_136
  · exact m20578_160

theorem m20579_5 : Upper (D 8) (R 8) [66,257,80,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11837

theorem m20579_9 : Upper (D 8) (R 8) [66,257,80,160,9] 13 :=
  permutation_upper _ _ _ [66,257,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11851

theorem m20579_12 : Upper (D 8) (R 8) [66,257,80,160,12] 13 :=
  permutation_upper _ _ _ [66,257,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11870

theorem m20579_33 : Upper (D 8) (R 8) [66,257,80,160,33] 13 :=
  permutation_upper _ _ _ [66,257,33,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11891

theorem m20579_36 : Upper (D 8) (R 8) [66,257,80,160,36] 13 :=
  permutation_upper _ _ _ [66,257,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11910

theorem m20579_40 : Upper (D 8) (R 8) [66,257,80,160,40] 13 :=
  permutation_upper _ _ _ [66,257,40,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11933

theorem m20579_129 : Upper (D 8) (R 8) [66,257,80,160,129] 13 :=
  permutation_upper _ _ _ [66,257,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11943

theorem m20579_132 : Upper (D 8) (R 8) [66,257,80,160,132] 13 :=
  permutation_upper _ _ _ [66,257,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11944

theorem m20579_136 : Upper (D 8) (R 8) [66,257,80,160,136] 13 :=
  permutation_upper _ _ _ [66,257,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11947

theorem m20579_160 : Upper (D 8) (R 8) [66,257,80,160,160] 13 :=
  permutation_upper _ _ _ [66,257,72,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11950

def r20579 : Route 9 := (fun mask => (mask,id))

def c20579 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20579 : Upper (D 8) (R 8) [66,257,80,160] 13 := by
  apply FastRouting.sound _ _ [66,257,80,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20579 c20579
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20579_5
  · exact m20579_9
  · exact m20579_12
  · exact m20579_33
  · exact m20579_36
  · exact m20579_40
  · exact m20579_129
  · exact m20579_132
  · exact m20579_136
  · exact m20579_160

#print axioms u20579
end Delivery.IrregularNine14.P08
