import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0272
import IrregularNine14P08C0273
import IrregularNine14P08C0274
import IrregularNine14P08C0275

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22620 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22620 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22620 : Upper (D 8) (R 8) [258,36,24,33] 13 := by
  apply FastRouting.sound _ _ [258,36,24,33] 13 (by decide) (choices 2) [33,65,96,192] r22620 c22620
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16346
  · exact u16347
  · exact u16348
  · exact u16349

theorem m22621_33 : Upper (D 8) (R 8) [258,36,24,65,33] 13 :=
  permutation_upper _ _ _ [258,36,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16347

def r22621 : Route 9 := (fun mask => (mask,id))

def c22621 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22621 : Upper (D 8) (R 8) [258,36,24,65] 13 := by
  apply FastRouting.sound _ _ [258,36,24,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22621 c22621
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22621_33
  · exact u16350
  · exact u16351
  · exact u16352
  · exact u16353
  · exact u16354

theorem m22622_33 : Upper (D 8) (R 8) [258,36,24,96,33] 13 :=
  permutation_upper _ _ _ [258,36,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16348

theorem m22622_65 : Upper (D 8) (R 8) [258,36,24,96,65] 13 :=
  permutation_upper _ _ _ [258,36,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16351

theorem m22622_129 : Upper (D 8) (R 8) [258,36,24,96,129] 13 :=
  permutation_upper _ _ _ [258,36,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16353

def r22622 : Route 9 := (fun mask => (mask,id))

def c22622 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22622 : Upper (D 8) (R 8) [258,36,24,96] 13 := by
  apply FastRouting.sound _ _ [258,36,24,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22622 c22622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22622_33
  · exact m22622_65
  · exact u16355
  · exact m22622_129
  · exact u16356
  · exact u16357

theorem m22623_33 : Upper (D 8) (R 8) [258,36,24,192,33] 13 :=
  permutation_upper _ _ _ [258,36,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16349

theorem m22623_65 : Upper (D 8) (R 8) [258,36,24,192,65] 13 :=
  permutation_upper _ _ _ [258,36,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16354

theorem m22623_96 : Upper (D 8) (R 8) [258,36,24,192,96] 13 :=
  permutation_upper _ _ _ [258,36,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16357

def r22623 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22623 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22623 : Upper (D 8) (R 8) [258,36,24,192] 13 := by
  apply FastRouting.sound _ _ [258,36,24,192] 13 (by decide) (choices 2) [33,65,96,192] r22623 c22623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22623_33
  · exact m22623_65
  · exact m22623_96
  · exact u16358

def b22624 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 25 248 232 232 232 488), lower := (rows 259 38 69 25 16 32 64 128 256), losses := [] }

theorem u22624 : Upper (D 8) (R 8) [258,36,65,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22625 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 41 248 248 248 248 504), lower := (rows 259 38 69 41 16 32 64 128 256), losses := [] }

theorem u22625 : Upper (D 8) (R 8) [258,36,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22626_9 : Upper (D 8) (R 8) [258,36,65,48,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16359

theorem m22626_33 : Upper (D 8) (R 8) [258,36,65,48,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16365

def r22626 : Route 9 := (fun mask => (mask,id))

def c22626 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22626 : Upper (D 8) (R 8) [258,36,65,48] 13 := by
  apply FastRouting.sound _ _ [258,36,65,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22626 c22626
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22626_9
  · exact m22626_33
  · exact u16371
  · exact u16372
  · exact u16373
  · exact u16374
  · exact u16375
  · exact u16376
  · exact u16377
  · exact u16378

def b22627 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 184 184 248 184 440), lower := (rows 259 38 69 73 16 32 64 128 256), losses := [] }

theorem u22627 : Upper (D 8) (R 8) [258,36,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22628_9 : Upper (D 8) (R 8) [258,36,65,80,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16360

theorem m22628_33 : Upper (D 8) (R 8) [258,36,65,80,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16366

theorem m22628_40 : Upper (D 8) (R 8) [258,36,65,80,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16373

def r22628 : Route 9 := (fun mask => (mask,id))

def c22628 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22628 : Upper (D 8) (R 8) [258,36,65,80] 13 := by
  apply FastRouting.sound _ _ [258,36,65,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22628 c22628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22628_9
  · exact m22628_33
  · exact m22628_40
  · exact u16381
  · exact u16382
  · exact u16383

theorem m22629_9 : Upper (D 8) (R 8) [258,36,65,96,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16361

theorem m22629_33 : Upper (D 8) (R 8) [258,36,65,96,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16367

theorem m22629_40 : Upper (D 8) (R 8) [258,36,65,96,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16374

def r22629 : Route 9 := (fun mask => (mask,id))

def c22629 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22629 : Upper (D 8) (R 8) [258,36,65,96] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22629 c22629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22629_9
  · exact m22629_33
  · exact m22629_40
  · exact u16384
  · exact u16385
  · exact u16386

def b22630 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 137 248 248 248 248 504), lower := (rows 259 38 69 137 16 32 64 128 256), losses := [] }

theorem u22630 : Upper (D 8) (R 8) [258,36,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22631_9 : Upper (D 8) (R 8) [258,36,65,144,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16362

theorem m22631_33 : Upper (D 8) (R 8) [258,36,65,144,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16368

theorem m22631_40 : Upper (D 8) (R 8) [258,36,65,144,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16376

theorem m22631_65 : Upper (D 8) (R 8) [258,36,65,144,65] 13 :=
  permutation_upper _ _ _ [258,36,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16379

theorem m22631_72 : Upper (D 8) (R 8) [258,36,65,144,72] 13 :=
  permutation_upper _ _ _ [258,36,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16382

theorem m22631_96 : Upper (D 8) (R 8) [258,36,65,144,96] 13 :=
  permutation_upper _ _ _ [258,36,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16385

theorem m22631_129 : Upper (D 8) (R 8) [258,36,65,144,129] 13 :=
  permutation_upper _ _ _ [258,36,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16387

def r22631 : Route 9 := (fun mask => (mask,id))

def c22631 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22631 : Upper (D 8) (R 8) [258,36,65,144] 13 := by
  apply FastRouting.sound _ _ [258,36,65,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22631 c22631
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22631_9
  · exact m22631_33
  · exact m22631_40
  · exact m22631_65
  · exact m22631_72
  · exact m22631_96
  · exact m22631_129
  · exact u16390
  · exact u16391
  · exact u16392

theorem m22632_9 : Upper (D 8) (R 8) [258,36,65,160,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16363

theorem m22632_33 : Upper (D 8) (R 8) [258,36,65,160,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16369

theorem m22632_40 : Upper (D 8) (R 8) [258,36,65,160,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16377

theorem m22632_65 : Upper (D 8) (R 8) [258,36,65,160,65] 13 :=
  permutation_upper _ _ _ [258,36,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16380

theorem m22632_72 : Upper (D 8) (R 8) [258,36,65,160,72] 13 :=
  permutation_upper _ _ _ [258,36,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16383

theorem m22632_96 : Upper (D 8) (R 8) [258,36,65,160,96] 13 :=
  permutation_upper _ _ _ [258,36,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16386

theorem m22632_129 : Upper (D 8) (R 8) [258,36,65,160,129] 13 :=
  permutation_upper _ _ _ [258,36,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16388

theorem m22632_136 : Upper (D 8) (R 8) [258,36,65,160,136] 13 :=
  permutation_upper _ _ _ [258,36,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16391

def r22632 : Route 9 := (fun mask => (mask,id))

def c22632 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22632 : Upper (D 8) (R 8) [258,36,65,160] 13 := by
  apply FastRouting.sound _ _ [258,36,65,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22632 c22632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22632_9
  · exact m22632_33
  · exact m22632_40
  · exact m22632_65
  · exact m22632_72
  · exact m22632_96
  · exact m22632_129
  · exact m22632_136
  · exact u16393
  · exact u16394

theorem m22633_9 : Upper (D 8) (R 8) [258,36,65,192,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16364

theorem m22633_33 : Upper (D 8) (R 8) [258,36,65,192,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16370

theorem m22633_40 : Upper (D 8) (R 8) [258,36,65,192,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16378

theorem m22633_129 : Upper (D 8) (R 8) [258,36,65,192,129] 13 :=
  permutation_upper _ _ _ [258,36,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16389

theorem m22633_136 : Upper (D 8) (R 8) [258,36,65,192,136] 13 :=
  permutation_upper _ _ _ [258,36,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16392

theorem m22633_160 : Upper (D 8) (R 8) [258,36,65,192,160] 13 :=
  permutation_upper _ _ _ [258,36,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16394

def r22633 : Route 9 := (fun mask => (mask,id))

def c22633 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22633 : Upper (D 8) (R 8) [258,36,65,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22633 c22633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22633_9
  · exact m22633_33
  · exact m22633_40
  · exact m22633_129
  · exact m22633_136
  · exact m22633_160

def r22634 : Route 9 := (fun mask => (mask,id))

def c22634 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22634 : Upper (D 8) (R 8) [258,36,72,17] 13 := by
  apply FastRouting.sound _ _ [258,36,72,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22634 c22634
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16395
  · exact u16396
  · exact u16397
  · exact u16398
  · exact u16399
  · exact u16400

def r22635 : Route 9 := (fun mask => (mask,id))

def c22635 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22635 : Upper (D 8) (R 8) [258,36,72,33] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22635 c22635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16401
  · exact u16402
  · exact u16403
  · exact u16404
  · exact u16405
  · exact u16406

def r22636 : Route 9 := (fun mask => (mask,id))

def c22636 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22636 : Upper (D 8) (R 8) [258,36,72,48] 13 := by
  apply FastRouting.sound _ _ [258,36,72,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22636 c22636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16407
  · exact u16408
  · exact u16409
  · exact u16410
  · exact u16411
  · exact u16412

def b22637 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 73 177 177 241 177 433), lower := (rows 259 38 76 73 16 32 64 128 256), losses := [] }

theorem u22637 : Upper (D 8) (R 8) [258,36,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22638 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 88 177 161 225 161 417), lower := (rows 259 38 76 88 16 32 64 128 256), losses := [] }

theorem u22638 : Upper (D 8) (R 8) [258,36,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22639 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 104 177 177 241 177 433), lower := (rows 259 38 76 104 16 32 64 128 256), losses := [] }

theorem u22639 : Upper (D 8) (R 8) [258,36,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22640 : Route 9 := (fun mask => (mask,id))

def c22640 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22640 : Upper (D 8) (R 8) [258,36,72,129] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22640 c22640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16413
  · exact u16414
  · exact u16415
  · exact u16416
  · exact u16417
  · exact u16418

def r22641 : Route 9 := (fun mask => (mask,id))

def c22641 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22641 : Upper (D 8) (R 8) [258,36,72,144] 13 := by
  apply FastRouting.sound _ _ [258,36,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22641 c22641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16419
  · exact u16420
  · exact u16421
  · exact u16422
  · exact u16423
  · exact u16424

def r22642 : Route 9 := (fun mask => (mask,id))

def c22642 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22642 : Upper (D 8) (R 8) [258,36,72,160] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22642 c22642
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16425
  · exact u16426
  · exact u16427
  · exact u16428
  · exact u16429
  · exact u16430

def b22643 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 200 177 177 241 177 433), lower := (rows 259 38 76 200 16 32 64 128 256), losses := [] }

theorem u22643 : Upper (D 8) (R 8) [258,36,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22644 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22644 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22644 : Upper (D 8) (R 8) [258,36,192,17] 13 := by
  apply FastRouting.sound _ _ [258,36,192,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22644 c22644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16431
  · exact u16432
  · exact u16433
  · exact u16434
  · exact u16435
  · exact u16436
  · exact u16437

theorem m22645_9 : Upper (D 8) (R 8) [258,36,192,33,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16432

def r22645 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22645 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22645 : Upper (D 8) (R 8) [258,36,192,33] 13 := by
  apply FastRouting.sound _ _ [258,36,192,33] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22645 c22645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22645_9
  · exact u16438
  · exact u16439
  · exact u16440
  · exact u16441
  · exact u16442
  · exact u16443

theorem m22646_9 : Upper (D 8) (R 8) [258,36,192,48,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16433

theorem m22646_33 : Upper (D 8) (R 8) [258,36,192,48,33] 13 :=
  permutation_upper _ _ _ [258,36,192,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16439

def r22646 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22646 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22646 : Upper (D 8) (R 8) [258,36,192,48] 13 := by
  apply FastRouting.sound _ _ [258,36,192,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22646 c22646
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22646_9
  · exact m22646_33
  · exact u16444
  · exact u16445
  · exact u16446
  · exact u16447
  · exact u16448

def b22647 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 73 185 185 249 185 441), lower := (rows 259 38 196 73 16 32 64 128 256), losses := [] }

theorem u22647 : Upper (D 8) (R 8) [258,36,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22648_9 : Upper (D 8) (R 8) [258,36,192,80,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16435

theorem m22648_33 : Upper (D 8) (R 8) [258,36,192,80,33] 13 :=
  permutation_upper _ _ _ [258,36,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16441

theorem m22648_40 : Upper (D 8) (R 8) [258,36,192,80,40] 13 :=
  permutation_upper _ _ _ [258,36,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16446

theorem m22648_129 : Upper (D 8) (R 8) [258,36,192,80,129] 13 :=
  permutation_upper _ _ _ [258,36,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16449

def r22648 : Route 9 := (fun mask => (mask,id))

def c22648 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22648 : Upper (D 8) (R 8) [258,36,192,80] 13 := by
  apply FastRouting.sound _ _ [258,36,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22648 c22648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22648_9
  · exact m22648_33
  · exact m22648_40
  · exact m22648_129
  · exact u16451
  · exact u16452

theorem m22649_9 : Upper (D 8) (R 8) [258,36,192,96,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16436

theorem m22649_33 : Upper (D 8) (R 8) [258,36,192,96,33] 13 :=
  permutation_upper _ _ _ [258,36,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16442

theorem m22649_40 : Upper (D 8) (R 8) [258,36,192,96,40] 13 :=
  permutation_upper _ _ _ [258,36,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16447

theorem m22649_129 : Upper (D 8) (R 8) [258,36,192,96,129] 13 :=
  permutation_upper _ _ _ [258,36,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16450

theorem m22649_136 : Upper (D 8) (R 8) [258,36,192,96,136] 13 :=
  permutation_upper _ _ _ [258,36,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16452

def r22649 : Route 9 := (fun mask => (mask,id))

def c22649 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22649 : Upper (D 8) (R 8) [258,36,192,96] 13 := by
  apply FastRouting.sound _ _ [258,36,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22649 c22649
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22649_9
  · exact m22649_33
  · exact m22649_40
  · exact m22649_129
  · exact m22649_136
  · exact u16453

def b22650 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 196 200 57 57 121 185 313), lower := (rows 259 38 196 200 16 32 64 128 256), losses := [] }

theorem u22650 : Upper (D 8) (R 8) [258,36,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22651 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 28 240 224 224 224 480), lower := (rows 259 67 13 28 16 32 64 128 256), losses := [] }

theorem u22651 : Upper (D 8) (R 8) [258,65,9,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22652 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 44 240 240 240 240 496), lower := (rows 259 67 13 44 16 32 64 128 256), losses := [] }

theorem u22652 : Upper (D 8) (R 8) [258,65,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22653 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 13 76 176 176 240 176 432), lower := (rows 259 67 13 76 16 32 64 128 256), losses := [] }

theorem u22653 : Upper (D 8) (R 8) [258,65,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22654 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 104 180 180 244 180 436), lower := (rows 259 67 13 104 16 32 64 128 256), losses := [] }

theorem u22654 : Upper (D 8) (R 8) [258,65,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22655 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 140 240 240 240 240 496), lower := (rows 259 67 13 140 16 32 64 128 256), losses := [] }

theorem u22655 : Upper (D 8) (R 8) [258,65,9,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22656 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 168 244 244 244 244 500), lower := (rows 259 67 13 168 16 32 64 128 256), losses := [] }

theorem u22656 : Upper (D 8) (R 8) [258,65,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22657 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 200 180 180 244 180 436), lower := (rows 259 67 13 200 16 32 64 128 256), losses := [] }

theorem u22657 : Upper (D 8) (R 8) [258,65,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22658 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 21 44 248 232 232 232 488), lower := (rows 259 67 21 44 16 32 64 128 256), losses := [] }

theorem u22658 : Upper (D 8) (R 8) [258,65,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22659 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 21 76 184 168 232 168 424), lower := (rows 259 67 21 76 16 32 64 128 256), losses := [] }

theorem u22659 : Upper (D 8) (R 8) [258,65,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22660 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 21 104 188 172 236 172 428), lower := (rows 259 67 21 104 16 32 64 128 256), losses := [] }

theorem u22660 : Upper (D 8) (R 8) [258,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22661 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 21 140 248 232 232 232 488), lower := (rows 259 67 21 140 16 32 64 128 256), losses := [] }

theorem u22661 : Upper (D 8) (R 8) [258,65,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22662 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 21 168 252 236 236 236 492), lower := (rows 259 67 21 168 16 32 64 128 256), losses := [] }

theorem u22662 : Upper (D 8) (R 8) [258,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22663 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 21 200 188 172 236 172 428), lower := (rows 259 67 21 200 16 32 64 128 256), losses := [] }

theorem u22663 : Upper (D 8) (R 8) [258,65,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22664 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 41 244 228 228 228 484), lower := (rows 259 67 28 41 16 32 64 128 256), losses := [] }

theorem u22664 : Upper (D 8) (R 8) [258,65,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22665_33 : Upper (D 8) (R 8) [258,65,24,36,33] 13 :=
  permutation_upper _ _ _ [258,65,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16484

def r22665 : Route 9 := (fun mask => (mask,id))

def c22665 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22665 : Upper (D 8) (R 8) [258,65,24,36] 13 := by
  apply FastRouting.sound _ _ [258,65,24,36] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22665 c22665
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22665_33
  · exact u16489
  · exact u16490
  · exact u16491
  · exact u16492
  · exact u16493

def b22666 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 67 28 73 180 164 228 164 420), lower := (rows 259 67 28 73 16 32 64 128 256), losses := [] }

theorem u22666 : Upper (D 8) (R 8) [258,65,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22667 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 28 76 177 161 225 161 417), lower := (rows 259 67 28 76 16 32 64 128 256), losses := [] }

theorem u22667 : Upper (D 8) (R 8) [258,65,24,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22668_5 : Upper (D 8) (R 8) [258,65,24,96,5] 13 :=
  permutation_upper _ _ _ [258,65,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16454

theorem m22668_33 : Upper (D 8) (R 8) [258,65,24,96,33] 13 :=
  permutation_upper _ _ _ [258,65,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16485

theorem m22668_36 : Upper (D 8) (R 8) [258,65,24,96,36] 13 :=
  permutation_upper _ _ _ [258,65,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16490

def r22668 : Route 9 := (fun mask => (mask,id))

def c22668 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22668 : Upper (D 8) (R 8) [258,65,24,96] 13 := by
  apply FastRouting.sound _ _ [258,65,24,96] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22668 c22668
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22668_5
  · exact m22668_33
  · exact m22668_36
  · exact u16497
  · exact u16498
  · exact u16499

def b22669 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 137 244 228 228 228 484), lower := (rows 259 67 28 137 16 32 64 128 256), losses := [] }

theorem u22669 : Upper (D 8) (R 8) [258,65,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22670_33 : Upper (D 8) (R 8) [258,65,24,132,33] 13 :=
  permutation_upper _ _ _ [258,65,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16486

theorem m22670_65 : Upper (D 8) (R 8) [258,65,24,132,65] 13 :=
  permutation_upper _ _ _ [258,65,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16494

theorem m22670_96 : Upper (D 8) (R 8) [258,65,24,132,96] 13 :=
  permutation_upper _ _ _ [258,65,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16498

theorem m22670_129 : Upper (D 8) (R 8) [258,65,24,132,129] 13 :=
  permutation_upper _ _ _ [258,65,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16500

def r22670 : Route 9 := (fun mask => (mask,id))

def c22670 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22670 : Upper (D 8) (R 8) [258,65,24,132] 13 := by
  apply FastRouting.sound _ _ [258,65,24,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22670 c22670
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22670_33
  · exact m22670_65
  · exact m22670_96
  · exact m22670_129
  · exact u16503
  · exact u16504

theorem m22671_5 : Upper (D 8) (R 8) [258,65,24,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16455

theorem m22671_33 : Upper (D 8) (R 8) [258,65,24,160,33] 13 :=
  permutation_upper _ _ _ [258,65,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16487

theorem m22671_36 : Upper (D 8) (R 8) [258,65,24,160,36] 13 :=
  permutation_upper _ _ _ [258,65,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16492

theorem m22671_65 : Upper (D 8) (R 8) [258,65,24,160,65] 13 :=
  permutation_upper _ _ _ [258,65,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16495

theorem m22671_68 : Upper (D 8) (R 8) [258,65,24,160,68] 13 :=
  permutation_upper _ _ _ [258,65,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16496

theorem m22671_96 : Upper (D 8) (R 8) [258,65,24,160,96] 13 :=
  permutation_upper _ _ _ [258,65,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16499

theorem m22671_129 : Upper (D 8) (R 8) [258,65,24,160,129] 13 :=
  permutation_upper _ _ _ [258,65,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16501

theorem m22671_132 : Upper (D 8) (R 8) [258,65,24,160,132] 13 :=
  permutation_upper _ _ _ [258,65,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16503

def r22671 : Route 9 := (fun mask => (mask,id))

def c22671 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22671 : Upper (D 8) (R 8) [258,65,24,160] 13 := by
  apply FastRouting.sound _ _ [258,65,24,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22671 c22671
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22671_5
  · exact m22671_33
  · exact m22671_36
  · exact m22671_65
  · exact m22671_68
  · exact m22671_96
  · exact m22671_129
  · exact m22671_132
  · exact u16505
  · exact u16506

theorem m22672_5 : Upper (D 8) (R 8) [258,65,24,192,5] 13 :=
  permutation_upper _ _ _ [258,65,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16456

theorem m22672_33 : Upper (D 8) (R 8) [258,65,24,192,33] 13 :=
  permutation_upper _ _ _ [258,65,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16488

theorem m22672_36 : Upper (D 8) (R 8) [258,65,24,192,36] 13 :=
  permutation_upper _ _ _ [258,65,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16493

theorem m22672_129 : Upper (D 8) (R 8) [258,65,24,192,129] 13 :=
  permutation_upper _ _ _ [258,65,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16502

theorem m22672_132 : Upper (D 8) (R 8) [258,65,24,192,132] 13 :=
  permutation_upper _ _ _ [258,65,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16504

theorem m22672_160 : Upper (D 8) (R 8) [258,65,24,192,160] 13 :=
  permutation_upper _ _ _ [258,65,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16506

def r22672 : Route 9 := (fun mask => (mask,id))

def c22672 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22672 : Upper (D 8) (R 8) [258,65,24,192] 13 := by
  apply FastRouting.sound _ _ [258,65,24,192] 13 (by decide) (choices 2) [5,33,36,129,132,160] r22672 c22672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22672_5
  · exact m22672_33
  · exact m22672_36
  · exact m22672_129
  · exact m22672_132
  · exact m22672_160

def b22673 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 44 248 248 248 248 504), lower := (rows 259 67 37 44 16 32 64 128 256), losses := [] }

theorem u22673 : Upper (D 8) (R 8) [258,65,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22674 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 76 184 184 248 184 440), lower := (rows 259 67 37 76 16 32 64 128 256), losses := [] }

theorem u22674 : Upper (D 8) (R 8) [258,65,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22675 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 104 188 188 252 188 444), lower := (rows 259 67 37 104 16 32 64 128 256), losses := [] }

theorem u22675 : Upper (D 8) (R 8) [258,65,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22676 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 140 248 248 248 248 504), lower := (rows 259 67 37 140 16 32 64 128 256), losses := [] }

theorem u22676 : Upper (D 8) (R 8) [258,65,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22677 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 168 252 252 252 252 508), lower := (rows 259 67 37 168 16 32 64 128 256), losses := [] }

theorem u22677 : Upper (D 8) (R 8) [258,65,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22678 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 200 188 188 252 188 444), lower := (rows 259 67 37 200 16 32 64 128 256), losses := [] }

theorem u22678 : Upper (D 8) (R 8) [258,65,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22679 : PairBound 9 := { available := 241, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 44 241 241 241 241 497), lower := (rows 259 67 44 44 16 32 64 128 256), losses := [] }

theorem u22679 : Upper (D 8) (R 8) [258,65,40,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u22679
end Delivery.IrregularNine14.P08
