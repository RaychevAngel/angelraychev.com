import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0639
import IrregularNine14P07C0640
import IrregularNine14P07C0641
import IrregularNine14P07C0642
import IrregularNine14P07C0643

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43200_3 : Upper (D 7) (R 7) [36,192,320,129,3] 13 :=
  permutation_upper _ _ _ [36,192,320,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38348

theorem m43200_9 : Upper (D 7) (R 7) [36,192,320,129,9] 13 :=
  permutation_upper _ _ _ [36,192,320,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38357

theorem m43200_10 : Upper (D 7) (R 7) [36,192,320,129,10] 13 :=
  permutation_upper _ _ _ [36,192,320,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38365

theorem m43200_33 : Upper (D 7) (R 7) [36,192,320,129,33] 13 :=
  permutation_upper _ _ _ [36,192,320,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38369

theorem m43200_34 : Upper (D 7) (R 7) [36,192,320,129,34] 13 :=
  permutation_upper _ _ _ [36,192,320,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38371

theorem m43200_40 : Upper (D 7) (R 7) [36,192,320,129,40] 13 :=
  permutation_upper _ _ _ [36,192,320,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38374

def r43200 : Route 9 := (fun mask => (mask,id))

def c43200 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43200 : Upper (D 7) (R 7) [36,192,320,129] 13 := by
  apply FastRouting.sound _ _ [36,192,320,129] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43200 c43200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43200_3
  · exact m43200_9
  · exact m43200_10
  · exact m43200_33
  · exact m43200_34
  · exact m43200_40

def b43201 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 37 194 324 138 59 59 123 187 315), lower := (rows 37 194 324 138 16 32 64 128 256), losses := [] }

theorem u43201 : Upper (D 7) (R 7) [36,192,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43202_3 : Upper (D 7) (R 7) [36,192,320,144,3] 13 :=
  permutation_upper _ _ _ [36,192,320,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38350

theorem m43202_9 : Upper (D 7) (R 7) [36,192,320,144,9] 13 :=
  permutation_upper _ _ _ [36,192,320,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38359

theorem m43202_10 : Upper (D 7) (R 7) [36,192,320,144,10] 13 :=
  permutation_upper _ _ _ [36,192,320,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38367

theorem m43202_33 : Upper (D 7) (R 7) [36,192,320,144,33] 13 :=
  permutation_upper _ _ _ [36,192,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38370

theorem m43202_34 : Upper (D 7) (R 7) [36,192,320,144,34] 13 :=
  permutation_upper _ _ _ [36,192,320,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38373

theorem m43202_40 : Upper (D 7) (R 7) [36,192,320,144,40] 13 :=
  permutation_upper _ _ _ [36,192,320,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38376

def r43202 : Route 9 := (fun mask => (mask,id))

def c43202 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43202 : Upper (D 7) (R 7) [36,192,320,144] 13 := by
  apply FastRouting.sound _ _ [36,192,320,144] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43202 c43202
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43202_3
  · exact m43202_9
  · exact m43202_10
  · exact m43202_33
  · exact m43202_34
  · exact m43202_40

theorem m43203_3 : Upper (D 7) (R 7) [36,192,320,160,3] 13 :=
  permutation_upper _ _ _ [36,192,320,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38351

theorem m43203_9 : Upper (D 7) (R 7) [36,192,320,160,9] 13 :=
  permutation_upper _ _ _ [36,192,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38360

theorem m43203_10 : Upper (D 7) (R 7) [36,192,320,160,10] 13 :=
  permutation_upper _ _ _ [36,192,320,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38368

def r43203 : Route 9 := (fun mask => (mask,id))

def c43203 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43203 : Upper (D 7) (R 7) [36,192,320,160] 13 := by
  apply FastRouting.sound _ _ [36,192,320,160] 13 (by decide) (choices 2) [3,9,10] r43203 c43203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43203_3
  · exact m43203_9
  · exact m43203_10

def r43204 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43204 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43204 : Upper (D 7) (R 7) [36,257,9,18] 13 := by
  apply FastRouting.sound _ _ [36,257,9,18] 13 (by decide) (choices 2) [34,66,96,192] r43204 c43204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38377
  · exact u38378
  · exact u38379
  · exact u38380

def b43205 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 259 13 42 210 242 210 210 466), lower := (rows 37 259 13 42 16 32 64 128 256), losses := [] }

theorem u43205 : Upper (D 7) (R 7) [36,257,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43206 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 259 13 56 210 226 194 194 450), lower := (rows 37 259 13 56 16 32 64 128 256), losses := [] }

theorem u43206 : Upper (D 7) (R 7) [36,257,9,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43207 : Route 9 := (fun mask => (mask,id))

def c43207 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43207 : Upper (D 7) (R 7) [36,257,9,66] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43207 c43207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38381
  · exact u38382
  · exact u38383
  · exact u38384
  · exact u38385
  · exact u38386

def r43208 : Route 9 := (fun mask => (mask,id))

def c43208 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43208 : Upper (D 7) (R 7) [36,257,9,80] 13 := by
  apply FastRouting.sound _ _ [36,257,9,80] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43208 c43208
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38387
  · exact u38388
  · exact u38389
  · exact u38390
  · exact u38391
  · exact u38392

def b43209 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 259 13 104 210 242 210 210 466), lower := (rows 37 259 13 104 16 32 64 128 256), losses := [] }

theorem u43209 : Upper (D 7) (R 7) [36,257,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43210 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43210 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43210 : Upper (D 7) (R 7) [36,257,9,192] 13 := by
  apply FastRouting.sound _ _ [36,257,9,192] 13 (by decide) (choices 2) [34,66,96,192] r43210 c43210
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38393
  · exact u38394
  · exact u38395
  · exact u38396

def b43211 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 37 259 14 11 240 240 240 240 496), lower := (rows 37 259 14 11 16 32 64 128 256), losses := [] }

theorem u43211 : Upper (D 7) (R 7) [36,257,10,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43212 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43212 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43212 : Upper (D 7) (R 7) [36,257,10,17] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17] 13 (by decide) (choices 2) [34,66,96,192] r43212 c43212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38397
  · exact u38398
  · exact u38399
  · exact u38400

def b43213 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 259 14 26 241 225 225 225 481), lower := (rows 37 259 14 26 16 32 64 128 256), losses := [] }

theorem u43213 : Upper (D 7) (R 7) [36,257,10,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43214 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 14 41 210 242 210 210 466), lower := (rows 37 259 14 41 16 32 64 128 256), losses := [] }

theorem u43214 : Upper (D 7) (R 7) [36,257,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43215 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 14 42 209 241 209 209 465), lower := (rows 37 259 14 42 16 32 64 128 256), losses := [] }

theorem u43215 : Upper (D 7) (R 7) [36,257,10,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43216 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43216 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43216 : Upper (D 7) (R 7) [36,257,10,48] 13 := by
  apply FastRouting.sound _ _ [36,257,10,48] 13 (by decide) (choices 2) [3,65,66,192] r43216 c43216
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38401
  · exact u38402
  · exact u38403
  · exact u38404

def r43217 : Route 9 := (fun mask => (mask,id))

def c43217 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43217 : Upper (D 7) (R 7) [36,257,10,65] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43217 c43217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38405
  · exact u38406
  · exact u38407
  · exact u38408
  · exact u38409
  · exact u38410

def b43218 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 259 14 74 241 241 241 241 497), lower := (rows 37 259 14 74 16 32 64 128 256), losses := [] }

theorem u43218 : Upper (D 7) (R 7) [36,257,10,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43219 : Route 9 := (fun mask => (mask,id))

def c43219 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43219 : Upper (D 7) (R 7) [36,257,10,80] 13 := by
  apply FastRouting.sound _ _ [36,257,10,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43219 c43219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38411
  · exact u38412
  · exact u38413
  · exact u38414
  · exact u38415
  · exact u38416
  · exact u38417
  · exact u38418
  · exact u38419
  · exact u38420

def r43220 : Route 9 := (fun mask => (mask,id))

def c43220 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43220 : Upper (D 7) (R 7) [36,257,10,96] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43220 c43220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38421
  · exact u38422
  · exact u38423
  · exact u38424
  · exact u38425
  · exact u38426

def r43221 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43221 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43221 : Upper (D 7) (R 7) [36,257,10,192] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43221 c43221
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38427
  · exact u38428
  · exact u38429
  · exact u38430
  · exact u38431
  · exact u38432
  · exact u38433

def b43222 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 28 11 242 226 226 226 482), lower := (rows 37 259 28 11 16 32 64 128 256), losses := [] }

theorem u43222 : Upper (D 7) (R 7) [36,257,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43223 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 28 41 210 226 194 194 450), lower := (rows 37 259 28 41 16 32 64 128 256), losses := [] }

theorem u43223 : Upper (D 7) (R 7) [36,257,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43224_3 : Upper (D 7) (R 7) [36,257,24,34,3] 13 :=
  permutation_upper _ _ _ [36,257,24,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38434

def r43224 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43224 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43224 : Upper (D 7) (R 7) [36,257,24,34] 13 := by
  apply FastRouting.sound _ _ [36,257,24,34] 13 (by decide) (choices 2) [3,65,66,192] r43224 c43224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m43224_3
  · exact u38440
  · exact u38441
  · exact u38442

theorem m43225_34 : Upper (D 7) (R 7) [36,257,24,65,34] 13 :=
  permutation_upper _ _ _ [36,257,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38440

def r43225 : Route 9 := (fun mask => (mask,id))

def c43225 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43225 : Upper (D 7) (R 7) [36,257,24,65] 13 := by
  apply FastRouting.sound _ _ [36,257,24,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43225 c43225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43225_34
  · exact u38443
  · exact u38444
  · exact u38445
  · exact u38446
  · exact u38447

theorem m43226_3 : Upper (D 7) (R 7) [36,257,24,66,3] 13 :=
  permutation_upper _ _ _ [36,257,24,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38435

theorem m43226_33 : Upper (D 7) (R 7) [36,257,24,66,33] 13 :=
  permutation_upper _ _ _ [36,257,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38438

theorem m43226_34 : Upper (D 7) (R 7) [36,257,24,66,34] 13 :=
  permutation_upper _ _ _ [36,257,24,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38441

theorem m43226_65 : Upper (D 7) (R 7) [36,257,24,66,65] 13 :=
  permutation_upper _ _ _ [36,257,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38443

theorem m43226_129 : Upper (D 7) (R 7) [36,257,24,66,129] 13 :=
  permutation_upper _ _ _ [36,257,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38445

def r43226 : Route 9 := (fun mask => (mask,id))

def c43226 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43226 : Upper (D 7) (R 7) [36,257,24,66] 13 := by
  apply FastRouting.sound _ _ [36,257,24,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43226 c43226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43226_3
  · exact m43226_33
  · exact m43226_34
  · exact m43226_65
  · exact u38448
  · exact u38449
  · exact m43226_129
  · exact u38450
  · exact u38451
  · exact u38452

theorem m43227_3 : Upper (D 7) (R 7) [36,257,24,96,3] 13 :=
  permutation_upper _ _ _ [36,257,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38436

theorem m43227_65 : Upper (D 7) (R 7) [36,257,24,96,65] 13 :=
  permutation_upper _ _ _ [36,257,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38444

theorem m43227_66 : Upper (D 7) (R 7) [36,257,24,96,66] 13 :=
  permutation_upper _ _ _ [36,257,24,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38449

theorem m43227_129 : Upper (D 7) (R 7) [36,257,24,96,129] 13 :=
  permutation_upper _ _ _ [36,257,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38446

theorem m43227_130 : Upper (D 7) (R 7) [36,257,24,96,130] 13 :=
  permutation_upper _ _ _ [36,257,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38451

def r43227 : Route 9 := (fun mask => (mask,id))

def c43227 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43227 : Upper (D 7) (R 7) [36,257,24,96] 13 := by
  apply FastRouting.sound _ _ [36,257,24,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43227 c43227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43227_3
  · exact m43227_65
  · exact m43227_66
  · exact m43227_129
  · exact m43227_130
  · exact u38453

theorem m43228_3 : Upper (D 7) (R 7) [36,257,24,192,3] 13 :=
  permutation_upper _ _ _ [36,257,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38437

theorem m43228_33 : Upper (D 7) (R 7) [36,257,24,192,33] 13 :=
  permutation_upper _ _ _ [36,257,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38439

theorem m43228_34 : Upper (D 7) (R 7) [36,257,24,192,34] 13 :=
  permutation_upper _ _ _ [36,257,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38442

theorem m43228_65 : Upper (D 7) (R 7) [36,257,24,192,65] 13 :=
  permutation_upper _ _ _ [36,257,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38447

theorem m43228_66 : Upper (D 7) (R 7) [36,257,24,192,66] 13 :=
  permutation_upper _ _ _ [36,257,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38452

theorem m43228_96 : Upper (D 7) (R 7) [36,257,24,192,96] 13 :=
  permutation_upper _ _ _ [36,257,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38453

def r43228 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43228 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43228 : Upper (D 7) (R 7) [36,257,24,192] 13 := by
  apply FastRouting.sound _ _ [36,257,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43228 c43228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43228_3
  · exact m43228_33
  · exact m43228_34
  · exact m43228_65
  · exact m43228_66
  · exact m43228_96
  · exact u38454

def r43229 : Route 9 := (fun mask => (mask,id))

def c43229 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43229 : Upper (D 7) (R 7) [36,257,65,18] 13 := by
  apply FastRouting.sound _ _ [36,257,65,18] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43229 c43229
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38455
  · exact u38456
  · exact u38457
  · exact u38458
  · exact u38459
  · exact u38460
  · exact u38461
  · exact u38462
  · exact u38463
  · exact u38464

theorem m43230_10 : Upper (D 7) (R 7) [36,257,65,34,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38456

def r43230 : Route 9 := (fun mask => (mask,id))

def c43230 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43230 : Upper (D 7) (R 7) [36,257,65,34] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34] 13 (by decide) (choices 2) [10,66,72,130,136,192] r43230 c43230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43230_10
  · exact u38465
  · exact u38466
  · exact u38467
  · exact u38468
  · exact u38469

theorem m43231_10 : Upper (D 7) (R 7) [36,257,65,48,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38457

def r43231 : Route 9 := (fun mask => (mask,id))

def c43231 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43231 : Upper (D 7) (R 7) [36,257,65,48] 13 := by
  apply FastRouting.sound _ _ [36,257,65,48] 13 (by decide) (choices 2) [10,66,72,130,136,192] r43231 c43231
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43231_10
  · exact u38470
  · exact u38471
  · exact u38472
  · exact u38473
  · exact u38474

theorem m43232_10 : Upper (D 7) (R 7) [36,257,65,66,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38458

theorem m43232_34 : Upper (D 7) (R 7) [36,257,65,66,34] 13 :=
  permutation_upper _ _ _ [36,257,65,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38465

theorem m43232_40 : Upper (D 7) (R 7) [36,257,65,66,40] 13 :=
  permutation_upper _ _ _ [36,257,65,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38470

def r43232 : Route 9 := (fun mask => (mask,id))

def c43232 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43232 : Upper (D 7) (R 7) [36,257,65,66] 13 := by
  apply FastRouting.sound _ _ [36,257,65,66] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43232 c43232
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43232_10
  · exact m43232_34
  · exact m43232_40
  · exact u38475
  · exact u38476
  · exact u38477

theorem m43233_10 : Upper (D 7) (R 7) [36,257,65,80,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38459

theorem m43233_34 : Upper (D 7) (R 7) [36,257,65,80,34] 13 :=
  permutation_upper _ _ _ [36,257,65,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38466

theorem m43233_40 : Upper (D 7) (R 7) [36,257,65,80,40] 13 :=
  permutation_upper _ _ _ [36,257,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38471

def r43233 : Route 9 := (fun mask => (mask,id))

def c43233 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43233 : Upper (D 7) (R 7) [36,257,65,80] 13 := by
  apply FastRouting.sound _ _ [36,257,65,80] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43233 c43233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43233_10
  · exact m43233_34
  · exact m43233_40
  · exact u38478
  · exact u38479
  · exact u38480

def b43234 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 104 154 186 218 154 410), lower := (rows 37 259 69 104 16 32 64 128 256), losses := [] }

theorem u43234 : Upper (D 7) (R 7) [36,257,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43235_10 : Upper (D 7) (R 7) [36,257,65,130,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38461

theorem m43235_34 : Upper (D 7) (R 7) [36,257,65,130,34] 13 :=
  permutation_upper _ _ _ [36,257,65,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38467

theorem m43235_40 : Upper (D 7) (R 7) [36,257,65,130,40] 13 :=
  permutation_upper _ _ _ [36,257,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38472

theorem m43235_66 : Upper (D 7) (R 7) [36,257,65,130,66] 13 :=
  permutation_upper _ _ _ [36,257,65,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38475

theorem m43235_72 : Upper (D 7) (R 7) [36,257,65,130,72] 13 :=
  permutation_upper _ _ _ [36,257,65,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38478

theorem m43235_96 : Upper (D 7) (R 7) [36,257,65,130,96] 13 :=
  permutation_upper _ _ _ [36,257,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38481

def r43235 : Route 9 := (fun mask => (mask,id))

def c43235 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43235 : Upper (D 7) (R 7) [36,257,65,130] 13 := by
  apply FastRouting.sound _ _ [36,257,65,130] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43235 c43235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43235_10
  · exact m43235_34
  · exact m43235_40
  · exact m43235_66
  · exact m43235_72
  · exact m43235_96
  · exact u38483
  · exact u38484
  · exact u38485
  · exact u38486

theorem m43236_10 : Upper (D 7) (R 7) [36,257,65,144,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38462

theorem m43236_34 : Upper (D 7) (R 7) [36,257,65,144,34] 13 :=
  permutation_upper _ _ _ [36,257,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38468

theorem m43236_40 : Upper (D 7) (R 7) [36,257,65,144,40] 13 :=
  permutation_upper _ _ _ [36,257,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38473

theorem m43236_66 : Upper (D 7) (R 7) [36,257,65,144,66] 13 :=
  permutation_upper _ _ _ [36,257,65,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38476

theorem m43236_72 : Upper (D 7) (R 7) [36,257,65,144,72] 13 :=
  permutation_upper _ _ _ [36,257,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38479

theorem m43236_96 : Upper (D 7) (R 7) [36,257,65,144,96] 13 :=
  permutation_upper _ _ _ [36,257,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38482

theorem m43236_130 : Upper (D 7) (R 7) [36,257,65,144,130] 13 :=
  permutation_upper _ _ _ [36,257,65,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38484

def r43236 : Route 9 := (fun mask => (mask,id))

def c43236 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43236 : Upper (D 7) (R 7) [36,257,65,144] 13 := by
  apply FastRouting.sound _ _ [36,257,65,144] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43236 c43236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43236_10
  · exact m43236_34
  · exact m43236_40
  · exact m43236_66
  · exact m43236_72
  · exact m43236_96
  · exact m43236_130
  · exact u38487
  · exact u38488
  · exact u38489

theorem m43237_10 : Upper (D 7) (R 7) [36,257,65,160,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38463

theorem m43237_66 : Upper (D 7) (R 7) [36,257,65,160,66] 13 :=
  permutation_upper _ _ _ [36,257,65,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38477

theorem m43237_72 : Upper (D 7) (R 7) [36,257,65,160,72] 13 :=
  permutation_upper _ _ _ [36,257,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38480

theorem m43237_130 : Upper (D 7) (R 7) [36,257,65,160,130] 13 :=
  permutation_upper _ _ _ [36,257,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38485

theorem m43237_136 : Upper (D 7) (R 7) [36,257,65,160,136] 13 :=
  permutation_upper _ _ _ [36,257,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38488

def r43237 : Route 9 := (fun mask => (mask,id))

def c43237 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43237 : Upper (D 7) (R 7) [36,257,65,160] 13 := by
  apply FastRouting.sound _ _ [36,257,65,160] 13 (by decide) (choices 2) [10,66,72,130,136,192] r43237 c43237
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43237_10
  · exact m43237_66
  · exact m43237_72
  · exact m43237_130
  · exact m43237_136
  · exact u38490

theorem m43238_10 : Upper (D 7) (R 7) [36,257,65,192,10] 13 :=
  permutation_upper _ _ _ [36,257,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38464

theorem m43238_34 : Upper (D 7) (R 7) [36,257,65,192,34] 13 :=
  permutation_upper _ _ _ [36,257,65,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38469

theorem m43238_40 : Upper (D 7) (R 7) [36,257,65,192,40] 13 :=
  permutation_upper _ _ _ [36,257,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38474

theorem m43238_130 : Upper (D 7) (R 7) [36,257,65,192,130] 13 :=
  permutation_upper _ _ _ [36,257,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38486

theorem m43238_136 : Upper (D 7) (R 7) [36,257,65,192,136] 13 :=
  permutation_upper _ _ _ [36,257,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38489

theorem m43238_160 : Upper (D 7) (R 7) [36,257,65,192,160] 13 :=
  permutation_upper _ _ _ [36,257,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38490

def r43238 : Route 9 := (fun mask => (mask,id))

def c43238 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43238 : Upper (D 7) (R 7) [36,257,65,192] 13 := by
  apply FastRouting.sound _ _ [36,257,65,192] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43238 c43238
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43238_10
  · exact m43238_34
  · exact m43238_40
  · exact m43238_130
  · exact m43238_136
  · exact m43238_160

def b43239 : PairBound 9 := { available := 248, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 248 248 248 248 504), lower := (rows 37 259 70 11 16 32 64 128 256), losses := [] }

theorem u43239 : Upper (D 7) (R 7) [36,257,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43240 : Route 9 := (fun mask => (mask,id))

def c43240 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43240 : Upper (D 7) (R 7) [36,257,66,17] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43240 c43240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38497
  · exact u38498
  · exact u38499
  · exact u38500
  · exact u38501
  · exact u38502
  · exact u38503
  · exact u38504
  · exact u38505
  · exact u38506

theorem m43241_9 : Upper (D 7) (R 7) [36,257,66,18,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38497

def r43241 : Route 9 := (fun mask => (mask,id))

def c43241 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43241 : Upper (D 7) (R 7) [36,257,66,18] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r43241 c43241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43241_9
  · exact u38507
  · exact u38508
  · exact u38509
  · exact u38510
  · exact u38511
  · exact u38512
  · exact u38513
  · exact u38514
  · exact u38515

def b43242 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 70 41 218 250 218 218 474), lower := (rows 37 259 70 41 16 32 64 128 256), losses := [] }

theorem u43242 : Upper (D 7) (R 7) [36,257,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43243_9 : Upper (D 7) (R 7) [36,257,66,34,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38498

def r43243 : Route 9 := (fun mask => (mask,id))

def c43243 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43243 : Upper (D 7) (R 7) [36,257,66,34] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34] 13 (by decide) (choices 2) [9,65,72,129,136,192] r43243 c43243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43243_9
  · exact u38520
  · exact u38521
  · exact u38522
  · exact u38523
  · exact u38524

theorem m43244_3 : Upper (D 7) (R 7) [36,257,66,48,3] 13 :=
  permutation_upper _ _ _ [36,257,66,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38491

theorem m43244_9 : Upper (D 7) (R 7) [36,257,66,48,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38499

theorem m43244_10 : Upper (D 7) (R 7) [36,257,66,48,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38508

def r43244 : Route 9 := (fun mask => (mask,id))

def c43244 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43244 : Upper (D 7) (R 7) [36,257,66,48] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43244 c43244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43244_3
  · exact m43244_9
  · exact m43244_10
  · exact u38525
  · exact u38526
  · exact u38527
  · exact u38528
  · exact u38529
  · exact u38530
  · exact u38531

theorem m43245_10 : Upper (D 7) (R 7) [36,257,66,65,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38509

theorem m43245_34 : Upper (D 7) (R 7) [36,257,66,65,34] 13 :=
  permutation_upper _ _ _ [36,257,66,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38520

theorem m43245_40 : Upper (D 7) (R 7) [36,257,66,65,40] 13 :=
  permutation_upper _ _ _ [36,257,66,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38525

def r43245 : Route 9 := (fun mask => (mask,id))

def c43245 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43245 : Upper (D 7) (R 7) [36,257,66,65] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43245 c43245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43245_10
  · exact m43245_34
  · exact m43245_40
  · exact u38532
  · exact u38533
  · exact u38534

def b43246 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 259 70 74 185 185 249 185 441), lower := (rows 37 259 70 74 16 32 64 128 256), losses := [] }

theorem u43246 : Upper (D 7) (R 7) [36,257,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43247_3 : Upper (D 7) (R 7) [36,257,66,80,3] 13 :=
  permutation_upper _ _ _ [36,257,66,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38492

theorem m43247_9 : Upper (D 7) (R 7) [36,257,66,80,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38501

theorem m43247_10 : Upper (D 7) (R 7) [36,257,66,80,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38510

theorem m43247_33 : Upper (D 7) (R 7) [36,257,66,80,33] 13 :=
  permutation_upper _ _ _ [36,257,66,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38516

theorem m43247_34 : Upper (D 7) (R 7) [36,257,66,80,34] 13 :=
  permutation_upper _ _ _ [36,257,66,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38521

theorem m43247_40 : Upper (D 7) (R 7) [36,257,66,80,40] 13 :=
  permutation_upper _ _ _ [36,257,66,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38527

def r43247 : Route 9 := (fun mask => (mask,id))

def c43247 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43247 : Upper (D 7) (R 7) [36,257,66,80] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43247 c43247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43247_3
  · exact m43247_9
  · exact m43247_10
  · exact m43247_33
  · exact m43247_34
  · exact m43247_40
  · exact u38538
  · exact u38539
  · exact u38540
  · exact u38541

theorem m43248_3 : Upper (D 7) (R 7) [36,257,66,96,3] 13 :=
  permutation_upper _ _ _ [36,257,66,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38493

theorem m43248_9 : Upper (D 7) (R 7) [36,257,66,96,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38502

theorem m43248_10 : Upper (D 7) (R 7) [36,257,66,96,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38511

def r43248 : Route 9 := (fun mask => (mask,id))

def c43248 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43248 : Upper (D 7) (R 7) [36,257,66,96] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43248 c43248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43248_3
  · exact m43248_9
  · exact m43248_10
  · exact u38542
  · exact u38543
  · exact u38544

theorem m43249_10 : Upper (D 7) (R 7) [36,257,66,129,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38512

theorem m43249_34 : Upper (D 7) (R 7) [36,257,66,129,34] 13 :=
  permutation_upper _ _ _ [36,257,66,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38522

theorem m43249_40 : Upper (D 7) (R 7) [36,257,66,129,40] 13 :=
  permutation_upper _ _ _ [36,257,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38528

theorem m43249_66 : Upper (D 7) (R 7) [36,257,66,129,66] 13 :=
  permutation_upper _ _ _ [36,257,66,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38535

theorem m43249_72 : Upper (D 7) (R 7) [36,257,66,129,72] 13 :=
  permutation_upper _ _ _ [36,257,66,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38538

theorem m43249_96 : Upper (D 7) (R 7) [36,257,66,129,96] 13 :=
  permutation_upper _ _ _ [36,257,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38542

def r43249 : Route 9 := (fun mask => (mask,id))

def c43249 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43249 : Upper (D 7) (R 7) [36,257,66,129] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43249 c43249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43249_10
  · exact m43249_34
  · exact m43249_40
  · exact m43249_66
  · exact m43249_72
  · exact m43249_96
  · exact u38545
  · exact u38546
  · exact u38547
  · exact u38548

theorem m43250_9 : Upper (D 7) (R 7) [36,257,66,130,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38503

theorem m43250_33 : Upper (D 7) (R 7) [36,257,66,130,33] 13 :=
  permutation_upper _ _ _ [36,257,66,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38517

theorem m43250_40 : Upper (D 7) (R 7) [36,257,66,130,40] 13 :=
  permutation_upper _ _ _ [36,257,66,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38529

theorem m43250_65 : Upper (D 7) (R 7) [36,257,66,130,65] 13 :=
  permutation_upper _ _ _ [36,257,66,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38532

theorem m43250_72 : Upper (D 7) (R 7) [36,257,66,130,72] 13 :=
  permutation_upper _ _ _ [36,257,66,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38539

theorem m43250_96 : Upper (D 7) (R 7) [36,257,66,130,96] 13 :=
  permutation_upper _ _ _ [36,257,66,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38543

theorem m43250_129 : Upper (D 7) (R 7) [36,257,66,130,129] 13 :=
  permutation_upper _ _ _ [36,257,66,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38545

def r43250 : Route 9 := (fun mask => (mask,id))

def c43250 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43250 : Upper (D 7) (R 7) [36,257,66,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r43250 c43250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43250_9
  · exact m43250_33
  · exact m43250_40
  · exact m43250_65
  · exact m43250_72
  · exact m43250_96
  · exact m43250_129
  · exact u38549
  · exact u38550
  · exact u38551

theorem m43251_3 : Upper (D 7) (R 7) [36,257,66,144,3] 13 :=
  permutation_upper _ _ _ [36,257,66,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38494

theorem m43251_9 : Upper (D 7) (R 7) [36,257,66,144,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38504

theorem m43251_10 : Upper (D 7) (R 7) [36,257,66,144,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38513

theorem m43251_33 : Upper (D 7) (R 7) [36,257,66,144,33] 13 :=
  permutation_upper _ _ _ [36,257,66,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38518

theorem m43251_34 : Upper (D 7) (R 7) [36,257,66,144,34] 13 :=
  permutation_upper _ _ _ [36,257,66,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38523

theorem m43251_40 : Upper (D 7) (R 7) [36,257,66,144,40] 13 :=
  permutation_upper _ _ _ [36,257,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38530

theorem m43251_65 : Upper (D 7) (R 7) [36,257,66,144,65] 13 :=
  permutation_upper _ _ _ [36,257,66,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38533

theorem m43251_66 : Upper (D 7) (R 7) [36,257,66,144,66] 13 :=
  permutation_upper _ _ _ [36,257,66,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38536

theorem m43251_72 : Upper (D 7) (R 7) [36,257,66,144,72] 13 :=
  permutation_upper _ _ _ [36,257,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38540

theorem m43251_96 : Upper (D 7) (R 7) [36,257,66,144,96] 13 :=
  permutation_upper _ _ _ [36,257,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38544

theorem m43251_129 : Upper (D 7) (R 7) [36,257,66,144,129] 13 :=
  permutation_upper _ _ _ [36,257,66,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38546

theorem m43251_130 : Upper (D 7) (R 7) [36,257,66,144,130] 13 :=
  permutation_upper _ _ _ [36,257,66,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38549

def r43251 : Route 9 := (fun mask => (mask,id))

def c43251 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43251 : Upper (D 7) (R 7) [36,257,66,144] 13 := by
  apply FastRouting.sound _ _ [36,257,66,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r43251 c43251
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43251_3
  · exact m43251_9
  · exact m43251_10
  · exact m43251_33
  · exact m43251_34
  · exact m43251_40
  · exact m43251_65
  · exact m43251_66
  · exact m43251_72
  · exact m43251_96
  · exact m43251_129
  · exact m43251_130
  · exact u38552
  · exact u38553
  · exact u38554

theorem m43252_3 : Upper (D 7) (R 7) [36,257,66,160,3] 13 :=
  permutation_upper _ _ _ [36,257,66,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38495

theorem m43252_9 : Upper (D 7) (R 7) [36,257,66,160,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38505

theorem m43252_10 : Upper (D 7) (R 7) [36,257,66,160,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38514

theorem m43252_65 : Upper (D 7) (R 7) [36,257,66,160,65] 13 :=
  permutation_upper _ _ _ [36,257,66,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38534

theorem m43252_66 : Upper (D 7) (R 7) [36,257,66,160,66] 13 :=
  permutation_upper _ _ _ [36,257,66,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38537

theorem m43252_72 : Upper (D 7) (R 7) [36,257,66,160,72] 13 :=
  permutation_upper _ _ _ [36,257,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38541

theorem m43252_129 : Upper (D 7) (R 7) [36,257,66,160,129] 13 :=
  permutation_upper _ _ _ [36,257,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38547

theorem m43252_130 : Upper (D 7) (R 7) [36,257,66,160,130] 13 :=
  permutation_upper _ _ _ [36,257,66,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38550

theorem m43252_136 : Upper (D 7) (R 7) [36,257,66,160,136] 13 :=
  permutation_upper _ _ _ [36,257,66,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38553

def r43252 : Route 9 := (fun mask => (mask,id))

def c43252 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43252 : Upper (D 7) (R 7) [36,257,66,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43252 c43252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43252_3
  · exact m43252_9
  · exact m43252_10
  · exact m43252_65
  · exact m43252_66
  · exact m43252_72
  · exact m43252_129
  · exact m43252_130
  · exact m43252_136
  · exact u38555

theorem m43253_3 : Upper (D 7) (R 7) [36,257,66,192,3] 13 :=
  permutation_upper _ _ _ [36,257,66,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38496

theorem m43253_9 : Upper (D 7) (R 7) [36,257,66,192,9] 13 :=
  permutation_upper _ _ _ [36,257,66,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38506

theorem m43253_10 : Upper (D 7) (R 7) [36,257,66,192,10] 13 :=
  permutation_upper _ _ _ [36,257,66,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38515

theorem m43253_33 : Upper (D 7) (R 7) [36,257,66,192,33] 13 :=
  permutation_upper _ _ _ [36,257,66,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38519

theorem m43253_34 : Upper (D 7) (R 7) [36,257,66,192,34] 13 :=
  permutation_upper _ _ _ [36,257,66,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38524

theorem m43253_40 : Upper (D 7) (R 7) [36,257,66,192,40] 13 :=
  permutation_upper _ _ _ [36,257,66,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38531

theorem m43253_129 : Upper (D 7) (R 7) [36,257,66,192,129] 13 :=
  permutation_upper _ _ _ [36,257,66,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38548

theorem m43253_130 : Upper (D 7) (R 7) [36,257,66,192,130] 13 :=
  permutation_upper _ _ _ [36,257,66,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38551

theorem m43253_136 : Upper (D 7) (R 7) [36,257,66,192,136] 13 :=
  permutation_upper _ _ _ [36,257,66,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38554

theorem m43253_160 : Upper (D 7) (R 7) [36,257,66,192,160] 13 :=
  permutation_upper _ _ _ [36,257,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38555

def r43253 : Route 9 := (fun mask => (mask,id))

def c43253 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43253 : Upper (D 7) (R 7) [36,257,66,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43253 c43253
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43253_3
  · exact m43253_9
  · exact m43253_10
  · exact m43253_33
  · exact m43253_34
  · exact m43253_40
  · exact m43253_129
  · exact m43253_130
  · exact m43253_136
  · exact m43253_160

def b43254 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 76 11 242 242 242 242 498), lower := (rows 37 259 76 11 16 32 64 128 256), losses := [] }

theorem u43254 : Upper (D 7) (R 7) [36,257,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43255 : Route 9 := (fun mask => (mask,id))

def c43255 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43255 : Upper (D 7) (R 7) [36,257,72,17] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43255 c43255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38556
  · exact u38557
  · exact u38558
  · exact u38559
  · exact u38560
  · exact u38561

def r43256 : Route 9 := (fun mask => (mask,id))

def c43256 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43256 : Upper (D 7) (R 7) [36,257,72,18] 13 := by
  apply FastRouting.sound _ _ [36,257,72,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43256 c43256
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38562
  · exact u38563
  · exact u38564
  · exact u38565
  · exact u38566
  · exact u38567
  · exact u38568
  · exact u38569
  · exact u38570
  · exact u38571

def b43257 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 76 41 210 242 210 210 466), lower := (rows 37 259 76 41 16 32 64 128 256), losses := [] }

theorem u43257 : Upper (D 7) (R 7) [36,257,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43258 : Route 9 := (fun mask => (mask,id))

def c43258 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43258 : Upper (D 7) (R 7) [36,257,72,34] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43258 c43258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38572
  · exact u38573
  · exact u38574
  · exact u38575
  · exact u38576
  · exact u38577

def r43259 : Route 9 := (fun mask => (mask,id))

def c43259 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43259 : Upper (D 7) (R 7) [36,257,72,48] 13 := by
  apply FastRouting.sound _ _ [36,257,72,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43259 c43259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38578
  · exact u38579
  · exact u38580
  · exact u38581
  · exact u38582
  · exact u38583

#print axioms u43259
end Delivery.IrregularNine14.P07
