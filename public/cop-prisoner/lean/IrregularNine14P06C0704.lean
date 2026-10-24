import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0576
import IrregularNine14P06C0577
import IrregularNine14P06C0578
import IrregularNine14P06C0579
import IrregularNine14P06C0580

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42240 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42240 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42240 : Upper (D 6) (R 6) [10,384,96,17] 13 := by
  apply FastRouting.sound _ _ [10,384,96,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r42240 c42240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34576
  · exact u34577
  · exact u34578
  · exact u34579
  · exact u34580
  · exact u34581
  · exact u34582

def b42241 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 26 117 101 101 229 357), lower := (rows 11 386 100 26 16 32 64 128 256), losses := [] }

theorem u42241 : Upper (D 6) (R 6) [10,384,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42242 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42242 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42242 : Upper (D 6) (R 6) [10,384,96,20] 13 := by
  apply FastRouting.sound _ _ [10,384,96,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r42242 c42242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34583
  · exact u34584
  · exact u34585
  · exact u34586
  · exact u34587
  · exact u34588
  · exact u34589

def r42243 : Route 9 := (fun mask => (mask,id))

def c42243 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42243 : Upper (D 6) (R 6) [10,384,96,33] 13 := by
  apply FastRouting.sound _ _ [10,384,96,33] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42243 c42243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34590
  · exact u34591
  · exact u34592
  · exact u34593
  · exact u34594
  · exact u34595

def b42244 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 42 85 117 85 213 341), lower := (rows 11 386 100 42 16 32 64 128 256), losses := [] }

theorem u42244 : Upper (D 6) (R 6) [10,384,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42245 : PairBound 9 := { available := 87, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 386 100 44 87 119 87 215 343), lower := (rows 11 386 100 44 16 32 64 128 256), losses := [] }

theorem u42245 : Upper (D 6) (R 6) [10,384,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42246 : Route 9 := (fun mask => (mask,id))

def c42246 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42246 : Upper (D 6) (R 6) [10,384,96,48] 13 := by
  apply FastRouting.sound _ _ [10,384,96,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42246 c42246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34596
  · exact u34597
  · exact u34598
  · exact u34599
  · exact u34600
  · exact u34601

def b42247 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 386 100 104 23 55 87 151 279), lower := (rows 11 386 100 104 16 32 64 128 256), losses := [] }

theorem u42247 : Upper (D 6) (R 6) [10,384,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42248_66 : Upper (D 6) (R 6) [24,33,65,6,66] 13 :=
  permutation_upper _ _ _ [24,33,65,6,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34604

theorem m42248_68 : Upper (D 6) (R 6) [24,33,65,6,68] 13 :=
  permutation_upper _ _ _ [24,33,65,6,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34603

theorem m42248_132 : Upper (D 6) (R 6) [24,33,65,6,132] 13 :=
  permutation_upper _ _ _ [24,33,65,6,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34606

theorem m42248_192 : Upper (D 6) (R 6) [24,33,65,6,192] 13 :=
  permutation_upper _ _ _ [24,33,65,6,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34607

def r42248 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42248 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42248 : Upper (D 6) (R 6) [24,33,65,6] 13 := by
  apply FastRouting.sound _ _ [24,33,65,6] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r42248 c42248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34602
  · exact u34603
  · exact u34604
  · exact m42248_66
  · exact m42248_68
  · exact u34605
  · exact u34606
  · exact m42248_132
  · exact u34607
  · exact m42248_192
  · exact u34608

def b42249 : PairBound 9 := { available := 454, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 42 470 486 454 454 454), lower := (rows 25 35 69 42 16 32 64 128 256), losses := [] }

theorem u42249 : Upper (D 6) (R 6) [24,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42250_6 : Upper (D 6) (R 6) [24,33,65,36,6] 13 :=
  permutation_upper _ _ _ [24,33,65,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34604

theorem m42250_68 : Upper (D 6) (R 6) [24,33,65,36,68] 13 :=
  permutation_upper _ _ _ [24,33,65,34,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34609

def r42250 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42250 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42250 : Upper (D 6) (R 6) [24,33,65,36] 13 := by
  apply FastRouting.sound _ _ [24,33,65,36] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r42250 c42250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42250_6
  · exact u34614
  · exact m42250_68
  · exact u34615
  · exact u34616
  · exact u34617
  · exact u34618

def b42251 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 69 104 406 422 454 390 390), lower := (rows 25 35 69 104 16 32 64 128 256), losses := [] }

theorem u42251 : Upper (D 6) (R 6) [24,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42252_6 : Upper (D 6) (R 6) [24,33,65,130,6] 13 :=
  permutation_upper _ _ _ [24,33,65,6,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34606

theorem m42252_34 : Upper (D 6) (R 6) [24,33,65,130,34] 13 :=
  permutation_upper _ _ _ [24,33,65,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34610

theorem m42252_36 : Upper (D 6) (R 6) [24,33,65,130,36] 13 :=
  permutation_upper _ _ _ [24,33,65,36,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34615

theorem m42252_66 : Upper (D 6) (R 6) [24,33,65,130,66] 13 :=
  permutation_upper _ _ _ [24,33,65,36,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34616

theorem m42252_68 : Upper (D 6) (R 6) [24,33,65,130,68] 13 :=
  permutation_upper _ _ _ [24,33,65,34,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34611

theorem m42252_96 : Upper (D 6) (R 6) [24,33,65,130,96] 13 :=
  permutation_upper _ _ _ [24,33,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34619

def r42252 : Route 9 := (fun mask => (mask,id))

def c42252 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42252 : Upper (D 6) (R 6) [24,33,65,130] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42252 c42252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42252_6
  · exact m42252_34
  · exact m42252_36
  · exact m42252_66
  · exact m42252_68
  · exact m42252_96
  · exact u34621
  · exact u34622
  · exact u34623
  · exact u34624

theorem m42253_6 : Upper (D 6) (R 6) [24,33,65,160,6] 13 :=
  permutation_upper _ _ _ [24,33,65,6,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34607

theorem m42253_66 : Upper (D 6) (R 6) [24,33,65,160,66] 13 :=
  permutation_upper _ _ _ [24,33,65,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34617

theorem m42253_68 : Upper (D 6) (R 6) [24,33,65,160,68] 13 :=
  permutation_upper _ _ _ [24,33,65,34,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34612

theorem m42253_258 : Upper (D 6) (R 6) [24,33,65,160,258] 13 :=
  permutation_upper _ _ _ [24,33,65,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34623

theorem m42253_260 : Upper (D 6) (R 6) [24,33,65,160,260] 13 :=
  permutation_upper _ _ _ [24,33,65,130,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34624

def r42253 : Route 9 := (fun mask => (mask,id))

def c42253 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42253 : Upper (D 6) (R 6) [24,33,65,160] 13 := by
  apply FastRouting.sound _ _ [24,33,65,160] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42253 c42253
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42253_6
  · exact m42253_66
  · exact m42253_68
  · exact m42253_258
  · exact m42253_260
  · exact u34625

theorem m42254_6 : Upper (D 6) (R 6) [24,33,65,384,6] 13 :=
  permutation_upper _ _ _ [24,33,65,6,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34608

theorem m42254_34 : Upper (D 6) (R 6) [24,33,65,384,34] 13 :=
  permutation_upper _ _ _ [24,33,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34613

theorem m42254_36 : Upper (D 6) (R 6) [24,33,65,384,36] 13 :=
  permutation_upper _ _ _ [24,33,65,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34618

theorem m42254_66 : Upper (D 6) (R 6) [24,33,65,384,66] 13 :=
  permutation_upper _ _ _ [24,33,65,36,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34618

theorem m42254_68 : Upper (D 6) (R 6) [24,33,65,384,68] 13 :=
  permutation_upper _ _ _ [24,33,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34613

theorem m42254_96 : Upper (D 6) (R 6) [24,33,65,384,96] 13 :=
  permutation_upper _ _ _ [24,33,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34620

def r42254 : Route 9 := (fun mask => (mask,id))

def c42254 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42254 : Upper (D 6) (R 6) [24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [24,33,65,384] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42254 c42254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42254_6
  · exact m42254_34
  · exact m42254_36
  · exact m42254_66
  · exact m42254_68
  · exact m42254_96

def b42255 : PairBound 9 := { available := 484, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 70 11 500 484 484 484 484), lower := (rows 25 35 70 11 16 32 64 128 256), losses := [] }

theorem u42255 : Upper (D 6) (R 6) [24,33,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42256 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42256 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42256 : Upper (D 6) (R 6) [24,33,66,5] 13 := by
  apply FastRouting.sound _ _ [24,33,66,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r42256 c42256
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34632
  · exact u34633
  · exact u34634
  · exact u34635
  · exact u34636
  · exact u34637
  · exact u34638
  · exact u34639
  · exact u34640
  · exact u34641
  · exact u34642

def b42257 : PairBound 9 := { available := 485, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 501 485 485 485 485), lower := (rows 25 35 70 14 16 32 64 128 256), losses := [] }

theorem u42257 : Upper (D 6) (R 6) [24,33,66,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42258 : PairBound 9 := { available := 454, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 41 470 486 454 454 454), lower := (rows 25 35 70 41 16 32 64 128 256), losses := [] }

theorem u42258 : Upper (D 6) (R 6) [24,33,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42259 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 70 42 469 485 453 453 453), lower := (rows 25 35 70 42 16 32 64 128 256), losses := [] }

theorem u42259 : Upper (D 6) (R 6) [24,33,66,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42260_3 : Upper (D 6) (R 6) [24,33,66,36,3] 13 :=
  permutation_upper _ _ _ [24,33,66,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34626

theorem m42260_5 : Upper (D 6) (R 6) [24,33,66,36,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34634

theorem m42260_6 : Upper (D 6) (R 6) [24,33,66,36,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34643

def r42260 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42260 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42260 : Upper (D 6) (R 6) [24,33,66,36] 13 := by
  apply FastRouting.sound _ _ [24,33,66,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r42260 c42260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42260_3
  · exact m42260_5
  · exact m42260_6
  · exact u34658
  · exact u34659
  · exact u34660
  · exact u34661
  · exact u34662
  · exact u34663
  · exact u34664
  · exact u34665

def b42261 : PairBound 9 := { available := 422, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 25 35 70 73 438 422 486 422 422), lower := (rows 25 35 70 73 16 32 64 128 256), losses := [] }

theorem u42261 : Upper (D 6) (R 6) [24,33,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42262 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 8, targets := 33 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 35 70 74 437 421 485 421 421), lower := (rows 25 35 70 74 16 32 64 128 256), losses := [] }

theorem u42262 : Upper (D 6) (R 6) [24,33,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42263 : PairBound 9 := { available := 423, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 70 76 439 423 487 423 423), lower := (rows 25 35 70 76 16 32 64 128 256), losses := [] }

theorem u42263 : Upper (D 6) (R 6) [24,33,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42264_3 : Upper (D 6) (R 6) [24,33,66,96,3] 13 :=
  permutation_upper _ _ _ [24,33,66,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34627

theorem m42264_5 : Upper (D 6) (R 6) [24,33,66,96,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34637

theorem m42264_6 : Upper (D 6) (R 6) [24,33,66,96,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34644

def r42264 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42264 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42264 : Upper (D 6) (R 6) [24,33,66,96] 13 := by
  apply FastRouting.sound _ _ [24,33,66,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42264 c42264
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42264_3
  · exact m42264_5
  · exact m42264_6
  · exact u34679
  · exact u34680
  · exact u34681
  · exact u34682

theorem m42265_6 : Upper (D 6) (R 6) [24,33,66,129,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34645

theorem m42265_34 : Upper (D 6) (R 6) [24,33,66,129,34] 13 :=
  permutation_upper _ _ _ [24,33,66,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34654

theorem m42265_36 : Upper (D 6) (R 6) [24,33,66,129,36] 13 :=
  permutation_upper _ _ _ [24,33,66,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34661

theorem m42265_66 : Upper (D 6) (R 6) [24,33,66,129,66] 13 :=
  permutation_upper _ _ _ [24,33,66,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34670

theorem m42265_68 : Upper (D 6) (R 6) [24,33,66,129,68] 13 :=
  permutation_upper _ _ _ [24,33,66,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34674

theorem m42265_96 : Upper (D 6) (R 6) [24,33,66,129,96] 13 :=
  permutation_upper _ _ _ [24,33,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34679

def r42265 : Route 9 := (fun mask => (mask,id))

def c42265 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42265 : Upper (D 6) (R 6) [24,33,66,129] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42265 c42265
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42265_6
  · exact m42265_34
  · exact m42265_36
  · exact m42265_66
  · exact m42265_68
  · exact m42265_96
  · exact u34683
  · exact u34684
  · exact u34685
  · exact u34686

theorem m42266_5 : Upper (D 6) (R 6) [24,33,66,130,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34638

theorem m42266_33 : Upper (D 6) (R 6) [24,33,66,130,33] 13 :=
  permutation_upper _ _ _ [24,33,66,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34650

theorem m42266_36 : Upper (D 6) (R 6) [24,33,66,130,36] 13 :=
  permutation_upper _ _ _ [24,33,66,36,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34662

theorem m42266_65 : Upper (D 6) (R 6) [24,33,66,130,65] 13 :=
  permutation_upper _ _ _ [24,33,66,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34666

theorem m42266_68 : Upper (D 6) (R 6) [24,33,66,130,68] 13 :=
  permutation_upper _ _ _ [24,33,66,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34675

theorem m42266_96 : Upper (D 6) (R 6) [24,33,66,130,96] 13 :=
  permutation_upper _ _ _ [24,33,66,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34680

theorem m42266_257 : Upper (D 6) (R 6) [24,33,66,130,257] 13 :=
  permutation_upper _ _ _ [24,33,66,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34683

def r42266 : Route 9 := (fun mask => (mask,id))

def c42266 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42266 : Upper (D 6) (R 6) [24,33,66,130] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42266 c42266
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42266_5
  · exact m42266_33
  · exact m42266_36
  · exact m42266_65
  · exact m42266_68
  · exact m42266_96
  · exact m42266_257
  · exact u34687
  · exact u34688
  · exact u34689

theorem m42267_3 : Upper (D 6) (R 6) [24,33,66,132,3] 13 :=
  permutation_upper _ _ _ [24,33,66,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34628

theorem m42267_5 : Upper (D 6) (R 6) [24,33,66,132,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34639

theorem m42267_6 : Upper (D 6) (R 6) [24,33,66,132,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34646

theorem m42267_33 : Upper (D 6) (R 6) [24,33,66,132,33] 13 :=
  permutation_upper _ _ _ [24,33,66,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34651

theorem m42267_34 : Upper (D 6) (R 6) [24,33,66,132,34] 13 :=
  permutation_upper _ _ _ [24,33,66,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34655

theorem m42267_36 : Upper (D 6) (R 6) [24,33,66,132,36] 13 :=
  permutation_upper _ _ _ [24,33,66,36,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34663

theorem m42267_65 : Upper (D 6) (R 6) [24,33,66,132,65] 13 :=
  permutation_upper _ _ _ [24,33,66,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34667

theorem m42267_66 : Upper (D 6) (R 6) [24,33,66,132,66] 13 :=
  permutation_upper _ _ _ [24,33,66,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34671

theorem m42267_68 : Upper (D 6) (R 6) [24,33,66,132,68] 13 :=
  permutation_upper _ _ _ [24,33,66,68,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34676

theorem m42267_96 : Upper (D 6) (R 6) [24,33,66,132,96] 13 :=
  permutation_upper _ _ _ [24,33,66,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34681

theorem m42267_257 : Upper (D 6) (R 6) [24,33,66,132,257] 13 :=
  permutation_upper _ _ _ [24,33,66,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34684

theorem m42267_258 : Upper (D 6) (R 6) [24,33,66,132,258] 13 :=
  permutation_upper _ _ _ [24,33,66,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34687

def r42267 : Route 9 := (fun mask => (mask,id))

def c42267 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42267 : Upper (D 6) (R 6) [24,33,66,132] 13 := by
  apply FastRouting.sound _ _ [24,33,66,132] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42267 c42267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42267_3
  · exact m42267_5
  · exact m42267_6
  · exact m42267_33
  · exact m42267_34
  · exact m42267_36
  · exact m42267_65
  · exact m42267_66
  · exact m42267_68
  · exact m42267_96
  · exact m42267_257
  · exact m42267_258
  · exact u34690
  · exact u34691
  · exact u34692

theorem m42268_3 : Upper (D 6) (R 6) [24,33,66,160,3] 13 :=
  permutation_upper _ _ _ [24,33,66,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34629

theorem m42268_5 : Upper (D 6) (R 6) [24,33,66,160,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34640

theorem m42268_6 : Upper (D 6) (R 6) [24,33,66,160,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34647

theorem m42268_65 : Upper (D 6) (R 6) [24,33,66,160,65] 13 :=
  permutation_upper _ _ _ [24,33,66,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34668

theorem m42268_66 : Upper (D 6) (R 6) [24,33,66,160,66] 13 :=
  permutation_upper _ _ _ [24,33,66,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34672

theorem m42268_68 : Upper (D 6) (R 6) [24,33,66,160,68] 13 :=
  permutation_upper _ _ _ [24,33,66,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34677

theorem m42268_257 : Upper (D 6) (R 6) [24,33,66,160,257] 13 :=
  permutation_upper _ _ _ [24,33,66,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34685

theorem m42268_258 : Upper (D 6) (R 6) [24,33,66,160,258] 13 :=
  permutation_upper _ _ _ [24,33,66,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34688

theorem m42268_260 : Upper (D 6) (R 6) [24,33,66,160,260] 13 :=
  permutation_upper _ _ _ [24,33,66,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34691

def r42268 : Route 9 := (fun mask => (mask,id))

def c42268 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42268 : Upper (D 6) (R 6) [24,33,66,160] 13 := by
  apply FastRouting.sound _ _ [24,33,66,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42268 c42268
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42268_3
  · exact m42268_5
  · exact m42268_6
  · exact m42268_65
  · exact m42268_66
  · exact m42268_68
  · exact m42268_257
  · exact m42268_258
  · exact m42268_260
  · exact u34693

theorem m42269_3 : Upper (D 6) (R 6) [24,33,66,192,3] 13 :=
  permutation_upper _ _ _ [24,33,66,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34630

theorem m42269_5 : Upper (D 6) (R 6) [24,33,66,192,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34641

theorem m42269_6 : Upper (D 6) (R 6) [24,33,66,192,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34648

theorem m42269_33 : Upper (D 6) (R 6) [24,33,66,192,33] 13 :=
  permutation_upper _ _ _ [24,33,66,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34652

theorem m42269_34 : Upper (D 6) (R 6) [24,33,66,192,34] 13 :=
  permutation_upper _ _ _ [24,33,66,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34656

theorem m42269_36 : Upper (D 6) (R 6) [24,33,66,192,36] 13 :=
  permutation_upper _ _ _ [24,33,66,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34664

theorem m42269_257 : Upper (D 6) (R 6) [24,33,66,192,257] 13 :=
  permutation_upper _ _ _ [24,33,66,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34686

theorem m42269_258 : Upper (D 6) (R 6) [24,33,66,192,258] 13 :=
  permutation_upper _ _ _ [24,33,66,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34689

theorem m42269_260 : Upper (D 6) (R 6) [24,33,66,192,260] 13 :=
  permutation_upper _ _ _ [24,33,66,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34692

theorem m42269_288 : Upper (D 6) (R 6) [24,33,66,192,288] 13 :=
  permutation_upper _ _ _ [24,33,66,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34693

def r42269 : Route 9 := (fun mask => (mask,id))

def c42269 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42269 : Upper (D 6) (R 6) [24,33,66,192] 13 := by
  apply FastRouting.sound _ _ [24,33,66,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42269 c42269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42269_3
  · exact m42269_5
  · exact m42269_6
  · exact m42269_33
  · exact m42269_34
  · exact m42269_36
  · exact m42269_257
  · exact m42269_258
  · exact m42269_260
  · exact m42269_288

theorem m42270_3 : Upper (D 6) (R 6) [24,33,66,384,3] 13 :=
  permutation_upper _ _ _ [24,33,66,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34631

theorem m42270_5 : Upper (D 6) (R 6) [24,33,66,384,5] 13 :=
  permutation_upper _ _ _ [24,33,66,5,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34642

theorem m42270_6 : Upper (D 6) (R 6) [24,33,66,384,6] 13 :=
  permutation_upper _ _ _ [24,33,66,6,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34649

theorem m42270_33 : Upper (D 6) (R 6) [24,33,66,384,33] 13 :=
  permutation_upper _ _ _ [24,33,66,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34653

theorem m42270_34 : Upper (D 6) (R 6) [24,33,66,384,34] 13 :=
  permutation_upper _ _ _ [24,33,66,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34657

theorem m42270_36 : Upper (D 6) (R 6) [24,33,66,384,36] 13 :=
  permutation_upper _ _ _ [24,33,66,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34665

theorem m42270_65 : Upper (D 6) (R 6) [24,33,66,384,65] 13 :=
  permutation_upper _ _ _ [24,33,66,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34669

theorem m42270_66 : Upper (D 6) (R 6) [24,33,66,384,66] 13 :=
  permutation_upper _ _ _ [24,33,66,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34673

theorem m42270_68 : Upper (D 6) (R 6) [24,33,66,384,68] 13 :=
  permutation_upper _ _ _ [24,33,66,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34678

theorem m42270_96 : Upper (D 6) (R 6) [24,33,66,384,96] 13 :=
  permutation_upper _ _ _ [24,33,66,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34682

def r42270 : Route 9 := (fun mask => (mask,id))

def c42270 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42270 : Upper (D 6) (R 6) [24,33,66,384] 13 := by
  apply FastRouting.sound _ _ [24,33,66,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42270 c42270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42270_3
  · exact m42270_5
  · exact m42270_6
  · exact m42270_33
  · exact m42270_34
  · exact m42270_36
  · exact m42270_65
  · exact m42270_66
  · exact m42270_68
  · exact m42270_96

def b42271 : PairBound 9 := { available := 454, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 100 11 470 486 454 454 454), lower := (rows 25 35 100 11 16 32 64 128 256), losses := [] }

theorem u42271 : Upper (D 6) (R 6) [24,33,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42272 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42272 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42272 : Upper (D 6) (R 6) [24,33,96,5] 13 := by
  apply FastRouting.sound _ _ [24,33,96,5] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r42272 c42272
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34700
  · exact u34701
  · exact u34702
  · exact u34703
  · exact u34704
  · exact u34705
  · exact u34706

theorem m42273_3 : Upper (D 6) (R 6) [24,33,96,6,3] 13 :=
  permutation_upper _ _ _ [24,33,96,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34694

theorem m42273_5 : Upper (D 6) (R 6) [24,33,96,6,5] 13 :=
  permutation_upper _ _ _ [24,33,96,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34700

def r42273 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42273 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42273 : Upper (D 6) (R 6) [24,33,96,6] 13 := by
  apply FastRouting.sound _ _ [24,33,96,6] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r42273 c42273
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42273_3
  · exact m42273_5
  · exact u34707
  · exact u34708
  · exact u34709
  · exact u34710
  · exact u34711
  · exact u34712
  · exact u34713
  · exact u34714
  · exact u34715

theorem m42274_6 : Upper (D 6) (R 6) [24,33,96,65,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34708

def r42274 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42274 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42274 : Upper (D 6) (R 6) [24,33,96,65] 13 := by
  apply FastRouting.sound _ _ [24,33,96,65] 13 (by decide) (choices 2) [6,130,132,384] r42274 c42274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m42274_6
  · exact u34716
  · exact u34717
  · exact u34718

theorem m42275_3 : Upper (D 6) (R 6) [24,33,96,66,3] 13 :=
  permutation_upper _ _ _ [24,33,96,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34695

theorem m42275_5 : Upper (D 6) (R 6) [24,33,96,66,5] 13 :=
  permutation_upper _ _ _ [24,33,96,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34701

theorem m42275_6 : Upper (D 6) (R 6) [24,33,96,66,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34709

def r42275 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42275 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42275 : Upper (D 6) (R 6) [24,33,96,66] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42275 c42275
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42275_3
  · exact m42275_5
  · exact m42275_6
  · exact u34719
  · exact u34720
  · exact u34721
  · exact u34722

def b42276 : PairBound 9 := { available := 391, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 100 76 407 423 455 391 391), lower := (rows 25 35 100 76 16 32 64 128 256), losses := [] }

theorem u42276 : Upper (D 6) (R 6) [24,33,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42277_6 : Upper (D 6) (R 6) [24,33,96,129,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34711

theorem m42277_66 : Upper (D 6) (R 6) [24,33,96,129,66] 13 :=
  permutation_upper _ _ _ [24,33,96,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34719

theorem m42277_68 : Upper (D 6) (R 6) [24,33,96,129,68] 13 :=
  permutation_upper _ _ _ [24,33,96,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34723

def r42277 : Route 9 := (fun mask => (mask,id))

def c42277 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42277 : Upper (D 6) (R 6) [24,33,96,129] 13 := by
  apply FastRouting.sound _ _ [24,33,96,129] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42277 c42277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42277_6
  · exact m42277_66
  · exact m42277_68
  · exact u34727
  · exact u34728
  · exact u34729

theorem m42278_3 : Upper (D 6) (R 6) [24,33,96,130,3] 13 :=
  permutation_upper _ _ _ [24,33,96,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34696

theorem m42278_5 : Upper (D 6) (R 6) [24,33,96,130,5] 13 :=
  permutation_upper _ _ _ [24,33,96,5,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34703

theorem m42278_6 : Upper (D 6) (R 6) [24,33,96,130,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34712

theorem m42278_65 : Upper (D 6) (R 6) [24,33,96,130,65] 13 :=
  permutation_upper _ _ _ [24,33,96,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34716

theorem m42278_66 : Upper (D 6) (R 6) [24,33,96,130,66] 13 :=
  permutation_upper _ _ _ [24,33,96,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34720

theorem m42278_68 : Upper (D 6) (R 6) [24,33,96,130,68] 13 :=
  permutation_upper _ _ _ [24,33,96,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34724

theorem m42278_257 : Upper (D 6) (R 6) [24,33,96,130,257] 13 :=
  permutation_upper _ _ _ [24,33,96,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34727

def r42278 : Route 9 := (fun mask => (mask,id))

def c42278 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42278 : Upper (D 6) (R 6) [24,33,96,130] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42278 c42278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42278_3
  · exact m42278_5
  · exact m42278_6
  · exact m42278_65
  · exact m42278_66
  · exact m42278_68
  · exact m42278_257
  · exact u34730
  · exact u34731
  · exact u34732

theorem m42279_3 : Upper (D 6) (R 6) [24,33,96,132,3] 13 :=
  permutation_upper _ _ _ [24,33,96,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34697

theorem m42279_5 : Upper (D 6) (R 6) [24,33,96,132,5] 13 :=
  permutation_upper _ _ _ [24,33,96,5,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34704

theorem m42279_6 : Upper (D 6) (R 6) [24,33,96,132,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34713

theorem m42279_65 : Upper (D 6) (R 6) [24,33,96,132,65] 13 :=
  permutation_upper _ _ _ [24,33,96,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34717

theorem m42279_66 : Upper (D 6) (R 6) [24,33,96,132,66] 13 :=
  permutation_upper _ _ _ [24,33,96,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34721

theorem m42279_68 : Upper (D 6) (R 6) [24,33,96,132,68] 13 :=
  permutation_upper _ _ _ [24,33,96,68,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34725

theorem m42279_257 : Upper (D 6) (R 6) [24,33,96,132,257] 13 :=
  permutation_upper _ _ _ [24,33,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34728

theorem m42279_258 : Upper (D 6) (R 6) [24,33,96,132,258] 13 :=
  permutation_upper _ _ _ [24,33,96,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34731

def r42279 : Route 9 := (fun mask => (mask,id))

def c42279 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42279 : Upper (D 6) (R 6) [24,33,96,132] 13 := by
  apply FastRouting.sound _ _ [24,33,96,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42279 c42279
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42279_3
  · exact m42279_5
  · exact m42279_6
  · exact m42279_65
  · exact m42279_66
  · exact m42279_68
  · exact m42279_257
  · exact m42279_258
  · exact u34733
  · exact u34734

theorem m42280_3 : Upper (D 6) (R 6) [24,33,96,192,3] 13 :=
  permutation_upper _ _ _ [24,33,96,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34698

theorem m42280_5 : Upper (D 6) (R 6) [24,33,96,192,5] 13 :=
  permutation_upper _ _ _ [24,33,96,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34705

theorem m42280_6 : Upper (D 6) (R 6) [24,33,96,192,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34714

theorem m42280_257 : Upper (D 6) (R 6) [24,33,96,192,257] 13 :=
  permutation_upper _ _ _ [24,33,96,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34729

theorem m42280_258 : Upper (D 6) (R 6) [24,33,96,192,258] 13 :=
  permutation_upper _ _ _ [24,33,96,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34732

theorem m42280_260 : Upper (D 6) (R 6) [24,33,96,192,260] 13 :=
  permutation_upper _ _ _ [24,33,96,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34734

def r42280 : Route 9 := (fun mask => (mask,id))

def c42280 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42280 : Upper (D 6) (R 6) [24,33,96,192] 13 := by
  apply FastRouting.sound _ _ [24,33,96,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42280 c42280
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42280_3
  · exact m42280_5
  · exact m42280_6
  · exact m42280_257
  · exact m42280_258
  · exact m42280_260

theorem m42281_3 : Upper (D 6) (R 6) [24,33,96,384,3] 13 :=
  permutation_upper _ _ _ [24,33,96,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34699

theorem m42281_5 : Upper (D 6) (R 6) [24,33,96,384,5] 13 :=
  permutation_upper _ _ _ [24,33,96,5,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34706

theorem m42281_6 : Upper (D 6) (R 6) [24,33,96,384,6] 13 :=
  permutation_upper _ _ _ [24,33,96,6,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34715

theorem m42281_65 : Upper (D 6) (R 6) [24,33,96,384,65] 13 :=
  permutation_upper _ _ _ [24,33,96,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34718

theorem m42281_66 : Upper (D 6) (R 6) [24,33,96,384,66] 13 :=
  permutation_upper _ _ _ [24,33,96,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34722

theorem m42281_68 : Upper (D 6) (R 6) [24,33,96,384,68] 13 :=
  permutation_upper _ _ _ [24,33,96,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34726

def r42281 : Route 9 := (fun mask => (mask,id))

def c42281 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42281 : Upper (D 6) (R 6) [24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [24,33,96,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42281 c42281
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42281_3
  · exact m42281_5
  · exact m42281_6
  · exact m42281_65
  · exact m42281_66
  · exact m42281_68

def r42282 : Route 9 := (fun mask => (mask,id))

def c42282 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42282 : Upper (D 6) (R 6) [24,33,129,6] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42282 c42282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34735
  · exact u34736
  · exact u34737
  · exact u34738
  · exact u34739
  · exact u34740
  · exact u34741
  · exact u34742
  · exact u34743
  · exact u34744

def b42283 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 133 42 342 358 326 454 326), lower := (rows 25 35 133 42 16 32 64 128 256), losses := [] }

theorem u42283 : Upper (D 6) (R 6) [24,33,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42284_6 : Upper (D 6) (R 6) [24,33,129,36,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34737

def r42284 : Route 9 := (fun mask => (mask,id))

def c42284 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42284 : Upper (D 6) (R 6) [24,33,129,36] 13 := by
  apply FastRouting.sound _ _ [24,33,129,36] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42284 c42284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42284_6
  · exact u34750
  · exact u34751
  · exact u34752
  · exact u34753
  · exact u34754

theorem m42285_6 : Upper (D 6) (R 6) [24,33,129,66,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34738

theorem m42285_34 : Upper (D 6) (R 6) [24,33,129,66,34] 13 :=
  permutation_upper _ _ _ [24,33,129,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34745

theorem m42285_36 : Upper (D 6) (R 6) [24,33,129,66,36] 13 :=
  permutation_upper _ _ _ [24,33,129,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34750

def r42285 : Route 9 := (fun mask => (mask,id))

def c42285 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42285 : Upper (D 6) (R 6) [24,33,129,66] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42285 c42285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42285_6
  · exact m42285_34
  · exact m42285_36
  · exact u34755
  · exact u34756
  · exact u34757
  · exact u34758
  · exact u34759
  · exact u34760
  · exact u34761

theorem m42286_6 : Upper (D 6) (R 6) [24,33,129,68,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34739

theorem m42286_34 : Upper (D 6) (R 6) [24,33,129,68,34] 13 :=
  permutation_upper _ _ _ [24,33,129,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34746

theorem m42286_36 : Upper (D 6) (R 6) [24,33,129,68,36] 13 :=
  permutation_upper _ _ _ [24,33,129,36,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34751

theorem m42286_66 : Upper (D 6) (R 6) [24,33,129,68,66] 13 :=
  permutation_upper _ _ _ [24,33,129,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34756

def r42286 : Route 9 := (fun mask => (mask,id))

def c42286 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42286 : Upper (D 6) (R 6) [24,33,129,68] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42286 c42286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42286_6
  · exact m42286_34
  · exact m42286_36
  · exact m42286_66
  · exact u34762
  · exact u34763
  · exact u34764
  · exact u34765
  · exact u34766
  · exact u34767

theorem m42287_6 : Upper (D 6) (R 6) [24,33,129,96,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34740

theorem m42287_66 : Upper (D 6) (R 6) [24,33,129,96,66] 13 :=
  permutation_upper _ _ _ [24,33,129,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34757

theorem m42287_68 : Upper (D 6) (R 6) [24,33,129,96,68] 13 :=
  permutation_upper _ _ _ [24,33,129,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34763

def r42287 : Route 9 := (fun mask => (mask,id))

def c42287 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42287 : Upper (D 6) (R 6) [24,33,129,96] 13 := by
  apply FastRouting.sound _ _ [24,33,129,96] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42287 c42287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42287_6
  · exact m42287_66
  · exact m42287_68
  · exact u34768
  · exact u34769
  · exact u34770

theorem m42288_6 : Upper (D 6) (R 6) [24,33,129,258,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34741

theorem m42288_34 : Upper (D 6) (R 6) [24,33,129,258,34] 13 :=
  permutation_upper _ _ _ [24,33,129,34,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34747

theorem m42288_36 : Upper (D 6) (R 6) [24,33,129,258,36] 13 :=
  permutation_upper _ _ _ [24,33,129,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34752

theorem m42288_66 : Upper (D 6) (R 6) [24,33,129,258,66] 13 :=
  permutation_upper _ _ _ [24,33,129,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34758

theorem m42288_68 : Upper (D 6) (R 6) [24,33,129,258,68] 13 :=
  permutation_upper _ _ _ [24,33,129,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34764

theorem m42288_96 : Upper (D 6) (R 6) [24,33,129,258,96] 13 :=
  permutation_upper _ _ _ [24,33,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34768

def r42288 : Route 9 := (fun mask => (mask,id))

def c42288 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42288 : Upper (D 6) (R 6) [24,33,129,258] 13 := by
  apply FastRouting.sound _ _ [24,33,129,258] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42288 c42288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42288_6
  · exact m42288_34
  · exact m42288_36
  · exact m42288_66
  · exact m42288_68
  · exact m42288_96

theorem m42289_6 : Upper (D 6) (R 6) [24,33,129,260,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34742

theorem m42289_34 : Upper (D 6) (R 6) [24,33,129,260,34] 13 :=
  permutation_upper _ _ _ [24,33,129,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34748

theorem m42289_36 : Upper (D 6) (R 6) [24,33,129,260,36] 13 :=
  permutation_upper _ _ _ [24,33,129,36,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34753

theorem m42289_66 : Upper (D 6) (R 6) [24,33,129,260,66] 13 :=
  permutation_upper _ _ _ [24,33,129,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34759

theorem m42289_68 : Upper (D 6) (R 6) [24,33,129,260,68] 13 :=
  permutation_upper _ _ _ [24,33,129,68,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34765

theorem m42289_96 : Upper (D 6) (R 6) [24,33,129,260,96] 13 :=
  permutation_upper _ _ _ [24,33,129,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34769

def r42289 : Route 9 := (fun mask => (mask,id))

def c42289 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42289 : Upper (D 6) (R 6) [24,33,129,260] 13 := by
  apply FastRouting.sound _ _ [24,33,129,260] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42289 c42289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42289_6
  · exact m42289_34
  · exact m42289_36
  · exact m42289_66
  · exact m42289_68
  · exact m42289_96

theorem m42290_6 : Upper (D 6) (R 6) [24,33,129,288,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34743

theorem m42290_66 : Upper (D 6) (R 6) [24,33,129,288,66] 13 :=
  permutation_upper _ _ _ [24,33,129,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34760

theorem m42290_68 : Upper (D 6) (R 6) [24,33,129,288,68] 13 :=
  permutation_upper _ _ _ [24,33,129,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34766

def r42290 : Route 9 := (fun mask => (mask,id))

def c42290 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42290 : Upper (D 6) (R 6) [24,33,129,288] 13 := by
  apply FastRouting.sound _ _ [24,33,129,288] 13 (by decide) (choices 2) [6,66,68] r42290 c42290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m42290_6
  · exact m42290_66
  · exact m42290_68

theorem m42291_6 : Upper (D 6) (R 6) [24,33,129,320,6] 13 :=
  permutation_upper _ _ _ [24,33,129,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34744

theorem m42291_34 : Upper (D 6) (R 6) [24,33,129,320,34] 13 :=
  permutation_upper _ _ _ [24,33,129,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34749

theorem m42291_36 : Upper (D 6) (R 6) [24,33,129,320,36] 13 :=
  permutation_upper _ _ _ [24,33,129,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34754

theorem m42291_66 : Upper (D 6) (R 6) [24,33,129,320,66] 13 :=
  permutation_upper _ _ _ [24,33,129,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34761

theorem m42291_68 : Upper (D 6) (R 6) [24,33,129,320,68] 13 :=
  permutation_upper _ _ _ [24,33,129,68,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34767

theorem m42291_96 : Upper (D 6) (R 6) [24,33,129,320,96] 13 :=
  permutation_upper _ _ _ [24,33,129,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34770

def r42291 : Route 9 := (fun mask => (mask,id))

def c42291 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42291 : Upper (D 6) (R 6) [24,33,129,320] 13 := by
  apply FastRouting.sound _ _ [24,33,129,320] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42291 c42291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42291_6
  · exact m42291_34
  · exact m42291_36
  · exact m42291_66
  · exact m42291_68
  · exact m42291_96

def b42292 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 134 11 372 356 356 484 356), lower := (rows 25 35 134 11 16 32 64 128 256), losses := [] }

theorem u42292 : Upper (D 6) (R 6) [24,33,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42293 : Route 9 := (fun mask => (mask,id))

def c42293 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42293 : Upper (D 6) (R 6) [24,33,130,5] 13 := by
  apply FastRouting.sound _ _ [24,33,130,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42293 c42293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34777
  · exact u34778
  · exact u34779
  · exact u34780
  · exact u34781
  · exact u34782
  · exact u34783
  · exact u34784
  · exact u34785
  · exact u34786

def b42294 : PairBound 9 := { available := 357, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 373 357 357 485 357), lower := (rows 25 35 134 14 16 32 64 128 256), losses := [] }

theorem u42294 : Upper (D 6) (R 6) [24,33,130,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42295 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 41 342 358 326 454 326), lower := (rows 25 35 134 41 16 32 64 128 256), losses := [] }

theorem u42295 : Upper (D 6) (R 6) [24,33,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42296 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 134 42 341 357 325 453 325), lower := (rows 25 35 134 42 16 32 64 128 256), losses := [] }

theorem u42296 : Upper (D 6) (R 6) [24,33,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42297_3 : Upper (D 6) (R 6) [24,33,130,36,3] 13 :=
  permutation_upper _ _ _ [24,33,130,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34771

theorem m42297_5 : Upper (D 6) (R 6) [24,33,130,36,5] 13 :=
  permutation_upper _ _ _ [24,33,130,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34779

theorem m42297_6 : Upper (D 6) (R 6) [24,33,130,36,6] 13 :=
  permutation_upper _ _ _ [24,33,130,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34787

def r42297 : Route 9 := (fun mask => (mask,id))

def c42297 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42297 : Upper (D 6) (R 6) [24,33,130,36] 13 := by
  apply FastRouting.sound _ _ [24,33,130,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42297 c42297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42297_3
  · exact m42297_5
  · exact m42297_6
  · exact u34805
  · exact u34806
  · exact u34807
  · exact u34808
  · exact u34809
  · exact u34810
  · exact u34811

theorem m42298_6 : Upper (D 6) (R 6) [24,33,130,65,6] 13 :=
  permutation_upper _ _ _ [24,33,130,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34788

theorem m42298_34 : Upper (D 6) (R 6) [24,33,130,65,34] 13 :=
  permutation_upper _ _ _ [24,33,130,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34800

theorem m42298_36 : Upper (D 6) (R 6) [24,33,130,65,36] 13 :=
  permutation_upper _ _ _ [24,33,130,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34805

def r42298 : Route 9 := (fun mask => (mask,id))

def c42298 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42298 : Upper (D 6) (R 6) [24,33,130,65] 13 := by
  apply FastRouting.sound _ _ [24,33,130,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42298 c42298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42298_6
  · exact m42298_34
  · exact m42298_36
  · exact u34812
  · exact u34813
  · exact u34814
  · exact u34815
  · exact u34816
  · exact u34817
  · exact u34818

theorem m42299_5 : Upper (D 6) (R 6) [24,33,130,66,5] 13 :=
  permutation_upper _ _ _ [24,33,130,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34780

theorem m42299_33 : Upper (D 6) (R 6) [24,33,130,66,33] 13 :=
  permutation_upper _ _ _ [24,33,130,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34795

theorem m42299_36 : Upper (D 6) (R 6) [24,33,130,66,36] 13 :=
  permutation_upper _ _ _ [24,33,130,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34806

theorem m42299_65 : Upper (D 6) (R 6) [24,33,130,66,65] 13 :=
  permutation_upper _ _ _ [24,33,130,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34812

def r42299 : Route 9 := (fun mask => (mask,id))

def c42299 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42299 : Upper (D 6) (R 6) [24,33,130,66] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42299 c42299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42299_5
  · exact m42299_33
  · exact m42299_36
  · exact m42299_65
  · exact u34819
  · exact u34820
  · exact u34821
  · exact u34822
  · exact u34823
  · exact u34824

#print axioms u42299
end Delivery.IrregularNine14.P06
