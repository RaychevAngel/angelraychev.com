import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0040
import IrregularNine14P03C0041
import IrregularNine14P03C0042
import IrregularNine14P03C0043

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m5880_9 : Upper (D 3) (R 3) [6,33,192,288,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2439

theorem m5880_65 : Upper (D 3) (R 3) [6,33,192,288,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2455

theorem m5880_72 : Upper (D 3) (R 3) [6,33,192,288,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2461

theorem m5880_192 : Upper (D 3) (R 3) [6,33,192,288,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2468

def r5880 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5880 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5880 : Upper (D 3) (R 3) [6,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288] 13 (by decide) (choices 2) [9,65,72,192] r5880 c5880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5880_9
  · exact m5880_65
  · exact m5880_72
  · exact m5880_192

theorem m5881_9 : Upper (D 3) (R 3) [6,33,192,320,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2440

theorem m5881_33 : Upper (D 3) (R 3) [6,33,192,320,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2444

theorem m5881_40 : Upper (D 3) (R 3) [6,33,192,320,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2450

theorem m5881_129 : Upper (D 3) (R 3) [6,33,192,320,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2456

theorem m5881_136 : Upper (D 3) (R 3) [6,33,192,320,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2462

theorem m5881_160 : Upper (D 3) (R 3) [6,33,192,320,160] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2465

def r5881 : Route 9 := (fun mask => (mask,id))

def c5881 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u5881 : Upper (D 3) (R 3) [6,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r5881 c5881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5881_9
  · exact m5881_33
  · exact m5881_40
  · exact m5881_129
  · exact m5881_136
  · exact m5881_160

def b5882 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 25 248 232 232 232 488), lower := (rows 7 35 261 25 16 32 64 128 256), losses := [] }

theorem u5882 : Upper (D 3) (R 3) [6,33,257,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5882
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5883 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 261 41 216 248 216 216 472), lower := (rows 7 35 261 41 16 32 64 128 256), losses := [] }

theorem u5883 : Upper (D 3) (R 3) [6,33,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5883
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5884_9 : Upper (D 3) (R 3) [6,33,257,48,9] 13 :=
  permutation_upper _ _ _ [6,33,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2469

def r5884 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5884 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5884 : Upper (D 3) (R 3) [6,33,257,48] 13 := by
  apply FastRouting.sound _ _ [6,33,257,48] 13 (by decide) (choices 2) [9,65,72,192] r5884 c5884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5884_9
  · exact u2475
  · exact u2476
  · exact u2477

def b5885 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 73 248 248 248 248 504), lower := (rows 7 35 261 73 16 32 64 128 256), losses := [] }

theorem u5885 : Upper (D 3) (R 3) [6,33,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5885
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5886_9 : Upper (D 3) (R 3) [6,33,257,80,9] 13 :=
  permutation_upper _ _ _ [6,33,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2470

theorem m5886_33 : Upper (D 3) (R 3) [6,33,257,80,33] 13 :=
  permutation_upper _ _ _ [6,33,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2473

theorem m5886_40 : Upper (D 3) (R 3) [6,33,257,80,40] 13 :=
  permutation_upper _ _ _ [6,33,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2476

theorem m5886_65 : Upper (D 3) (R 3) [6,33,257,80,65] 13 :=
  permutation_upper _ _ _ [6,33,257,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2478

theorem m5886_129 : Upper (D 3) (R 3) [6,33,257,80,129] 13 :=
  permutation_upper _ _ _ [6,33,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2480

def r5886 : Route 9 := (fun mask => (mask,id))

def c5886 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5886 : Upper (D 3) (R 3) [6,33,257,80] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r5886 c5886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5886_9
  · exact m5886_33
  · exact m5886_40
  · exact m5886_65
  · exact u2483
  · exact u2484
  · exact m5886_129
  · exact u2485
  · exact u2486
  · exact u2487

theorem m5887_9 : Upper (D 3) (R 3) [6,33,257,96,9] 13 :=
  permutation_upper _ _ _ [6,33,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2471

theorem m5887_65 : Upper (D 3) (R 3) [6,33,257,96,65] 13 :=
  permutation_upper _ _ _ [6,33,257,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

theorem m5887_72 : Upper (D 3) (R 3) [6,33,257,96,72] 13 :=
  permutation_upper _ _ _ [6,33,257,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2484

theorem m5887_129 : Upper (D 3) (R 3) [6,33,257,96,129] 13 :=
  permutation_upper _ _ _ [6,33,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2481

theorem m5887_136 : Upper (D 3) (R 3) [6,33,257,96,136] 13 :=
  permutation_upper _ _ _ [6,33,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2486

def r5887 : Route 9 := (fun mask => (mask,id))

def c5887 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5887 : Upper (D 3) (R 3) [6,33,257,96] 13 := by
  apply FastRouting.sound _ _ [6,33,257,96] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5887 c5887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5887_9
  · exact m5887_65
  · exact m5887_72
  · exact m5887_129
  · exact m5887_136
  · exact u2488

theorem m5888_9 : Upper (D 3) (R 3) [6,33,257,192,9] 13 :=
  permutation_upper _ _ _ [6,33,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2472

theorem m5888_33 : Upper (D 3) (R 3) [6,33,257,192,33] 13 :=
  permutation_upper _ _ _ [6,33,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2474

theorem m5888_40 : Upper (D 3) (R 3) [6,33,257,192,40] 13 :=
  permutation_upper _ _ _ [6,33,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2477

theorem m5888_65 : Upper (D 3) (R 3) [6,33,257,192,65] 13 :=
  permutation_upper _ _ _ [6,33,257,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2482

theorem m5888_72 : Upper (D 3) (R 3) [6,33,257,192,72] 13 :=
  permutation_upper _ _ _ [6,33,257,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2487

theorem m5888_96 : Upper (D 3) (R 3) [6,33,257,192,96] 13 :=
  permutation_upper _ _ _ [6,33,257,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2488

def r5888 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5888 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5888 : Upper (D 3) (R 3) [6,33,257,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,192] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r5888 c5888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5888_9
  · exact m5888_33
  · exact m5888_40
  · exact m5888_65
  · exact m5888_72
  · exact m5888_96
  · exact u2489

def r5889 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5889 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5889 : Upper (D 3) (R 3) [6,33,264,17] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17] 13 (by decide) (choices 2) [33,65,96,192] r5889 c5889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2490
  · exact u2491
  · exact u2492
  · exact u2493

def b5890 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 268 41 209 241 209 209 465), lower := (rows 7 35 268 41 16 32 64 128 256), losses := [] }

theorem u5890 : Upper (D 3) (R 3) [6,33,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5890
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5891 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 268 56 209 225 193 193 449), lower := (rows 7 35 268 56 16 32 64 128 256), losses := [] }

theorem u5891 : Upper (D 3) (R 3) [6,33,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5891
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5892 : Route 9 := (fun mask => (mask,id))

def c5892 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5892 : Upper (D 3) (R 3) [6,33,264,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5892 c5892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2494
  · exact u2495
  · exact u2496
  · exact u2497
  · exact u2498
  · exact u2499

def r5893 : Route 9 := (fun mask => (mask,id))

def c5893 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5893 : Upper (D 3) (R 3) [6,33,264,80] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5893 c5893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2500
  · exact u2501
  · exact u2502
  · exact u2503
  · exact u2504
  · exact u2505

def b5894 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 268 104 209 241 209 209 465), lower := (rows 7 35 268 104 16 32 64 128 256), losses := [] }

theorem u5894 : Upper (D 3) (R 3) [6,33,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5894
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5895 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5895 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5895 : Upper (D 3) (R 3) [6,33,264,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192] 13 (by decide) (choices 2) [33,65,96,192] r5895 c5895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2506
  · exact u2507
  · exact u2508
  · exact u2509

def r5896 : Route 9 := (fun mask => (mask,id))

def c5896 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5896 : Upper (D 3) (R 3) [6,33,320,17] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r5896 c5896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2510
  · exact u2511
  · exact u2512
  · exact u2513
  · exact u2514
  · exact u2515
  · exact u2516
  · exact u2517
  · exact u2518
  · exact u2519

def b5897 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 217 249 217 217 473), lower := (rows 7 35 324 41 16 32 64 128 256), losses := [] }

theorem u5897 : Upper (D 3) (R 3) [6,33,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5897
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5898_9 : Upper (D 3) (R 3) [6,33,320,48,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2512

def r5898 : Route 9 := (fun mask => (mask,id))

def c5898 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5898 : Upper (D 3) (R 3) [6,33,320,48] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5898 c5898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5898_9
  · exact u2524
  · exact u2525
  · exact u2526
  · exact u2527
  · exact u2528

def b5899 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 73 185 185 249 185 441), lower := (rows 7 35 324 73 16 32 64 128 256), losses := [] }

theorem u5899 : Upper (D 3) (R 3) [6,33,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5899
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5900_9 : Upper (D 3) (R 3) [6,33,320,80,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2514

theorem m5900_33 : Upper (D 3) (R 3) [6,33,320,80,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2520

theorem m5900_40 : Upper (D 3) (R 3) [6,33,320,80,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2525

def r5900 : Route 9 := (fun mask => (mask,id))

def c5900 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u5900 : Upper (D 3) (R 3) [6,33,320,80] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r5900 c5900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5900_9
  · exact m5900_33
  · exact m5900_40
  · exact u2532
  · exact u2533
  · exact u2534

theorem m5901_9 : Upper (D 3) (R 3) [6,33,320,96,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2515

def r5901 : Route 9 := (fun mask => (mask,id))

def c5901 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u5901 : Upper (D 3) (R 3) [6,33,320,96] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96] 13 (by decide) (choices 2) [9,129,136] r5901 c5901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5901_9
  · exact u2535
  · exact u2536

theorem m5902_9 : Upper (D 3) (R 3) [6,33,320,129,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2516

theorem m5902_33 : Upper (D 3) (R 3) [6,33,320,129,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2521

theorem m5902_40 : Upper (D 3) (R 3) [6,33,320,129,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2526

theorem m5902_65 : Upper (D 3) (R 3) [6,33,320,129,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2529

theorem m5902_72 : Upper (D 3) (R 3) [6,33,320,129,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2532

theorem m5902_96 : Upper (D 3) (R 3) [6,33,320,129,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2535

def r5902 : Route 9 := (fun mask => (mask,id))

def c5902 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5902 : Upper (D 3) (R 3) [6,33,320,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r5902 c5902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5902_9
  · exact m5902_33
  · exact m5902_40
  · exact m5902_65
  · exact m5902_72
  · exact m5902_96
  · exact u2537
  · exact u2538
  · exact u2539
  · exact u2540

theorem m5903_9 : Upper (D 3) (R 3) [6,33,320,144,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2517

theorem m5903_33 : Upper (D 3) (R 3) [6,33,320,144,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2522

theorem m5903_40 : Upper (D 3) (R 3) [6,33,320,144,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2527

theorem m5903_65 : Upper (D 3) (R 3) [6,33,320,144,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2530

theorem m5903_72 : Upper (D 3) (R 3) [6,33,320,144,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2533

theorem m5903_96 : Upper (D 3) (R 3) [6,33,320,144,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2536

theorem m5903_129 : Upper (D 3) (R 3) [6,33,320,144,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2538

def r5903 : Route 9 := (fun mask => (mask,id))

def c5903 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5903 : Upper (D 3) (R 3) [6,33,320,144] 13 := by
  apply FastRouting.sound _ _ [6,33,320,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r5903 c5903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5903_9
  · exact m5903_33
  · exact m5903_40
  · exact m5903_65
  · exact m5903_72
  · exact m5903_96
  · exact m5903_129
  · exact u2541
  · exact u2542
  · exact u2543

theorem m5904_9 : Upper (D 3) (R 3) [6,33,320,160,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2518

theorem m5904_65 : Upper (D 3) (R 3) [6,33,320,160,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2531

theorem m5904_72 : Upper (D 3) (R 3) [6,33,320,160,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2534

theorem m5904_129 : Upper (D 3) (R 3) [6,33,320,160,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2539

theorem m5904_136 : Upper (D 3) (R 3) [6,33,320,160,136] 13 :=
  permutation_upper _ _ _ [6,33,320,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2542

def r5904 : Route 9 := (fun mask => (mask,id))

def c5904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5904 : Upper (D 3) (R 3) [6,33,320,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5904 c5904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5904_9
  · exact m5904_65
  · exact m5904_72
  · exact m5904_129
  · exact m5904_136
  · exact u2544

theorem m5905_9 : Upper (D 3) (R 3) [6,33,320,192,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2519

theorem m5905_33 : Upper (D 3) (R 3) [6,33,320,192,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2523

theorem m5905_40 : Upper (D 3) (R 3) [6,33,320,192,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2528

theorem m5905_129 : Upper (D 3) (R 3) [6,33,320,192,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2540

theorem m5905_136 : Upper (D 3) (R 3) [6,33,320,192,136] 13 :=
  permutation_upper _ _ _ [6,33,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2543

theorem m5905_160 : Upper (D 3) (R 3) [6,33,320,192,160] 13 :=
  permutation_upper _ _ _ [6,33,320,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2544

def r5905 : Route 9 := (fun mask => (mask,id))

def c5905 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u5905 : Upper (D 3) (R 3) [6,33,320,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r5905 c5905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5905_9
  · exact m5905_33
  · exact m5905_40
  · exact m5905_129
  · exact m5905_136
  · exact m5905_160

def b5906 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 41 465 481 449 449 449), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u5906 : Upper (D 3) (R 3) [6,40,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5906
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5907 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 73 433 417 481 417 417), lower := (rows 7 42 84 73 16 32 64 128 256), losses := [] }

theorem u5907 : Upper (D 3) (R 3) [6,40,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5907
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5908 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 104 401 417 449 385 385), lower := (rows 7 42 84 104 16 32 64 128 256), losses := [] }

theorem u5908 : Upper (D 3) (R 3) [6,40,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5908
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5909_33 : Upper (D 3) (R 3) [6,40,80,129,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2548

theorem m5909_65 : Upper (D 3) (R 3) [6,40,80,129,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2545

theorem m5909_96 : Upper (D 3) (R 3) [6,40,80,129,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2551

def r5909 : Route 9 := (fun mask => (mask,id))

def c5909 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5909 : Upper (D 3) (R 3) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5909 c5909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5909_33
  · exact m5909_65
  · exact m5909_96
  · exact u2554
  · exact u2555
  · exact u2556
  · exact u2557
  · exact u2558
  · exact u2559
  · exact u2560

def b5910 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 168 465 481 449 449 449), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u5910 : Upper (D 3) (R 3) [6,40,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5911 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 200 433 417 481 417 417), lower := (rows 7 42 84 200 16 32 64 128 256), losses := [] }

theorem u5911 : Upper (D 3) (R 3) [6,40,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5911
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5912_33 : Upper (D 3) (R 3) [6,40,80,257,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2549

theorem m5912_65 : Upper (D 3) (R 3) [6,40,80,257,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2546

theorem m5912_96 : Upper (D 3) (R 3) [6,40,80,257,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2552

theorem m5912_129 : Upper (D 3) (R 3) [6,40,80,257,129] 13 :=
  permutation_upper _ _ _ [6,40,80,129,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2557

theorem m5912_160 : Upper (D 3) (R 3) [6,40,80,257,160] 13 :=
  permutation_upper _ _ _ [6,40,80,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2563

theorem m5912_192 : Upper (D 3) (R 3) [6,40,80,257,192] 13 :=
  permutation_upper _ _ _ [6,40,80,160,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2561

def r5912 : Route 9 := (fun mask => (mask,id))

def c5912 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5912 : Upper (D 3) (R 3) [6,40,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5912 c5912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5912_33
  · exact m5912_65
  · exact m5912_96
  · exact m5912_129
  · exact m5912_160
  · exact m5912_192

def b5913 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 296 209 225 193 193 449), lower := (rows 7 42 84 296 16 32 64 128 256), losses := [] }

theorem u5913 : Upper (D 3) (R 3) [6,40,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5913
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5914 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 328 177 161 225 161 417), lower := (rows 7 42 84 328 16 32 64 128 256), losses := [] }

theorem u5914 : Upper (D 3) (R 3) [6,40,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5914
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5915_33 : Upper (D 3) (R 3) [6,40,80,384,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2550

theorem m5915_65 : Upper (D 3) (R 3) [6,40,80,384,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2547

theorem m5915_96 : Upper (D 3) (R 3) [6,40,80,384,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2553

theorem m5915_129 : Upper (D 3) (R 3) [6,40,80,384,129] 13 :=
  permutation_upper _ _ _ [6,40,80,129,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2560

theorem m5915_160 : Upper (D 3) (R 3) [6,40,80,384,160] 13 :=
  permutation_upper _ _ _ [6,40,80,192,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2564

theorem m5915_192 : Upper (D 3) (R 3) [6,40,80,384,192] 13 :=
  permutation_upper _ _ _ [6,40,80,160,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2562

def r5915 : Route 9 := (fun mask => (mask,id))

def c5915 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5915 : Upper (D 3) (R 3) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5915 c5915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5915_33
  · exact m5915_65
  · exact m5915_96
  · exact m5915_129
  · exact m5915_160
  · exact m5915_192

def r5916 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5916 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5916 : Upper (D 3) (R 3) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r5916 c5916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2565
  · exact u2566
  · exact u2567
  · exact u2568
  · exact u2569
  · exact u2570
  · exact u2571

def b5917 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 41 465 497 465 465 465), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u5917 : Upper (D 3) (R 3) [6,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5917
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 56 465 481 449 449 449), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u5918 : Upper (D 3) (R 3) [6,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5919 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 73 433 433 497 433 433), lower := (rows 7 42 196 73 16 32 64 128 256), losses := [] }

theorem u5919 : Upper (D 3) (R 3) [6,40,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5919
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5920 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 88 433 417 481 417 417), lower := (rows 7 42 196 88 16 32 64 128 256), losses := [] }

theorem u5920 : Upper (D 3) (R 3) [6,40,192,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5920
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 104 401 433 465 401 401), lower := (rows 7 42 196 104 16 32 64 128 256), losses := [] }

theorem u5921 : Upper (D 3) (R 3) [6,40,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5921
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5922 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 196 200 305 305 369 433 305), lower := (rows 7 42 196 200 16 32 64 128 256), losses := [] }

theorem u5922 : Upper (D 3) (R 3) [6,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5922
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5923 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5923 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5923 : Upper (D 3) (R 3) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [33,65,96,192] r5923 c5923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2572
  · exact u2573
  · exact u2574
  · exact u2575

def r5924 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5924 : Upper (D 3) (R 3) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [33,65,96,192] r5924 c5924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2576
  · exact u2577
  · exact u2578
  · exact u2579

def b5925 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 296 209 241 209 209 465), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u5925 : Upper (D 3) (R 3) [6,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5925
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5926 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 328 177 177 241 177 433), lower := (rows 7 42 196 328 16 32 64 128 256), losses := [] }

theorem u5926 : Upper (D 3) (R 3) [6,40,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5926
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5927 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5927 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5927 : Upper (D 3) (R 3) [6,40,257,17] 13 := by
  apply FastRouting.sound _ _ [6,40,257,17] 13 (by decide) (choices 2) [33,65,96,192] r5927 c5927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2580
  · exact u2581
  · exact u2582
  · exact u2583

def b5928 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 261 41 209 241 209 209 465), lower := (rows 7 42 261 41 16 32 64 128 256), losses := [] }

theorem u5928 : Upper (D 3) (R 3) [6,40,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5928
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 261 56 209 225 193 193 449), lower := (rows 7 42 261 56 16 32 64 128 256), losses := [] }

theorem u5929 : Upper (D 3) (R 3) [6,40,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5929
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5930 : Route 9 := (fun mask => (mask,id))

def c5930 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5930 : Upper (D 3) (R 3) [6,40,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5930 c5930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2584
  · exact u2585
  · exact u2586
  · exact u2587
  · exact u2588
  · exact u2589

def r5931 : Route 9 := (fun mask => (mask,id))

def c5931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5931 : Upper (D 3) (R 3) [6,40,257,80] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5931 c5931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2590
  · exact u2591
  · exact u2592
  · exact u2593
  · exact u2594
  · exact u2595

def b5932 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 261 104 209 241 209 209 465), lower := (rows 7 42 261 104 16 32 64 128 256), losses := [] }

theorem u5932 : Upper (D 3) (R 3) [6,40,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5932
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5933 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5933 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5933 : Upper (D 3) (R 3) [6,40,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192] 13 (by decide) (choices 2) [33,65,96,192] r5933 c5933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2596
  · exact u2597
  · exact u2598
  · exact u2599

def b5934 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 276 41 209 225 193 193 449), lower := (rows 7 42 276 41 16 32 64 128 256), losses := [] }

theorem u5934 : Upper (D 3) (R 3) [6,40,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5935 : Route 9 := (fun mask => (mask,id))

def c5935 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5935 : Upper (D 3) (R 3) [6,40,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5935 c5935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2600
  · exact u2601
  · exact u2602
  · exact u2603
  · exact u2604
  · exact u2605

def b5936 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 276 104 209 225 193 193 449), lower := (rows 7 42 276 104 16 32 64 128 256), losses := [] }

theorem u5936 : Upper (D 3) (R 3) [6,40,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5936
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5937 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5937 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5937 : Upper (D 3) (R 3) [6,40,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192] 13 (by decide) (choices 2) [33,65,96,192] r5937 c5937
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2606
  · exact u2607
  · exact u2608
  · exact u2609

def r5938 : Route 9 := (fun mask => (mask,id))

def c5938 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5938 : Upper (D 3) (R 3) [6,40,320,17] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5938 c5938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2610
  · exact u2611
  · exact u2612
  · exact u2613
  · exact u2614
  · exact u2615

def b5939 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 41 209 241 209 209 465), lower := (rows 7 42 324 41 16 32 64 128 256), losses := [] }

theorem u5939 : Upper (D 3) (R 3) [6,40,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5939
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5939
end Delivery.IrregularNine14.P03
