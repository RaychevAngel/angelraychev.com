import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0492
import IrregularNine14P06C0493
import IrregularNine14P06C0494
import IrregularNine14P06C0495
import IrregularNine14P06C0496

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m41040_12 : Upper (D 6) (R 6) [6,129,257,34,12] 13 :=
  permutation_upper _ _ _ [6,129,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29537

def r41040 : Route 9 := (fun mask => (mask,id))

def c41040 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41040 : Upper (D 6) (R 6) [6,129,257,34] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34] 13 (by decide) (choices 2) [12,36,40,68,72,96] r41040 c41040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41040_12
  · exact u29540
  · exact u29541
  · exact u29542
  · exact u29543
  · exact u29544

theorem m41041_6 : Upper (D 6) (R 6) [6,129,257,48,6] 13 :=
  permutation_upper _ _ _ [6,129,257,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29534

theorem m41041_10 : Upper (D 6) (R 6) [6,129,257,48,10] 13 :=
  permutation_upper _ _ _ [6,129,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29538

theorem m41041_12 : Upper (D 6) (R 6) [6,129,257,48,12] 13 :=
  permutation_upper _ _ _ [6,129,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29538

theorem m41041_34 : Upper (D 6) (R 6) [6,129,257,48,34] 13 :=
  permutation_upper _ _ _ [6,129,257,34,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29541

theorem m41041_36 : Upper (D 6) (R 6) [6,129,257,48,36] 13 :=
  permutation_upper _ _ _ [6,129,257,34,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29541

theorem m41041_66 : Upper (D 6) (R 6) [6,129,257,48,66] 13 :=
  permutation_upper _ _ _ [6,129,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29543

theorem m41041_68 : Upper (D 6) (R 6) [6,129,257,48,68] 13 :=
  permutation_upper _ _ _ [6,129,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29543

def r41041 : Route 9 := (fun mask => (mask,id))

def c41041 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41041 : Upper (D 6) (R 6) [6,129,257,48] 13 := by
  apply FastRouting.sound _ _ [6,129,257,48] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r41041 c41041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41041_6
  · exact m41041_10
  · exact m41041_12
  · exact m41041_34
  · exact m41041_36
  · exact u29545
  · exact m41041_66
  · exact m41041_68
  · exact u29546
  · exact u29547

theorem m41042_6 : Upper (D 6) (R 6) [6,129,257,96,6] 13 :=
  permutation_upper _ _ _ [6,129,257,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29535

theorem m41042_10 : Upper (D 6) (R 6) [6,129,257,96,10] 13 :=
  permutation_upper _ _ _ [6,129,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29539

theorem m41042_12 : Upper (D 6) (R 6) [6,129,257,96,12] 13 :=
  permutation_upper _ _ _ [6,129,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29539

theorem m41042_34 : Upper (D 6) (R 6) [6,129,257,96,34] 13 :=
  permutation_upper _ _ _ [6,129,257,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29544

theorem m41042_36 : Upper (D 6) (R 6) [6,129,257,96,36] 13 :=
  permutation_upper _ _ _ [6,129,257,34,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29544

theorem m41042_40 : Upper (D 6) (R 6) [6,129,257,96,40] 13 :=
  permutation_upper _ _ _ [6,129,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29547

def r41042 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41042 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41042 : Upper (D 6) (R 6) [6,129,257,96] 13 := by
  apply FastRouting.sound _ _ [6,129,257,96] 13 (by decide) (choices 2) [6,10,12,34,36,40,96] r41042 c41042
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41042_6
  · exact m41042_10
  · exact m41042_12
  · exact m41042_34
  · exact m41042_36
  · exact m41042_40
  · exact u29548

def b41043 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 11 116 116 116 244 372), lower := (rows 7 131 268 11 16 32 64 128 256), losses := [] }

theorem u41043 : Upper (D 6) (R 6) [6,129,264,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41043
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41044 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 268 13 114 114 114 242 370), lower := (rows 7 131 268 13 16 32 64 128 256), losses := [] }

theorem u41044 : Upper (D 6) (R 6) [6,129,264,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41044
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41045 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 242, targets := 4 },{ cop := 0, region := 8, targets := 32 }], pairs := [(1,2),(3,5),(4,2)], upper := (rows 7 131 268 14 113 113 113 241 369), lower := (rows 7 131 268 14 16 32 64 128 256), losses := [] }

theorem u41045 : Upper (D 6) (R 6) [6,129,264,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41045
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41046 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41046 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41046 : Upper (D 6) (R 6) [6,129,264,17] 13 := by
  apply FastRouting.sound _ _ [6,129,264,17] 13 (by decide) (choices 2) [6,34,36,96] r41046 c41046
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29549
  · exact u29550
  · exact u29551
  · exact u29552

def r41047 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41047 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41047 : Upper (D 6) (R 6) [6,129,264,18] 13 := by
  apply FastRouting.sound _ _ [6,129,264,18] 13 (by decide) (choices 2) [5,33,36,96] r41047 c41047
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29553
  · exact u29554
  · exact u29555
  · exact u29556

def r41048 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41048 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41048 : Upper (D 6) (R 6) [6,129,264,20] 13 := by
  apply FastRouting.sound _ _ [6,129,264,20] 13 (by decide) (choices 2) [3,33,34,96] r41048 c41048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29557
  · exact u29558
  · exact u29559
  · exact u29560

def r41049 : Route 9 := (fun mask => (mask,id))

def c41049 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41049 : Upper (D 6) (R 6) [6,129,264,33] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41049 c41049
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29561
  · exact u29562
  · exact u29563
  · exact u29564
  · exact u29565
  · exact u29566

def r41050 : Route 9 := (fun mask => (mask,id))

def c41050 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41050 : Upper (D 6) (R 6) [6,129,264,34] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41050 c41050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29567
  · exact u29568
  · exact u29569
  · exact u29570
  · exact u29571
  · exact u29572

def r41051 : Route 9 := (fun mask => (mask,id))

def c41051 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41051 : Upper (D 6) (R 6) [6,129,264,36] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41051 c41051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29573
  · exact u29574
  · exact u29575
  · exact u29576
  · exact u29577
  · exact u29578

def r41052 : Route 9 := (fun mask => (mask,id))

def c41052 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41052 : Upper (D 6) (R 6) [6,129,264,48] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41052 c41052
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29579
  · exact u29580
  · exact u29581
  · exact u29582
  · exact u29583
  · exact u29584
  · exact u29585
  · exact u29586
  · exact u29587
  · exact u29588

def r41053 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41053 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41053 : Upper (D 6) (R 6) [6,129,264,96] 13 := by
  apply FastRouting.sound _ _ [6,129,264,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41053 c41053
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29589
  · exact u29590
  · exact u29591
  · exact u29592
  · exact u29593
  · exact u29594
  · exact u29595

def b41054 : PairBound 9 := { available := 124, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 11 124 124 124 252 380), lower := (rows 7 131 292 11 16 32 64 128 256), losses := [] }

theorem u41054 : Upper (D 6) (R 6) [6,129,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41054
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41055 : PairBound 9 := { available := 122, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 13 122 122 122 250 378), lower := (rows 7 131 292 13 16 32 64 128 256), losses := [] }

theorem u41055 : Upper (D 6) (R 6) [6,129,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41055
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41056 : PairBound 9 := { available := 121, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 131 292 14 121 121 121 249 377), lower := (rows 7 131 292 14 16 32 64 128 256), losses := [] }

theorem u41056 : Upper (D 6) (R 6) [6,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41056
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41057_6 : Upper (D 6) (R 6) [6,129,288,17,6] 13 :=
  permutation_upper _ _ _ [6,129,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29607

def r41057 : Route 9 := (fun mask => (mask,id))

def c41057 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41057 : Upper (D 6) (R 6) [6,129,288,17] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r41057 c41057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41057_6
  · exact u29613
  · exact u29614
  · exact u29615
  · exact u29616
  · exact u29617
  · exact u29618
  · exact u29619
  · exact u29620
  · exact u29621

theorem m41058_5 : Upper (D 6) (R 6) [6,129,288,18,5] 13 :=
  permutation_upper _ _ _ [6,129,288,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29601

theorem m41058_9 : Upper (D 6) (R 6) [6,129,288,18,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29613

def r41058 : Route 9 := (fun mask => (mask,id))

def c41058 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41058 : Upper (D 6) (R 6) [6,129,288,18] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r41058 c41058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41058_5
  · exact m41058_9
  · exact u29622
  · exact u29623
  · exact u29624
  · exact u29625
  · exact u29626
  · exact u29627
  · exact u29628
  · exact u29629

theorem m41059_3 : Upper (D 6) (R 6) [6,129,288,20,3] 13 :=
  permutation_upper _ _ _ [6,129,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29596

theorem m41059_9 : Upper (D 6) (R 6) [6,129,288,20,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29614

theorem m41059_10 : Upper (D 6) (R 6) [6,129,288,20,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29622

def r41059 : Route 9 := (fun mask => (mask,id))

def c41059 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41059 : Upper (D 6) (R 6) [6,129,288,20] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r41059 c41059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41059_3
  · exact m41059_9
  · exact m41059_10
  · exact u29630
  · exact u29631
  · exact u29632
  · exact u29633
  · exact u29634
  · exact u29635
  · exact u29636

theorem m41060_6 : Upper (D 6) (R 6) [6,129,288,33,6] 13 :=
  permutation_upper _ _ _ [6,129,288,6,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29608

theorem m41060_10 : Upper (D 6) (R 6) [6,129,288,33,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29623

theorem m41060_12 : Upper (D 6) (R 6) [6,129,288,33,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29630

def r41060 : Route 9 := (fun mask => (mask,id))

def c41060 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41060 : Upper (D 6) (R 6) [6,129,288,33] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33] 13 (by decide) (choices 2) [6,10,12,66,68,72] r41060 c41060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41060_6
  · exact m41060_10
  · exact m41060_12
  · exact u29637
  · exact u29638
  · exact u29639

theorem m41061_5 : Upper (D 6) (R 6) [6,129,288,34,5] 13 :=
  permutation_upper _ _ _ [6,129,288,5,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29602

theorem m41061_9 : Upper (D 6) (R 6) [6,129,288,34,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29615

theorem m41061_12 : Upper (D 6) (R 6) [6,129,288,34,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29631

def r41061 : Route 9 := (fun mask => (mask,id))

def c41061 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41061 : Upper (D 6) (R 6) [6,129,288,34] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34] 13 (by decide) (choices 2) [5,9,12,65,68,72] r41061 c41061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41061_5
  · exact m41061_9
  · exact m41061_12
  · exact u29640
  · exact u29641
  · exact u29642

def b41062 : PairBound 9 := { available := 91, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 131 292 44 91 123 91 219 347), lower := (rows 7 131 292 44 16 32 64 128 256), losses := [] }

theorem u41062 : Upper (D 6) (R 6) [6,129,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41062
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41063_3 : Upper (D 6) (R 6) [6,129,288,48,3] 13 :=
  permutation_upper _ _ _ [6,129,288,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29597

theorem m41063_5 : Upper (D 6) (R 6) [6,129,288,48,5] 13 :=
  permutation_upper _ _ _ [6,129,288,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29603

theorem m41063_6 : Upper (D 6) (R 6) [6,129,288,48,6] 13 :=
  permutation_upper _ _ _ [6,129,288,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29609

theorem m41063_9 : Upper (D 6) (R 6) [6,129,288,48,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29617

theorem m41063_10 : Upper (D 6) (R 6) [6,129,288,48,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29625

theorem m41063_12 : Upper (D 6) (R 6) [6,129,288,48,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29632

def r41063 : Route 9 := (fun mask => (mask,id))

def c41063 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41063 : Upper (D 6) (R 6) [6,129,288,48] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41063 c41063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41063_3
  · exact m41063_5
  · exact m41063_6
  · exact m41063_9
  · exact m41063_10
  · exact m41063_12
  · exact u29646
  · exact u29647
  · exact u29648
  · exact u29649

theorem m41064_6 : Upper (D 6) (R 6) [6,129,288,65,6] 13 :=
  permutation_upper _ _ _ [6,129,288,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29610

theorem m41064_10 : Upper (D 6) (R 6) [6,129,288,65,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29626

theorem m41064_12 : Upper (D 6) (R 6) [6,129,288,65,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29633

theorem m41064_34 : Upper (D 6) (R 6) [6,129,288,65,34] 13 :=
  permutation_upper _ _ _ [6,129,288,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29640

theorem m41064_36 : Upper (D 6) (R 6) [6,129,288,65,36] 13 :=
  permutation_upper _ _ _ [6,129,288,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29643

theorem m41064_40 : Upper (D 6) (R 6) [6,129,288,65,40] 13 :=
  permutation_upper _ _ _ [6,129,288,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29646

def r41064 : Route 9 := (fun mask => (mask,id))

def c41064 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41064 : Upper (D 6) (R 6) [6,129,288,65] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r41064 c41064
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41064_6
  · exact m41064_10
  · exact m41064_12
  · exact m41064_34
  · exact m41064_36
  · exact m41064_40
  · exact u29650
  · exact u29651
  · exact u29652
  · exact u29653

theorem m41065_5 : Upper (D 6) (R 6) [6,129,288,66,5] 13 :=
  permutation_upper _ _ _ [6,129,288,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29604

theorem m41065_9 : Upper (D 6) (R 6) [6,129,288,66,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29618

theorem m41065_12 : Upper (D 6) (R 6) [6,129,288,66,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29634

theorem m41065_33 : Upper (D 6) (R 6) [6,129,288,66,33] 13 :=
  permutation_upper _ _ _ [6,129,288,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29637

theorem m41065_36 : Upper (D 6) (R 6) [6,129,288,66,36] 13 :=
  permutation_upper _ _ _ [6,129,288,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29644

theorem m41065_40 : Upper (D 6) (R 6) [6,129,288,66,40] 13 :=
  permutation_upper _ _ _ [6,129,288,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29647

theorem m41065_65 : Upper (D 6) (R 6) [6,129,288,66,65] 13 :=
  permutation_upper _ _ _ [6,129,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29650

def r41065 : Route 9 := (fun mask => (mask,id))

def c41065 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41065 : Upper (D 6) (R 6) [6,129,288,66] 13 := by
  apply FastRouting.sound _ _ [6,129,288,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r41065 c41065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41065_5
  · exact m41065_9
  · exact m41065_12
  · exact m41065_33
  · exact m41065_36
  · exact m41065_40
  · exact m41065_65
  · exact u29654
  · exact u29655
  · exact u29656

theorem m41066_3 : Upper (D 6) (R 6) [6,129,288,68,3] 13 :=
  permutation_upper _ _ _ [6,129,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29598

theorem m41066_9 : Upper (D 6) (R 6) [6,129,288,68,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29619

theorem m41066_10 : Upper (D 6) (R 6) [6,129,288,68,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29627

theorem m41066_33 : Upper (D 6) (R 6) [6,129,288,68,33] 13 :=
  permutation_upper _ _ _ [6,129,288,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29638

theorem m41066_34 : Upper (D 6) (R 6) [6,129,288,68,34] 13 :=
  permutation_upper _ _ _ [6,129,288,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29641

theorem m41066_40 : Upper (D 6) (R 6) [6,129,288,68,40] 13 :=
  permutation_upper _ _ _ [6,129,288,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29648

theorem m41066_65 : Upper (D 6) (R 6) [6,129,288,68,65] 13 :=
  permutation_upper _ _ _ [6,129,288,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29651

theorem m41066_66 : Upper (D 6) (R 6) [6,129,288,68,66] 13 :=
  permutation_upper _ _ _ [6,129,288,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29654

def r41066 : Route 9 := (fun mask => (mask,id))

def c41066 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41066 : Upper (D 6) (R 6) [6,129,288,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,68] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r41066 c41066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41066_3
  · exact m41066_9
  · exact m41066_10
  · exact m41066_33
  · exact m41066_34
  · exact m41066_40
  · exact m41066_65
  · exact m41066_66
  · exact u29657
  · exact u29658

theorem m41067_3 : Upper (D 6) (R 6) [6,129,288,80,3] 13 :=
  permutation_upper _ _ _ [6,129,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29599

theorem m41067_5 : Upper (D 6) (R 6) [6,129,288,80,5] 13 :=
  permutation_upper _ _ _ [6,129,288,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29605

theorem m41067_6 : Upper (D 6) (R 6) [6,129,288,80,6] 13 :=
  permutation_upper _ _ _ [6,129,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29611

theorem m41067_9 : Upper (D 6) (R 6) [6,129,288,80,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29620

theorem m41067_10 : Upper (D 6) (R 6) [6,129,288,80,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29628

theorem m41067_12 : Upper (D 6) (R 6) [6,129,288,80,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29635

theorem m41067_33 : Upper (D 6) (R 6) [6,129,288,80,33] 13 :=
  permutation_upper _ _ _ [6,129,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29639

theorem m41067_34 : Upper (D 6) (R 6) [6,129,288,80,34] 13 :=
  permutation_upper _ _ _ [6,129,288,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29642

theorem m41067_36 : Upper (D 6) (R 6) [6,129,288,80,36] 13 :=
  permutation_upper _ _ _ [6,129,288,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29645

theorem m41067_40 : Upper (D 6) (R 6) [6,129,288,80,40] 13 :=
  permutation_upper _ _ _ [6,129,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29649

theorem m41067_65 : Upper (D 6) (R 6) [6,129,288,80,65] 13 :=
  permutation_upper _ _ _ [6,129,288,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29652

theorem m41067_66 : Upper (D 6) (R 6) [6,129,288,80,66] 13 :=
  permutation_upper _ _ _ [6,129,288,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29655

theorem m41067_68 : Upper (D 6) (R 6) [6,129,288,80,68] 13 :=
  permutation_upper _ _ _ [6,129,288,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29657

def r41067 : Route 9 := (fun mask => (mask,id))

def c41067 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41067 : Upper (D 6) (R 6) [6,129,288,80] 13 := by
  apply FastRouting.sound _ _ [6,129,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r41067 c41067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41067_3
  · exact m41067_5
  · exact m41067_6
  · exact m41067_9
  · exact m41067_10
  · exact m41067_12
  · exact m41067_33
  · exact m41067_34
  · exact m41067_36
  · exact m41067_40
  · exact m41067_65
  · exact m41067_66
  · exact m41067_68
  · exact u29659
  · exact u29660

theorem m41068_3 : Upper (D 6) (R 6) [6,129,288,96,3] 13 :=
  permutation_upper _ _ _ [6,129,288,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29600

theorem m41068_5 : Upper (D 6) (R 6) [6,129,288,96,5] 13 :=
  permutation_upper _ _ _ [6,129,288,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29606

theorem m41068_6 : Upper (D 6) (R 6) [6,129,288,96,6] 13 :=
  permutation_upper _ _ _ [6,129,288,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29612

theorem m41068_9 : Upper (D 6) (R 6) [6,129,288,96,9] 13 :=
  permutation_upper _ _ _ [6,129,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29621

theorem m41068_10 : Upper (D 6) (R 6) [6,129,288,96,10] 13 :=
  permutation_upper _ _ _ [6,129,288,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29629

theorem m41068_12 : Upper (D 6) (R 6) [6,129,288,96,12] 13 :=
  permutation_upper _ _ _ [6,129,288,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29636

theorem m41068_65 : Upper (D 6) (R 6) [6,129,288,96,65] 13 :=
  permutation_upper _ _ _ [6,129,288,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29653

theorem m41068_66 : Upper (D 6) (R 6) [6,129,288,96,66] 13 :=
  permutation_upper _ _ _ [6,129,288,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29656

theorem m41068_68 : Upper (D 6) (R 6) [6,129,288,96,68] 13 :=
  permutation_upper _ _ _ [6,129,288,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29658

theorem m41068_72 : Upper (D 6) (R 6) [6,129,288,96,72] 13 :=
  permutation_upper _ _ _ [6,129,288,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29660

def r41068 : Route 9 := (fun mask => (mask,id))

def c41068 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41068 : Upper (D 6) (R 6) [6,129,288,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41068 c41068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41068_3
  · exact m41068_5
  · exact m41068_6
  · exact m41068_9
  · exact m41068_10
  · exact m41068_12
  · exact m41068_65
  · exact m41068_66
  · exact m41068_68
  · exact m41068_72

def b41069 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 138 276 11 117 101 101 229 357), lower := (rows 7 138 276 11 16 32 64 128 256), losses := [] }

theorem u41069 : Upper (D 6) (R 6) [6,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41069
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41070 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 138 276 13 115 99 99 227 355), lower := (rows 7 138 276 13 16 32 64 128 256), losses := [] }

theorem u41070 : Upper (D 6) (R 6) [6,136,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41070
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41071 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 276 14 113 97 97 225 353), lower := (rows 7 138 276 14 16 32 64 128 256), losses := [] }

theorem u41071 : Upper (D 6) (R 6) [6,136,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41071
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41072_3 : Upper (D 6) (R 6) [6,136,272,33,3] 13 :=
  permutation_upper _ _ _ [6,136,272,5,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29664

theorem m41072_5 : Upper (D 6) (R 6) [6,136,272,33,5] 13 :=
  permutation_upper _ _ _ [6,136,272,3,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29661

theorem m41072_6 : Upper (D 6) (R 6) [6,136,272,33,6] 13 :=
  permutation_upper _ _ _ [6,136,272,6,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29667

def r41072 : Route 9 := (fun mask => (mask,id))

def c41072 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41072 : Upper (D 6) (R 6) [6,136,272,33] 13 := by
  apply FastRouting.sound _ _ [6,136,272,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41072 c41072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41072_3
  · exact m41072_5
  · exact m41072_6
  · exact u29669
  · exact u29670
  · exact u29671
  · exact u29672
  · exact u29673
  · exact u29674
  · exact u29675

theorem m41073_5 : Upper (D 6) (R 6) [6,136,272,34,5] 13 :=
  permutation_upper _ _ _ [6,136,272,3,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29662

theorem m41073_33 : Upper (D 6) (R 6) [6,136,272,34,33] 13 :=
  permutation_upper _ _ _ [6,136,272,33,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29671

theorem m41073_65 : Upper (D 6) (R 6) [6,136,272,34,65] 13 :=
  permutation_upper _ _ _ [6,136,272,33,68] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29674

def r41073 : Route 9 := (fun mask => (mask,id))

def c41073 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41073 : Upper (D 6) (R 6) [6,136,272,34] 13 := by
  apply FastRouting.sound _ _ [6,136,272,34] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41073 c41073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41073_5
  · exact m41073_33
  · exact u29676
  · exact m41073_65
  · exact u29677
  · exact u29678

theorem m41074_3 : Upper (D 6) (R 6) [6,136,272,36,3] 13 :=
  permutation_upper _ _ _ [6,136,272,5,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29665

theorem m41074_33 : Upper (D 6) (R 6) [6,136,272,36,33] 13 :=
  permutation_upper _ _ _ [6,136,272,33,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29670

theorem m41074_65 : Upper (D 6) (R 6) [6,136,272,36,65] 13 :=
  permutation_upper _ _ _ [6,136,272,33,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29673

def r41074 : Route 9 := (fun mask => (mask,id))

def c41074 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41074 : Upper (D 6) (R 6) [6,136,272,36] 13 := by
  apply FastRouting.sound _ _ [6,136,272,36] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41074 c41074
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41074_3
  · exact m41074_33
  · exact u29679
  · exact m41074_65
  · exact u29680
  · exact u29681

theorem m41075_3 : Upper (D 6) (R 6) [6,136,272,96,3] 13 :=
  permutation_upper _ _ _ [6,136,272,5,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29666

theorem m41075_5 : Upper (D 6) (R 6) [6,136,272,96,5] 13 :=
  permutation_upper _ _ _ [6,136,272,3,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29663

theorem m41075_6 : Upper (D 6) (R 6) [6,136,272,96,6] 13 :=
  permutation_upper _ _ _ [6,136,272,6,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29668

theorem m41075_33 : Upper (D 6) (R 6) [6,136,272,96,33] 13 :=
  permutation_upper _ _ _ [6,136,272,33,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29675

theorem m41075_34 : Upper (D 6) (R 6) [6,136,272,96,34] 13 :=
  permutation_upper _ _ _ [6,136,272,36,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29681

theorem m41075_36 : Upper (D 6) (R 6) [6,136,272,96,36] 13 :=
  permutation_upper _ _ _ [6,136,272,34,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29678

def r41075 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41075 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41075 : Upper (D 6) (R 6) [6,136,272,96] 13 := by
  apply FastRouting.sound _ _ [6,136,272,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41075 c41075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41075_3
  · exact m41075_5
  · exact m41075_6
  · exact m41075_33
  · exact m41075_34
  · exact m41075_36
  · exact u29682

def b41076 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 138 292 11 117 117 117 245 373), lower := (rows 7 138 292 11 16 32 64 128 256), losses := [] }

theorem u41076 : Upper (D 6) (R 6) [6,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41076
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41077 : PairBound 9 := { available := 115, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 138 292 13 115 115 115 243 371), lower := (rows 7 138 292 13 16 32 64 128 256), losses := [] }

theorem u41077 : Upper (D 6) (R 6) [6,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41077
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41078 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 292 14 113 113 113 241 369), lower := (rows 7 138 292 14 16 32 64 128 256), losses := [] }

theorem u41078 : Upper (D 6) (R 6) [6,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41078
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41079 : Route 9 := (fun mask => (mask,id))

def c41079 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41079 : Upper (D 6) (R 6) [6,136,288,17] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41079 c41079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29683
  · exact u29684
  · exact u29685
  · exact u29686
  · exact u29687
  · exact u29688
  · exact u29689
  · exact u29690
  · exact u29691
  · exact u29692

def r41080 : Route 9 := (fun mask => (mask,id))

def c41080 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41080 : Upper (D 6) (R 6) [6,136,288,18] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41080 c41080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29693
  · exact u29694
  · exact u29695
  · exact u29696
  · exact u29697
  · exact u29698

def r41081 : Route 9 := (fun mask => (mask,id))

def c41081 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41081 : Upper (D 6) (R 6) [6,136,288,20] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41081 c41081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29699
  · exact u29700
  · exact u29701
  · exact u29702
  · exact u29703
  · exact u29704

def r41082 : Route 9 := (fun mask => (mask,id))

def c41082 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41082 : Upper (D 6) (R 6) [6,136,288,33] 13 := by
  apply FastRouting.sound _ _ [6,136,288,33] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41082 c41082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29705
  · exact u29706
  · exact u29707
  · exact u29708
  · exact u29709
  · exact u29710

def b41083 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 138 292 42 85 117 85 213 341), lower := (rows 7 138 292 42 16 32 64 128 256), losses := [] }

theorem u41083 : Upper (D 6) (R 6) [6,136,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41083
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41084 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 138 292 44 83 115 83 211 339), lower := (rows 7 138 292 44 16 32 64 128 256), losses := [] }

theorem u41084 : Upper (D 6) (R 6) [6,136,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41084
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41085 : Route 9 := (fun mask => (mask,id))

def c41085 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41085 : Upper (D 6) (R 6) [6,136,288,48] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41085 c41085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29711
  · exact u29712
  · exact u29713
  · exact u29714
  · exact u29715
  · exact u29716

def r41086 : Route 9 := (fun mask => (mask,id))

def c41086 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41086 : Upper (D 6) (R 6) [6,136,288,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41086 c41086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29717
  · exact u29718
  · exact u29719
  · exact u29720
  · exact u29721
  · exact u29722
  · exact u29723
  · exact u29724
  · exact u29725
  · exact u29726

def r41087 : Route 9 := (fun mask => (mask,id))

def c41087 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41087 : Upper (D 6) (R 6) [6,136,288,66] 13 := by
  apply FastRouting.sound _ _ [6,136,288,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41087 c41087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29727
  · exact u29728
  · exact u29729
  · exact u29730
  · exact u29731
  · exact u29732

def r41088 : Route 9 := (fun mask => (mask,id))

def c41088 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41088 : Upper (D 6) (R 6) [6,136,288,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41088 c41088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29733
  · exact u29734
  · exact u29735
  · exact u29736
  · exact u29737
  · exact u29738

def r41089 : Route 9 := (fun mask => (mask,id))

def c41089 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41089 : Upper (D 6) (R 6) [6,136,288,80] 13 := by
  apply FastRouting.sound _ _ [6,136,288,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41089 c41089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29739
  · exact u29740
  · exact u29741
  · exact u29742
  · exact u29743
  · exact u29744
  · exact u29745
  · exact u29746
  · exact u29747
  · exact u29748

def r41090 : Route 9 := (fun mask => (mask,id))

def c41090 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41090 : Upper (D 6) (R 6) [6,136,288,96] 13 := by
  apply FastRouting.sound _ _ [6,136,288,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41090 c41090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29749
  · exact u29750
  · exact u29751
  · exact u29752
  · exact u29753
  · exact u29754

def b41091 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 292 11 93 125 93 221 349), lower := (rows 7 162 292 11 16 32 64 128 256), losses := [] }

theorem u41091 : Upper (D 6) (R 6) [6,160,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41091
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41092 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 162 292 14 89 121 89 217 345), lower := (rows 7 162 292 14 16 32 64 128 256), losses := [] }

theorem u41092 : Upper (D 6) (R 6) [6,160,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41092
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41093_3 : Upper (D 6) (R 6) [6,160,288,17,3] 13 :=
  permutation_upper _ _ _ [6,160,288,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29755

theorem m41093_5 : Upper (D 6) (R 6) [6,160,288,17,5] 13 :=
  permutation_upper _ _ _ [6,160,288,3,9] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29755

theorem m41093_6 : Upper (D 6) (R 6) [6,160,288,17,6] 13 :=
  permutation_upper _ _ _ [6,160,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29760

theorem m41093_12 : Upper (D 6) (R 6) [6,160,288,17,12] 13 :=
  permutation_upper _ _ _ [6,160,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29764

theorem m41093_68 : Upper (D 6) (R 6) [6,160,288,17,68] 13 :=
  permutation_upper _ _ _ [6,160,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29766

def r41093 : Route 9 := (fun mask => (mask,id))

def c41093 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41093 : Upper (D 6) (R 6) [6,160,288,17] 13 := by
  apply FastRouting.sound _ _ [6,160,288,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41093 c41093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41093_3
  · exact m41093_5
  · exact m41093_6
  · exact u29763
  · exact u29764
  · exact m41093_12
  · exact u29765
  · exact u29766
  · exact m41093_68
  · exact u29767

theorem m41094_5 : Upper (D 6) (R 6) [6,160,288,18,5] 13 :=
  permutation_upper _ _ _ [6,160,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29756

theorem m41094_9 : Upper (D 6) (R 6) [6,160,288,18,9] 13 :=
  permutation_upper _ _ _ [6,160,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29764

def r41094 : Route 9 := (fun mask => (mask,id))

def c41094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41094 : Upper (D 6) (R 6) [6,160,288,18] 13 := by
  apply FastRouting.sound _ _ [6,160,288,18] 13 (by decide) (choices 2) [5,9,12,65,68,72] r41094 c41094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41094_5
  · exact m41094_9
  · exact u29768
  · exact u29769
  · exact u29770
  · exact u29771

theorem m41095_3 : Upper (D 6) (R 6) [6,160,288,65,3] 13 :=
  permutation_upper _ _ _ [6,160,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29757

theorem m41095_5 : Upper (D 6) (R 6) [6,160,288,65,5] 13 :=
  permutation_upper _ _ _ [6,160,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29757

theorem m41095_6 : Upper (D 6) (R 6) [6,160,288,65,6] 13 :=
  permutation_upper _ _ _ [6,160,288,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29761

theorem m41095_9 : Upper (D 6) (R 6) [6,160,288,65,9] 13 :=
  permutation_upper _ _ _ [6,160,288,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29765

theorem m41095_10 : Upper (D 6) (R 6) [6,160,288,65,10] 13 :=
  permutation_upper _ _ _ [6,160,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29769

theorem m41095_12 : Upper (D 6) (R 6) [6,160,288,65,12] 13 :=
  permutation_upper _ _ _ [6,160,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29769

theorem m41095_68 : Upper (D 6) (R 6) [6,160,288,65,68] 13 :=
  permutation_upper _ _ _ [6,160,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29773

def r41095 : Route 9 := (fun mask => (mask,id))

def c41095 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41095 : Upper (D 6) (R 6) [6,160,288,65] 13 := by
  apply FastRouting.sound _ _ [6,160,288,65] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41095 c41095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41095_3
  · exact m41095_5
  · exact m41095_6
  · exact m41095_9
  · exact m41095_10
  · exact m41095_12
  · exact u29772
  · exact u29773
  · exact m41095_68
  · exact u29774

theorem m41096_5 : Upper (D 6) (R 6) [6,160,288,66,5] 13 :=
  permutation_upper _ _ _ [6,160,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29758

theorem m41096_9 : Upper (D 6) (R 6) [6,160,288,66,9] 13 :=
  permutation_upper _ _ _ [6,160,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29766

theorem m41096_12 : Upper (D 6) (R 6) [6,160,288,66,12] 13 :=
  permutation_upper _ _ _ [6,160,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29770

theorem m41096_65 : Upper (D 6) (R 6) [6,160,288,66,65] 13 :=
  permutation_upper _ _ _ [6,160,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29773

def r41096 : Route 9 := (fun mask => (mask,id))

def c41096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41096 : Upper (D 6) (R 6) [6,160,288,66] 13 := by
  apply FastRouting.sound _ _ [6,160,288,66] 13 (by decide) (choices 2) [5,9,12,65,68,72] r41096 c41096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41096_5
  · exact m41096_9
  · exact m41096_12
  · exact m41096_65
  · exact u29775
  · exact u29776

theorem m41097_3 : Upper (D 6) (R 6) [6,160,288,80,3] 13 :=
  permutation_upper _ _ _ [6,160,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29759

theorem m41097_5 : Upper (D 6) (R 6) [6,160,288,80,5] 13 :=
  permutation_upper _ _ _ [6,160,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29759

theorem m41097_6 : Upper (D 6) (R 6) [6,160,288,80,6] 13 :=
  permutation_upper _ _ _ [6,160,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29762

theorem m41097_9 : Upper (D 6) (R 6) [6,160,288,80,9] 13 :=
  permutation_upper _ _ _ [6,160,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29767

theorem m41097_10 : Upper (D 6) (R 6) [6,160,288,80,10] 13 :=
  permutation_upper _ _ _ [6,160,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29771

theorem m41097_12 : Upper (D 6) (R 6) [6,160,288,80,12] 13 :=
  permutation_upper _ _ _ [6,160,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29771

theorem m41097_65 : Upper (D 6) (R 6) [6,160,288,80,65] 13 :=
  permutation_upper _ _ _ [6,160,288,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29774

theorem m41097_66 : Upper (D 6) (R 6) [6,160,288,80,66] 13 :=
  permutation_upper _ _ _ [6,160,288,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29776

theorem m41097_68 : Upper (D 6) (R 6) [6,160,288,80,68] 13 :=
  permutation_upper _ _ _ [6,160,288,66,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29776

def r41097 : Route 9 := (fun mask => (mask,id))

def c41097 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41097 : Upper (D 6) (R 6) [6,160,288,80] 13 := by
  apply FastRouting.sound _ _ [6,160,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41097 c41097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41097_3
  · exact m41097_5
  · exact m41097_6
  · exact m41097_9
  · exact m41097_10
  · exact m41097_12
  · exact m41097_65
  · exact m41097_66
  · exact m41097_68
  · exact u29777

def b41098 : PairBound 9 := { available := 125, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 125 125 125 253 381), lower := (rows 7 162 324 11 16 32 64 128 256), losses := [] }

theorem u41098 : Upper (D 6) (R 6) [6,160,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41098
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41099 : PairBound 9 := { available := 121, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 162 324 14 121 121 121 249 377), lower := (rows 7 162 324 14 16 32 64 128 256), losses := [] }

theorem u41099 : Upper (D 6) (R 6) [6,160,320,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41099
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41099
end Delivery.IrregularNine14.P06
