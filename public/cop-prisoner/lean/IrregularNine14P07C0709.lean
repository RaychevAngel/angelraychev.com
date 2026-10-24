import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0597
import IrregularNine14P07C0598
import IrregularNine14P07C0599
import IrregularNine14P07C0600
import IrregularNine14P07C0601

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42540_3 : Upper (D 7) (R 7) [34,260,65,160,3] 13 :=
  permutation_upper _ _ _ [34,260,65,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35855

theorem m42540_9 : Upper (D 7) (R 7) [34,260,65,160,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35865

theorem m42540_10 : Upper (D 7) (R 7) [34,260,65,160,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35874

theorem m42540_65 : Upper (D 7) (R 7) [34,260,65,160,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35894

theorem m42540_66 : Upper (D 7) (R 7) [34,260,65,160,66] 13 :=
  permutation_upper _ _ _ [34,260,65,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35897

theorem m42540_72 : Upper (D 7) (R 7) [34,260,65,160,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35901

theorem m42540_129 : Upper (D 7) (R 7) [34,260,65,160,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35907

theorem m42540_130 : Upper (D 7) (R 7) [34,260,65,160,130] 13 :=
  permutation_upper _ _ _ [34,260,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35910

theorem m42540_136 : Upper (D 7) (R 7) [34,260,65,160,136] 13 :=
  permutation_upper _ _ _ [34,260,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35913

def r42540 : Route 9 := (fun mask => (mask,id))

def c42540 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42540 : Upper (D 7) (R 7) [34,260,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42540 c42540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42540_3
  · exact m42540_9
  · exact m42540_10
  · exact m42540_65
  · exact m42540_66
  · exact m42540_72
  · exact m42540_129
  · exact m42540_130
  · exact m42540_136
  · exact u35915

theorem m42541_3 : Upper (D 7) (R 7) [34,260,65,192,3] 13 :=
  permutation_upper _ _ _ [34,260,65,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35856

theorem m42541_9 : Upper (D 7) (R 7) [34,260,65,192,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35866

theorem m42541_10 : Upper (D 7) (R 7) [34,260,65,192,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35875

theorem m42541_33 : Upper (D 7) (R 7) [34,260,65,192,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35880

theorem m42541_34 : Upper (D 7) (R 7) [34,260,65,192,34] 13 :=
  permutation_upper _ _ _ [34,260,65,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35884

theorem m42541_40 : Upper (D 7) (R 7) [34,260,65,192,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35891

theorem m42541_129 : Upper (D 7) (R 7) [34,260,65,192,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35908

theorem m42541_130 : Upper (D 7) (R 7) [34,260,65,192,130] 13 :=
  permutation_upper _ _ _ [34,260,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35911

theorem m42541_136 : Upper (D 7) (R 7) [34,260,65,192,136] 13 :=
  permutation_upper _ _ _ [34,260,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35914

theorem m42541_160 : Upper (D 7) (R 7) [34,260,65,192,160] 13 :=
  permutation_upper _ _ _ [34,260,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35915

def r42541 : Route 9 := (fun mask => (mask,id))

def c42541 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42541 : Upper (D 7) (R 7) [34,260,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42541 c42541
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42541_3
  · exact m42541_9
  · exact m42541_10
  · exact m42541_33
  · exact m42541_34
  · exact m42541_40
  · exact m42541_129
  · exact m42541_130
  · exact m42541_136
  · exact m42541_160

def r42542 : Route 9 := (fun mask => (mask,id))

def c42542 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42542 : Upper (D 7) (R 7) [34,260,66,17] 13 := by
  apply FastRouting.sound _ _ [34,260,66,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42542 c42542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35916
  · exact u35917
  · exact u35918
  · exact u35919
  · exact u35920
  · exact u35921
  · exact u35922
  · exact u35923
  · exact u35924
  · exact u35925

def b42543 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 41 217 249 217 217 473), lower := (rows 35 262 70 41 16 32 64 128 256), losses := [] }

theorem u42543 : Upper (D 7) (R 7) [34,260,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42544_9 : Upper (D 7) (R 7) [34,260,66,48,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35918

def r42544 : Route 9 := (fun mask => (mask,id))

def c42544 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42544 : Upper (D 7) (R 7) [34,260,66,48] 13 := by
  apply FastRouting.sound _ _ [34,260,66,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42544 c42544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42544_9
  · exact u35931
  · exact u35932
  · exact u35933
  · exact u35934
  · exact u35935

theorem m42545_9 : Upper (D 7) (R 7) [34,260,66,65,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35919

theorem m42545_33 : Upper (D 7) (R 7) [34,260,66,65,33] 13 :=
  permutation_upper _ _ _ [34,260,66,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35926

theorem m42545_40 : Upper (D 7) (R 7) [34,260,66,65,40] 13 :=
  permutation_upper _ _ _ [34,260,66,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35931

def r42545 : Route 9 := (fun mask => (mask,id))

def c42545 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42545 : Upper (D 7) (R 7) [34,260,66,65] 13 := by
  apply FastRouting.sound _ _ [34,260,66,65] 13 (by decide) (choices 2) [9,33,40,129,136,160] r42545 c42545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42545_9
  · exact m42545_33
  · exact m42545_40
  · exact u35936
  · exact u35937
  · exact u35938

theorem m42546_9 : Upper (D 7) (R 7) [34,260,66,80,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35920

theorem m42546_33 : Upper (D 7) (R 7) [34,260,66,80,33] 13 :=
  permutation_upper _ _ _ [34,260,66,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35927

theorem m42546_40 : Upper (D 7) (R 7) [34,260,66,80,40] 13 :=
  permutation_upper _ _ _ [34,260,66,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35932

def r42546 : Route 9 := (fun mask => (mask,id))

def c42546 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42546 : Upper (D 7) (R 7) [34,260,66,80] 13 := by
  apply FastRouting.sound _ _ [34,260,66,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r42546 c42546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42546_9
  · exact m42546_33
  · exact m42546_40
  · exact u35939
  · exact u35940
  · exact u35941

theorem m42547_9 : Upper (D 7) (R 7) [34,260,66,96,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35921

def r42547 : Route 9 := (fun mask => (mask,id))

def c42547 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42547 : Upper (D 7) (R 7) [34,260,66,96] 13 := by
  apply FastRouting.sound _ _ [34,260,66,96] 13 (by decide) (choices 2) [9,129,136] r42547 c42547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m42547_9
  · exact u35942
  · exact u35943

theorem m42548_9 : Upper (D 7) (R 7) [34,260,66,129,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35922

theorem m42548_33 : Upper (D 7) (R 7) [34,260,66,129,33] 13 :=
  permutation_upper _ _ _ [34,260,66,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35928

theorem m42548_40 : Upper (D 7) (R 7) [34,260,66,129,40] 13 :=
  permutation_upper _ _ _ [34,260,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35933

theorem m42548_65 : Upper (D 7) (R 7) [34,260,66,129,65] 13 :=
  permutation_upper _ _ _ [34,260,66,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35936

theorem m42548_72 : Upper (D 7) (R 7) [34,260,66,129,72] 13 :=
  permutation_upper _ _ _ [34,260,66,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35939

theorem m42548_96 : Upper (D 7) (R 7) [34,260,66,129,96] 13 :=
  permutation_upper _ _ _ [34,260,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35942

def r42548 : Route 9 := (fun mask => (mask,id))

def c42548 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42548 : Upper (D 7) (R 7) [34,260,66,129] 13 := by
  apply FastRouting.sound _ _ [34,260,66,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42548 c42548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42548_9
  · exact m42548_33
  · exact m42548_40
  · exact m42548_65
  · exact m42548_72
  · exact m42548_96
  · exact u35944
  · exact u35945
  · exact u35946
  · exact u35947

theorem m42549_9 : Upper (D 7) (R 7) [34,260,66,144,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35923

theorem m42549_33 : Upper (D 7) (R 7) [34,260,66,144,33] 13 :=
  permutation_upper _ _ _ [34,260,66,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35929

theorem m42549_40 : Upper (D 7) (R 7) [34,260,66,144,40] 13 :=
  permutation_upper _ _ _ [34,260,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35934

theorem m42549_65 : Upper (D 7) (R 7) [34,260,66,144,65] 13 :=
  permutation_upper _ _ _ [34,260,66,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35937

theorem m42549_72 : Upper (D 7) (R 7) [34,260,66,144,72] 13 :=
  permutation_upper _ _ _ [34,260,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35940

theorem m42549_96 : Upper (D 7) (R 7) [34,260,66,144,96] 13 :=
  permutation_upper _ _ _ [34,260,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35943

theorem m42549_129 : Upper (D 7) (R 7) [34,260,66,144,129] 13 :=
  permutation_upper _ _ _ [34,260,66,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35945

def r42549 : Route 9 := (fun mask => (mask,id))

def c42549 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42549 : Upper (D 7) (R 7) [34,260,66,144] 13 := by
  apply FastRouting.sound _ _ [34,260,66,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42549 c42549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42549_9
  · exact m42549_33
  · exact m42549_40
  · exact m42549_65
  · exact m42549_72
  · exact m42549_96
  · exact m42549_129
  · exact u35948
  · exact u35949
  · exact u35950

theorem m42550_9 : Upper (D 7) (R 7) [34,260,66,160,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35924

theorem m42550_65 : Upper (D 7) (R 7) [34,260,66,160,65] 13 :=
  permutation_upper _ _ _ [34,260,66,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35938

theorem m42550_72 : Upper (D 7) (R 7) [34,260,66,160,72] 13 :=
  permutation_upper _ _ _ [34,260,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35941

theorem m42550_129 : Upper (D 7) (R 7) [34,260,66,160,129] 13 :=
  permutation_upper _ _ _ [34,260,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35946

theorem m42550_136 : Upper (D 7) (R 7) [34,260,66,160,136] 13 :=
  permutation_upper _ _ _ [34,260,66,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35949

def r42550 : Route 9 := (fun mask => (mask,id))

def c42550 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42550 : Upper (D 7) (R 7) [34,260,66,160] 13 := by
  apply FastRouting.sound _ _ [34,260,66,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42550 c42550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42550_9
  · exact m42550_65
  · exact m42550_72
  · exact m42550_129
  · exact m42550_136
  · exact u35951

theorem m42551_9 : Upper (D 7) (R 7) [34,260,66,192,9] 13 :=
  permutation_upper _ _ _ [34,260,66,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35925

theorem m42551_33 : Upper (D 7) (R 7) [34,260,66,192,33] 13 :=
  permutation_upper _ _ _ [34,260,66,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35930

theorem m42551_40 : Upper (D 7) (R 7) [34,260,66,192,40] 13 :=
  permutation_upper _ _ _ [34,260,66,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35935

theorem m42551_129 : Upper (D 7) (R 7) [34,260,66,192,129] 13 :=
  permutation_upper _ _ _ [34,260,66,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35947

theorem m42551_136 : Upper (D 7) (R 7) [34,260,66,192,136] 13 :=
  permutation_upper _ _ _ [34,260,66,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35950

theorem m42551_160 : Upper (D 7) (R 7) [34,260,66,192,160] 13 :=
  permutation_upper _ _ _ [34,260,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35951

def r42551 : Route 9 := (fun mask => (mask,id))

def c42551 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42551 : Upper (D 7) (R 7) [34,260,66,192] 13 := by
  apply FastRouting.sound _ _ [34,260,66,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r42551 c42551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42551_9
  · exact m42551_33
  · exact m42551_40
  · exact m42551_129
  · exact m42551_136
  · exact m42551_160

def b42552 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 76 11 241 241 241 241 497), lower := (rows 35 262 76 11 16 32 64 128 256), losses := [] }

theorem u42552 : Upper (D 7) (R 7) [34,260,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42553 : Route 9 := (fun mask => (mask,id))

def c42553 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42553 : Upper (D 7) (R 7) [34,260,72,17] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42553 c42553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35952
  · exact u35953
  · exact u35954
  · exact u35955
  · exact u35956
  · exact u35957
  · exact u35958
  · exact u35959
  · exact u35960
  · exact u35961

def r42554 : Route 9 := (fun mask => (mask,id))

def c42554 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42554 : Upper (D 7) (R 7) [34,260,72,18] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42554 c42554
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35962
  · exact u35963
  · exact u35964
  · exact u35965
  · exact u35966
  · exact u35967

def b42555 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 76 41 211 243 211 211 467), lower := (rows 35 262 76 41 16 32 64 128 256), losses := [] }

theorem u42555 : Upper (D 7) (R 7) [34,260,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42556 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 76 42 209 241 209 209 465), lower := (rows 35 262 76 42 16 32 64 128 256), losses := [] }

theorem u42556 : Upper (D 7) (R 7) [34,260,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42557 : Route 9 := (fun mask => (mask,id))

def c42557 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42557 : Upper (D 7) (R 7) [34,260,72,48] 13 := by
  apply FastRouting.sound _ _ [34,260,72,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42557 c42557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35968
  · exact u35969
  · exact u35970
  · exact u35971
  · exact u35972
  · exact u35973

def b42558 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 76 73 179 179 243 179 435), lower := (rows 35 262 76 73 16 32 64 128 256), losses := [] }

theorem u42558 : Upper (D 7) (R 7) [34,260,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42559 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 76 74 177 177 241 177 433), lower := (rows 35 262 76 74 16 32 64 128 256), losses := [] }

theorem u42559 : Upper (D 7) (R 7) [34,260,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42560 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 76 88 179 163 227 163 419), lower := (rows 35 262 76 88 16 32 64 128 256), losses := [] }

theorem u42560 : Upper (D 7) (R 7) [34,260,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42561 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 76 104 147 179 211 147 403), lower := (rows 35 262 76 104 16 32 64 128 256), losses := [] }

theorem u42561 : Upper (D 7) (R 7) [34,260,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42562 : Route 9 := (fun mask => (mask,id))

def c42562 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42562 : Upper (D 7) (R 7) [34,260,72,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42562 c42562
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35974
  · exact u35975
  · exact u35976
  · exact u35977
  · exact u35978
  · exact u35979
  · exact u35980
  · exact u35981
  · exact u35982
  · exact u35983

def r42563 : Route 9 := (fun mask => (mask,id))

def c42563 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42563 : Upper (D 7) (R 7) [34,260,72,130] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42563 c42563
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35984
  · exact u35985
  · exact u35986
  · exact u35987
  · exact u35988
  · exact u35989

def r42564 : Route 9 := (fun mask => (mask,id))

def c42564 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42564 : Upper (D 7) (R 7) [34,260,72,144] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42564 c42564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35990
  · exact u35991
  · exact u35992
  · exact u35993
  · exact u35994
  · exact u35995
  · exact u35996
  · exact u35997
  · exact u35998
  · exact u35999

def r42565 : Route 9 := (fun mask => (mask,id))

def c42565 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42565 : Upper (D 7) (R 7) [34,260,72,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42565 c42565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36000
  · exact u36001
  · exact u36002
  · exact u36003
  · exact u36004
  · exact u36005

def b42566 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 76 200 179 179 243 179 435), lower := (rows 35 262 76 200 16 32 64 128 256), losses := [] }

theorem u42566 : Upper (D 7) (R 7) [34,260,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42567 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 100 11 217 249 217 217 473), lower := (rows 35 262 100 11 16 32 64 128 256), losses := [] }

theorem u42567 : Upper (D 7) (R 7) [34,260,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42568_3 : Upper (D 7) (R 7) [34,260,96,17,3] 13 :=
  permutation_upper _ _ _ [34,260,96,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36006

def r42568 : Route 9 := (fun mask => (mask,id))

def c42568 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42568 : Upper (D 7) (R 7) [34,260,96,17] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42568 c42568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42568_3
  · exact u36012
  · exact u36013
  · exact u36014
  · exact u36015
  · exact u36016
  · exact u36017
  · exact u36018
  · exact u36019
  · exact u36020

theorem m42569_9 : Upper (D 7) (R 7) [34,260,96,18,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36013

def r42569 : Route 9 := (fun mask => (mask,id))

def c42569 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42569 : Upper (D 7) (R 7) [34,260,96,18] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42569 c42569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42569_9
  · exact u36021
  · exact u36022
  · exact u36023
  · exact u36024
  · exact u36025

theorem m42570_3 : Upper (D 7) (R 7) [34,260,96,65,3] 13 :=
  permutation_upper _ _ _ [34,260,96,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36007

theorem m42570_9 : Upper (D 7) (R 7) [34,260,96,65,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36014

theorem m42570_10 : Upper (D 7) (R 7) [34,260,96,65,10] 13 :=
  permutation_upper _ _ _ [34,260,96,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36021

def r42570 : Route 9 := (fun mask => (mask,id))

def c42570 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42570 : Upper (D 7) (R 7) [34,260,96,65] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42570 c42570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42570_3
  · exact m42570_9
  · exact m42570_10
  · exact u36026
  · exact u36027
  · exact u36028

def b42571 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 262 100 74 153 185 217 153 409), lower := (rows 35 262 100 74 16 32 64 128 256), losses := [] }

theorem u42571 : Upper (D 7) (R 7) [34,260,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42572_3 : Upper (D 7) (R 7) [34,260,96,80,3] 13 :=
  permutation_upper _ _ _ [34,260,96,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36008

theorem m42572_9 : Upper (D 7) (R 7) [34,260,96,80,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36016

theorem m42572_10 : Upper (D 7) (R 7) [34,260,96,80,10] 13 :=
  permutation_upper _ _ _ [34,260,96,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36022

def r42572 : Route 9 := (fun mask => (mask,id))

def c42572 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42572 : Upper (D 7) (R 7) [34,260,96,80] 13 := by
  apply FastRouting.sound _ _ [34,260,96,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42572 c42572
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42572_3
  · exact m42572_9
  · exact m42572_10
  · exact u36031
  · exact u36032
  · exact u36033

theorem m42573_3 : Upper (D 7) (R 7) [34,260,96,129,3] 13 :=
  permutation_upper _ _ _ [34,260,96,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36009

theorem m42573_9 : Upper (D 7) (R 7) [34,260,96,129,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36017

theorem m42573_10 : Upper (D 7) (R 7) [34,260,96,129,10] 13 :=
  permutation_upper _ _ _ [34,260,96,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36023

theorem m42573_65 : Upper (D 7) (R 7) [34,260,96,129,65] 13 :=
  permutation_upper _ _ _ [34,260,96,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36026

theorem m42573_66 : Upper (D 7) (R 7) [34,260,96,129,66] 13 :=
  permutation_upper _ _ _ [34,260,96,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36029

theorem m42573_72 : Upper (D 7) (R 7) [34,260,96,129,72] 13 :=
  permutation_upper _ _ _ [34,260,96,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36031

def r42573 : Route 9 := (fun mask => (mask,id))

def c42573 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42573 : Upper (D 7) (R 7) [34,260,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42573 c42573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42573_3
  · exact m42573_9
  · exact m42573_10
  · exact m42573_65
  · exact m42573_66
  · exact m42573_72
  · exact u36034
  · exact u36035
  · exact u36036
  · exact u36037

theorem m42574_9 : Upper (D 7) (R 7) [34,260,96,130,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36018

theorem m42574_65 : Upper (D 7) (R 7) [34,260,96,130,65] 13 :=
  permutation_upper _ _ _ [34,260,96,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36027

theorem m42574_72 : Upper (D 7) (R 7) [34,260,96,130,72] 13 :=
  permutation_upper _ _ _ [34,260,96,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36032

theorem m42574_129 : Upper (D 7) (R 7) [34,260,96,130,129] 13 :=
  permutation_upper _ _ _ [34,260,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36035

def r42574 : Route 9 := (fun mask => (mask,id))

def c42574 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42574 : Upper (D 7) (R 7) [34,260,96,130] 13 := by
  apply FastRouting.sound _ _ [34,260,96,130] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42574 c42574
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42574_9
  · exact m42574_65
  · exact m42574_72
  · exact m42574_129
  · exact u36038
  · exact u36039

theorem m42575_3 : Upper (D 7) (R 7) [34,260,96,144,3] 13 :=
  permutation_upper _ _ _ [34,260,96,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36010

theorem m42575_9 : Upper (D 7) (R 7) [34,260,96,144,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36019

theorem m42575_10 : Upper (D 7) (R 7) [34,260,96,144,10] 13 :=
  permutation_upper _ _ _ [34,260,96,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36024

theorem m42575_65 : Upper (D 7) (R 7) [34,260,96,144,65] 13 :=
  permutation_upper _ _ _ [34,260,96,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36028

theorem m42575_66 : Upper (D 7) (R 7) [34,260,96,144,66] 13 :=
  permutation_upper _ _ _ [34,260,96,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36030

theorem m42575_72 : Upper (D 7) (R 7) [34,260,96,144,72] 13 :=
  permutation_upper _ _ _ [34,260,96,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36033

theorem m42575_129 : Upper (D 7) (R 7) [34,260,96,144,129] 13 :=
  permutation_upper _ _ _ [34,260,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36036

theorem m42575_130 : Upper (D 7) (R 7) [34,260,96,144,130] 13 :=
  permutation_upper _ _ _ [34,260,96,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36038

def r42575 : Route 9 := (fun mask => (mask,id))

def c42575 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42575 : Upper (D 7) (R 7) [34,260,96,144] 13 := by
  apply FastRouting.sound _ _ [34,260,96,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42575 c42575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42575_3
  · exact m42575_9
  · exact m42575_10
  · exact m42575_65
  · exact m42575_66
  · exact m42575_72
  · exact m42575_129
  · exact m42575_130
  · exact u36040
  · exact u36041

theorem m42576_3 : Upper (D 7) (R 7) [34,260,96,192,3] 13 :=
  permutation_upper _ _ _ [34,260,96,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36011

theorem m42576_9 : Upper (D 7) (R 7) [34,260,96,192,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36020

theorem m42576_10 : Upper (D 7) (R 7) [34,260,96,192,10] 13 :=
  permutation_upper _ _ _ [34,260,96,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36025

theorem m42576_129 : Upper (D 7) (R 7) [34,260,96,192,129] 13 :=
  permutation_upper _ _ _ [34,260,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36037

theorem m42576_130 : Upper (D 7) (R 7) [34,260,96,192,130] 13 :=
  permutation_upper _ _ _ [34,260,96,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36039

theorem m42576_136 : Upper (D 7) (R 7) [34,260,96,192,136] 13 :=
  permutation_upper _ _ _ [34,260,96,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36041

def r42576 : Route 9 := (fun mask => (mask,id))

def c42576 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42576 : Upper (D 7) (R 7) [34,260,96,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,192] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42576 c42576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42576_3
  · exact m42576_9
  · exact m42576_10
  · exact m42576_129
  · exact m42576_130
  · exact m42576_136

def b42577 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 196 11 249 249 249 249 505), lower := (rows 35 262 196 11 16 32 64 128 256), losses := [] }

theorem u42577 : Upper (D 7) (R 7) [34,260,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42578_3 : Upper (D 7) (R 7) [34,260,192,17,3] 13 :=
  permutation_upper _ _ _ [34,260,192,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36042

def r42578 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42578 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42578 : Upper (D 7) (R 7) [34,260,192,17] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r42578 c42578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42578_3
  · exact u36047
  · exact u36048
  · exact u36049
  · exact u36050
  · exact u36051
  · exact u36052
  · exact u36053
  · exact u36054
  · exact u36055
  · exact u36056

theorem m42579_9 : Upper (D 7) (R 7) [34,260,192,18,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36048

def r42579 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42579 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42579 : Upper (D 7) (R 7) [34,260,192,18] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r42579 c42579
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42579_9
  · exact u36057
  · exact u36058
  · exact u36059
  · exact u36060
  · exact u36061
  · exact u36062

def b42580 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 196 41 219 251 219 219 475), lower := (rows 35 262 196 41 16 32 64 128 256), losses := [] }

theorem u42580 : Upper (D 7) (R 7) [34,260,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42581 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 196 42 217 249 217 217 473), lower := (rows 35 262 196 42 16 32 64 128 256), losses := [] }

theorem u42581 : Upper (D 7) (R 7) [34,260,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42582_3 : Upper (D 7) (R 7) [34,260,192,48,3] 13 :=
  permutation_upper _ _ _ [34,260,192,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36043

theorem m42582_9 : Upper (D 7) (R 7) [34,260,192,48,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36051

theorem m42582_10 : Upper (D 7) (R 7) [34,260,192,48,10] 13 :=
  permutation_upper _ _ _ [34,260,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36058

def r42582 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42582 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42582 : Upper (D 7) (R 7) [34,260,192,48] 13 := by
  apply FastRouting.sound _ _ [34,260,192,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r42582 c42582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42582_3
  · exact m42582_9
  · exact m42582_10
  · exact u36068
  · exact u36069
  · exact u36070
  · exact u36071

theorem m42583_3 : Upper (D 7) (R 7) [34,260,192,65,3] 13 :=
  permutation_upper _ _ _ [34,260,192,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36044

theorem m42583_9 : Upper (D 7) (R 7) [34,260,192,65,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36052

theorem m42583_10 : Upper (D 7) (R 7) [34,260,192,65,10] 13 :=
  permutation_upper _ _ _ [34,260,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36059

theorem m42583_33 : Upper (D 7) (R 7) [34,260,192,65,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36063

theorem m42583_34 : Upper (D 7) (R 7) [34,260,192,65,34] 13 :=
  permutation_upper _ _ _ [34,260,192,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36066

theorem m42583_40 : Upper (D 7) (R 7) [34,260,192,65,40] 13 :=
  permutation_upper _ _ _ [34,260,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36068

def r42583 : Route 9 := (fun mask => (mask,id))

def c42583 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42583 : Upper (D 7) (R 7) [34,260,192,65] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42583 c42583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42583_3
  · exact m42583_9
  · exact m42583_10
  · exact m42583_33
  · exact m42583_34
  · exact m42583_40
  · exact u36072
  · exact u36073
  · exact u36074
  · exact u36075

theorem m42584_9 : Upper (D 7) (R 7) [34,260,192,66,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36053

theorem m42584_33 : Upper (D 7) (R 7) [34,260,192,66,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36064

theorem m42584_40 : Upper (D 7) (R 7) [34,260,192,66,40] 13 :=
  permutation_upper _ _ _ [34,260,192,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36069

theorem m42584_129 : Upper (D 7) (R 7) [34,260,192,66,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36073

def r42584 : Route 9 := (fun mask => (mask,id))

def c42584 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42584 : Upper (D 7) (R 7) [34,260,192,66] 13 := by
  apply FastRouting.sound _ _ [34,260,192,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r42584 c42584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42584_9
  · exact m42584_33
  · exact m42584_40
  · exact m42584_129
  · exact u36076
  · exact u36077

theorem m42585_3 : Upper (D 7) (R 7) [34,260,192,80,3] 13 :=
  permutation_upper _ _ _ [34,260,192,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36045

theorem m42585_9 : Upper (D 7) (R 7) [34,260,192,80,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36054

theorem m42585_10 : Upper (D 7) (R 7) [34,260,192,80,10] 13 :=
  permutation_upper _ _ _ [34,260,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36060

theorem m42585_33 : Upper (D 7) (R 7) [34,260,192,80,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36065

theorem m42585_34 : Upper (D 7) (R 7) [34,260,192,80,34] 13 :=
  permutation_upper _ _ _ [34,260,192,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36067

theorem m42585_40 : Upper (D 7) (R 7) [34,260,192,80,40] 13 :=
  permutation_upper _ _ _ [34,260,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36070

theorem m42585_129 : Upper (D 7) (R 7) [34,260,192,80,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36074

theorem m42585_130 : Upper (D 7) (R 7) [34,260,192,80,130] 13 :=
  permutation_upper _ _ _ [34,260,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36076

def r42585 : Route 9 := (fun mask => (mask,id))

def c42585 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42585 : Upper (D 7) (R 7) [34,260,192,80] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42585 c42585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42585_3
  · exact m42585_9
  · exact m42585_10
  · exact m42585_33
  · exact m42585_34
  · exact m42585_40
  · exact m42585_129
  · exact m42585_130
  · exact u36078
  · exact u36079

theorem m42586_3 : Upper (D 7) (R 7) [34,260,192,96,3] 13 :=
  permutation_upper _ _ _ [34,260,192,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36046

theorem m42586_9 : Upper (D 7) (R 7) [34,260,192,96,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36055

theorem m42586_10 : Upper (D 7) (R 7) [34,260,192,96,10] 13 :=
  permutation_upper _ _ _ [34,260,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36061

theorem m42586_129 : Upper (D 7) (R 7) [34,260,192,96,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36075

theorem m42586_130 : Upper (D 7) (R 7) [34,260,192,96,130] 13 :=
  permutation_upper _ _ _ [34,260,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36077

theorem m42586_136 : Upper (D 7) (R 7) [34,260,192,96,136] 13 :=
  permutation_upper _ _ _ [34,260,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36079

def r42586 : Route 9 := (fun mask => (mask,id))

def c42586 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42586 : Upper (D 7) (R 7) [34,260,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,192,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42586 c42586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42586_3
  · exact m42586_9
  · exact m42586_10
  · exact m42586_129
  · exact m42586_130
  · exact m42586_136

def b42587 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 35 262 196 200 59 59 123 187 315), lower := (rows 35 262 196 200 16 32 64 128 256), losses := [] }

theorem u42587 : Upper (D 7) (R 7) [34,260,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42588 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 13 248 248 248 248 504), lower := (rows 35 322 7 13 16 32 64 128 256), losses := [] }

theorem u42588 : Upper (D 7) (R 7) [34,320,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42589 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 249 233 233 233 489), lower := (rows 35 322 7 28 16 32 64 128 256), losses := [] }

theorem u42589 : Upper (D 7) (R 7) [34,320,3,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42590 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 44 217 249 217 217 473), lower := (rows 35 322 7 44 16 32 64 128 256), losses := [] }

theorem u42590 : Upper (D 7) (R 7) [34,320,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42591 : PairBound 9 := { available := 188, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 73 188 188 252 188 444), lower := (rows 35 322 7 73 16 32 64 128 256), losses := [] }

theorem u42591 : Upper (D 7) (R 7) [34,320,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42592 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 76 185 185 249 185 441), lower := (rows 35 322 7 76 16 32 64 128 256), losses := [] }

theorem u42592 : Upper (D 7) (R 7) [34,320,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42593 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 104 157 189 221 157 413), lower := (rows 35 322 7 104 16 32 64 128 256), losses := [] }

theorem u42593 : Upper (D 7) (R 7) [34,320,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42594 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 137 252 252 252 252 508), lower := (rows 35 322 7 137 16 32 64 128 256), losses := [] }

theorem u42594 : Upper (D 7) (R 7) [34,320,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42595 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 140 249 249 249 249 505), lower := (rows 35 322 7 140 16 32 64 128 256), losses := [] }

theorem u42595 : Upper (D 7) (R 7) [34,320,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42596 : PairBound 9 := { available := 221, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 168 221 253 221 221 477), lower := (rows 35 322 7 168 16 32 64 128 256), losses := [] }

theorem u42596 : Upper (D 7) (R 7) [34,320,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42597 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 200 189 189 253 189 445), lower := (rows 35 322 7 200 16 32 64 128 256), losses := [] }

theorem u42597 : Upper (D 7) (R 7) [34,320,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42598 : PairBound 9 := { available := 242, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 13 242 242 242 242 498), lower := (rows 35 322 13 13 16 32 64 128 256), losses := [] }

theorem u42598 : Upper (D 7) (R 7) [34,320,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42599 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 14 241 241 241 241 497), lower := (rows 35 322 13 14 16 32 64 128 256), losses := [] }

theorem u42599 : Upper (D 7) (R 7) [34,320,9,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u42599
end Delivery.IrregularNine14.P07
