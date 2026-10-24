import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0115
import IrregularNine14P09C0116
import IrregularNine14P09C0117
import IrregularNine14P09C0118
import IrregularNine14P09C0119

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m8880_9 : Upper (D 9) (R 9) [6,96,160,80,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6947

theorem m8880_129 : Upper (D 9) (R 9) [6,96,160,80,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6953

def r8880 : Route 9 := (fun mask => (mask,id))

def c8880 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8880 : Upper (D 9) (R 9) [6,96,160,80] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80] 13 (by decide) (choices 2) [9,129,136,257,264,384] r8880 c8880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8880_9
  · exact m8880_129
  · exact u6957
  · exact u6958
  · exact u6959
  · exact u6960

theorem m8881_9 : Upper (D 9) (R 9) [6,96,160,192,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6948

def r8881 : Route 9 := (fun mask => (mask,id))

def c8881 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8881 : Upper (D 9) (R 9) [6,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192] 13 (by decide) (choices 2) [9,257,264] r8881 c8881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m8881_9
  · exact u6961
  · exact u6962

theorem m8882_9 : Upper (D 9) (R 9) [6,96,160,257,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6949

theorem m8882_65 : Upper (D 9) (R 9) [6,96,160,257,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6954

theorem m8882_72 : Upper (D 9) (R 9) [6,96,160,257,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6958

theorem m8882_129 : Upper (D 9) (R 9) [6,96,160,257,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6954

theorem m8882_136 : Upper (D 9) (R 9) [6,96,160,257,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6958

theorem m8882_192 : Upper (D 9) (R 9) [6,96,160,257,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6961

theorem m8882_384 : Upper (D 9) (R 9) [6,96,160,257,384] 13 :=
  permutation_upper _ _ _ [6,96,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6965

def r8882 : Route 9 := (fun mask => (mask,id))

def c8882 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8882 : Upper (D 9) (R 9) [6,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r8882 c8882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8882_9
  · exact m8882_65
  · exact m8882_72
  · exact m8882_129
  · exact m8882_136
  · exact m8882_192
  · exact u6963
  · exact u6964
  · exact u6965
  · exact m8882_384

theorem m8883_9 : Upper (D 9) (R 9) [6,96,160,272,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6950

theorem m8883_65 : Upper (D 9) (R 9) [6,96,160,272,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6955

theorem m8883_72 : Upper (D 9) (R 9) [6,96,160,272,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6959

theorem m8883_129 : Upper (D 9) (R 9) [6,96,160,272,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6955

theorem m8883_136 : Upper (D 9) (R 9) [6,96,160,272,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6959

theorem m8883_192 : Upper (D 9) (R 9) [6,96,160,272,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6962

theorem m8883_257 : Upper (D 9) (R 9) [6,96,160,272,257] 13 :=
  permutation_upper _ _ _ [6,96,160,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6964

theorem m8883_384 : Upper (D 9) (R 9) [6,96,160,272,384] 13 :=
  permutation_upper _ _ _ [6,96,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6967

def r8883 : Route 9 := (fun mask => (mask,id))

def c8883 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8883 : Upper (D 9) (R 9) [6,96,160,272] 13 := by
  apply FastRouting.sound _ _ [6,96,160,272] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r8883 c8883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8883_9
  · exact m8883_65
  · exact m8883_72
  · exact m8883_129
  · exact m8883_136
  · exact m8883_192
  · exact m8883_257
  · exact u6966
  · exact u6967
  · exact m8883_384

theorem m8884_9 : Upper (D 9) (R 9) [6,96,160,320,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6951

theorem m8884_129 : Upper (D 9) (R 9) [6,96,160,320,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6956

theorem m8884_136 : Upper (D 9) (R 9) [6,96,160,320,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6960

theorem m8884_257 : Upper (D 9) (R 9) [6,96,160,320,257] 13 :=
  permutation_upper _ _ _ [6,96,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6965

theorem m8884_264 : Upper (D 9) (R 9) [6,96,160,320,264] 13 :=
  permutation_upper _ _ _ [6,96,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6967

def r8884 : Route 9 := (fun mask => (mask,id))

def c8884 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8884 : Upper (D 9) (R 9) [6,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320] 13 (by decide) (choices 2) [9,129,136,257,264,384] r8884 c8884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8884_9
  · exact m8884_129
  · exact m8884_136
  · exact m8884_257
  · exact m8884_264
  · exact u6968

theorem m8885_129 : Upper (D 9) (R 9) [6,96,384,17,129] 13 :=
  permutation_upper _ _ _ [6,96,384,17,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6970

theorem m8885_136 : Upper (D 9) (R 9) [6,96,384,17,136] 13 :=
  permutation_upper _ _ _ [6,96,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6971

theorem m8885_384 : Upper (D 9) (R 9) [6,96,384,17,384] 13 :=
  permutation_upper _ _ _ [6,96,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6972

def r8885 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8885 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8885 : Upper (D 9) (R 9) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,384] r8885 c8885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6969
  · exact u6970
  · exact u6971
  · exact u6972
  · exact m8885_129
  · exact m8885_136
  · exact u6973
  · exact m8885_384

theorem m8886_9 : Upper (D 9) (R 9) [6,96,384,33,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6970

def r8886 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8886 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8886 : Upper (D 9) (R 9) [6,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33] 13 (by decide) (choices 2) [9,65,72,129,136,192,384] r8886 c8886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8886_9
  · exact u6974
  · exact u6975
  · exact u6976
  · exact u6977
  · exact u6978
  · exact u6979

theorem m8887_9 : Upper (D 9) (R 9) [6,96,384,48,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6971

theorem m8887_65 : Upper (D 9) (R 9) [6,96,384,48,65] 13 :=
  permutation_upper _ _ _ [6,96,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6975

theorem m8887_129 : Upper (D 9) (R 9) [6,96,384,48,129] 13 :=
  permutation_upper _ _ _ [6,96,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6977

def r8887 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8887 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8887 : Upper (D 9) (R 9) [6,96,384,48] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,384] r8887 c8887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8887_9
  · exact m8887_65
  · exact u6980
  · exact m8887_129
  · exact u6981
  · exact u6982
  · exact u6983

def b8888 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 8, targets := 385 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7),(3,8)], upper := (rows 7 98 388 104 409 441 473 409 409), lower := (rows 7 98 388 104 16 32 64 128 256), losses := [] }

theorem u8888 : Upper (D 9) (R 9) [6,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8888 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8889_9 : Upper (D 9) (R 9) [6,96,384,160,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6973

theorem m8889_65 : Upper (D 9) (R 9) [6,96,384,160,65] 13 :=
  permutation_upper _ _ _ [6,96,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6978

theorem m8889_72 : Upper (D 9) (R 9) [6,96,384,160,72] 13 :=
  permutation_upper _ _ _ [6,96,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6982

theorem m8889_257 : Upper (D 9) (R 9) [6,96,384,160,257] 13 :=
  permutation_upper _ _ _ [6,96,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6978

theorem m8889_264 : Upper (D 9) (R 9) [6,96,384,160,264] 13 :=
  permutation_upper _ _ _ [6,96,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6982

def r8889 : Route 9 := (fun mask => (mask,id))

def c8889 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u8889 : Upper (D 9) (R 9) [6,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r8889 c8889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8889_9
  · exact m8889_65
  · exact m8889_72
  · exact m8889_257
  · exact m8889_264
  · exact u6984

def b8890 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 28 41 464 480 448 448 448), lower := (rows 35 7 28 41 16 32 64 128 256), losses := [] }

theorem u8890 : Upper (D 9) (R 9) [34,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8890 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8891 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8891 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8891 : Upper (D 9) (R 9) [34,5,24,65] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65] 13 (by decide) (choices 2) [96,160,192,384] r8891 c8891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6986
  · exact u6987
  · exact u6988
  · exact u6989

theorem m8892_65 : Upper (D 9) (R 9) [34,5,24,96,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6986

theorem m8892_129 : Upper (D 9) (R 9) [34,5,24,96,129] 13 :=
  permutation_upper _ _ _ [34,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6987

def r8892 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8892 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8892 : Upper (D 9) (R 9) [34,5,24,96] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96] 13 (by decide) (choices 2) [65,129,192,384] r8892 c8892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m8892_65
  · exact m8892_129
  · exact u6990
  · exact u6991

theorem m8893_33 : Upper (D 9) (R 9) [34,5,24,192,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6985

theorem m8893_65 : Upper (D 9) (R 9) [34,5,24,192,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6988

theorem m8893_96 : Upper (D 9) (R 9) [34,5,24,192,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6990

theorem m8893_257 : Upper (D 9) (R 9) [34,5,24,192,257] 13 :=
  permutation_upper _ _ _ [34,5,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6989

theorem m8893_288 : Upper (D 9) (R 9) [34,5,24,192,288] 13 :=
  permutation_upper _ _ _ [34,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6991

def r8893 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8893 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8893 : Upper (D 9) (R 9) [34,5,24,192] 13 := by
  apply FastRouting.sound _ _ [34,5,24,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8893 c8893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8893_33
  · exact m8893_65
  · exact m8893_96
  · exact u6992
  · exact m8893_257
  · exact m8893_288
  · exact u6993

def r8894 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8894 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8894 : Upper (D 9) (R 9) [34,5,72,17] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17] 13 (by decide) (choices 2) [96,160,192,384] r8894 c8894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6994
  · exact u6995
  · exact u6996
  · exact u6997

def b8895 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 76 41 464 496 464 464 464), lower := (rows 35 7 76 41 16 32 64 128 256), losses := [] }

theorem u8895 : Upper (D 9) (R 9) [34,5,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8895 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8896 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8896 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8896 : Upper (D 9) (R 9) [34,5,72,48] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48] 13 (by decide) (choices 2) [65,129,192,384] r8896 c8896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6998
  · exact u6999
  · exact u7000
  · exact u7001

def b8897 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(2,5),(2,7)], upper := (rows 35 7 76 73 432 432 496 432 432), lower := (rows 35 7 76 73 16 32 64 128 256), losses := [] }

theorem u8897 : Upper (D 9) (R 9) [34,5,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8897 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8898 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 417 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 7 76 88 433 417 481 417 417), lower := (rows 35 7 76 88 16 32 64 128 256), losses := [] }

theorem u8898 : Upper (D 9) (R 9) [34,5,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8898 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8899 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 76 104 401 433 465 401 401), lower := (rows 35 7 76 104 16 32 64 128 256), losses := [] }

theorem u8899 : Upper (D 9) (R 9) [34,5,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8899 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8900 : Route 9 := (fun mask => (mask,id))

def c8900 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8900 : Upper (D 9) (R 9) [34,5,72,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r8900 c8900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7002
  · exact u7003
  · exact u7004
  · exact u7005
  · exact u7006
  · exact u7007

def r8901 : Route 9 := (fun mask => (mask,id))

def c8901 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8901 : Upper (D 9) (R 9) [34,5,72,144] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r8901 c8901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7008
  · exact u7009
  · exact u7010
  · exact u7011
  · exact u7012
  · exact u7013
  · exact u7014
  · exact u7015
  · exact u7016
  · exact u7017

def r8902 : Route 9 := (fun mask => (mask,id))

def c8902 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8902 : Upper (D 9) (R 9) [34,5,72,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8902 c8902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7018
  · exact u7019
  · exact u7020
  · exact u7021
  · exact u7022
  · exact u7023

def b8903 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 4, targets := 417 },{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 7 76 200 433 433 497 433 433), lower := (rows 35 7 76 200 16 32 64 128 256), losses := [] }

theorem u8903 : Upper (D 9) (R 9) [34,5,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8903 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8904 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8904 : Upper (D 9) (R 9) [34,5,72,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r8904 c8904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7024
  · exact u7025
  · exact u7026
  · exact u7027
  · exact u7028
  · exact u7029
  · exact u7030

def r8905 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8905 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8905 : Upper (D 9) (R 9) [34,5,192,17] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r8905 c8905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7031
  · exact u7032
  · exact u7033
  · exact u7034
  · exact u7035
  · exact u7036
  · exact u7037

def b8906 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 196 41 472 504 472 472 472), lower := (rows 35 7 196 41 16 32 64 128 256), losses := [] }

theorem u8906 : Upper (D 9) (R 9) [34,5,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8906 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8907_9 : Upper (D 9) (R 9) [34,5,192,48,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7031

def r8907 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8907 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8907 : Upper (D 9) (R 9) [34,5,192,48] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48] 13 (by decide) (choices 2) [9,65,72,192,257,264,320] r8907 c8907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8907_9
  · exact u7041
  · exact u7042
  · exact u7043
  · exact u7044
  · exact u7045
  · exact u7046

theorem m8908_40 : Upper (D 9) (R 9) [34,5,192,65,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7041

def r8908 : Route 9 := (fun mask => (mask,id))

def c8908 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8908 : Upper (D 9) (R 9) [34,5,192,65] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65] 13 (by decide) (choices 2) [40,136,160,264,288,384] r8908 c8908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8908_40
  · exact u7047
  · exact u7048
  · exact u7049
  · exact u7050
  · exact u7051

theorem m8909_9 : Upper (D 9) (R 9) [34,5,192,80,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7032

theorem m8909_33 : Upper (D 9) (R 9) [34,5,192,80,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7038

theorem m8909_40 : Upper (D 9) (R 9) [34,5,192,80,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7042

theorem m8909_129 : Upper (D 9) (R 9) [34,5,192,80,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7047

def r8909 : Route 9 := (fun mask => (mask,id))

def c8909 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8909 : Upper (D 9) (R 9) [34,5,192,80] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r8909 c8909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8909_9
  · exact m8909_33
  · exact m8909_40
  · exact m8909_129
  · exact u7052
  · exact u7053
  · exact u7054
  · exact u7055
  · exact u7056
  · exact u7057

theorem m8910_9 : Upper (D 9) (R 9) [34,5,192,96,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7033

theorem m8910_129 : Upper (D 9) (R 9) [34,5,192,96,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7048

theorem m8910_136 : Upper (D 9) (R 9) [34,5,192,96,136] 13 :=
  permutation_upper _ _ _ [34,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7053

def r8910 : Route 9 := (fun mask => (mask,id))

def c8910 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8910 : Upper (D 9) (R 9) [34,5,192,96] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r8910 c8910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8910_9
  · exact m8910_129
  · exact m8910_136
  · exact u7058
  · exact u7059
  · exact u7060

def b8911 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 35 7 196 200 313 313 377 441 313), lower := (rows 35 7 196 200 16 32 64 128 256), losses := [] }

theorem u8911 : Upper (D 9) (R 9) [34,5,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8911 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8912_40 : Upper (D 9) (R 9) [34,5,192,257,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7044

theorem m8912_72 : Upper (D 9) (R 9) [34,5,192,257,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7054

theorem m8912_96 : Upper (D 9) (R 9) [34,5,192,257,96] 13 :=
  permutation_upper _ _ _ [34,5,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7058

theorem m8912_192 : Upper (D 9) (R 9) [34,5,192,257,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7061

def r8912 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8912 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8912 : Upper (D 9) (R 9) [34,5,192,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,257] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r8912 c8912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8912_40
  · exact m8912_72
  · exact m8912_96
  · exact m8912_192
  · exact u7064
  · exact u7065
  · exact u7066

theorem m8913_9 : Upper (D 9) (R 9) [34,5,192,272,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7035

theorem m8913_33 : Upper (D 9) (R 9) [34,5,192,272,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7039

theorem m8913_40 : Upper (D 9) (R 9) [34,5,192,272,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7045

theorem m8913_65 : Upper (D 9) (R 9) [34,5,192,272,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7049

theorem m8913_72 : Upper (D 9) (R 9) [34,5,192,272,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7055

theorem m8913_96 : Upper (D 9) (R 9) [34,5,192,272,96] 13 :=
  permutation_upper _ _ _ [34,5,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7059

theorem m8913_192 : Upper (D 9) (R 9) [34,5,192,272,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7062

theorem m8913_257 : Upper (D 9) (R 9) [34,5,192,272,257] 13 :=
  permutation_upper _ _ _ [34,5,192,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7064

def r8913 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8913 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8913 : Upper (D 9) (R 9) [34,5,192,272] 13 := by
  apply FastRouting.sound _ _ [34,5,192,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r8913 c8913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8913_9
  · exact m8913_33
  · exact m8913_40
  · exact m8913_65
  · exact m8913_72
  · exact m8913_96
  · exact m8913_192
  · exact m8913_257
  · exact u7067
  · exact u7068
  · exact u7069

theorem m8914_9 : Upper (D 9) (R 9) [34,5,192,288,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7036

theorem m8914_65 : Upper (D 9) (R 9) [34,5,192,288,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7050

theorem m8914_72 : Upper (D 9) (R 9) [34,5,192,288,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7056

theorem m8914_192 : Upper (D 9) (R 9) [34,5,192,288,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7063

theorem m8914_257 : Upper (D 9) (R 9) [34,5,192,288,257] 13 :=
  permutation_upper _ _ _ [34,5,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7065

theorem m8914_264 : Upper (D 9) (R 9) [34,5,192,288,264] 13 :=
  permutation_upper _ _ _ [34,5,192,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7068

def r8914 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8914 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8914 : Upper (D 9) (R 9) [34,5,192,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,288] 13 (by decide) (choices 2) [9,65,72,192,257,264,320] r8914 c8914
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8914_9
  · exact m8914_65
  · exact m8914_72
  · exact m8914_192
  · exact m8914_257
  · exact m8914_264
  · exact u7070

theorem m8915_9 : Upper (D 9) (R 9) [34,5,192,320,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7037

theorem m8915_33 : Upper (D 9) (R 9) [34,5,192,320,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7040

theorem m8915_40 : Upper (D 9) (R 9) [34,5,192,320,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7046

theorem m8915_129 : Upper (D 9) (R 9) [34,5,192,320,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7051

theorem m8915_136 : Upper (D 9) (R 9) [34,5,192,320,136] 13 :=
  permutation_upper _ _ _ [34,5,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7057

theorem m8915_160 : Upper (D 9) (R 9) [34,5,192,320,160] 13 :=
  permutation_upper _ _ _ [34,5,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7060

theorem m8915_257 : Upper (D 9) (R 9) [34,5,192,320,257] 13 :=
  permutation_upper _ _ _ [34,5,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7066

theorem m8915_264 : Upper (D 9) (R 9) [34,5,192,320,264] 13 :=
  permutation_upper _ _ _ [34,5,192,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7069

theorem m8915_288 : Upper (D 9) (R 9) [34,5,192,320,288] 13 :=
  permutation_upper _ _ _ [34,5,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7070

def r8915 : Route 9 := (fun mask => (mask,id))

def c8915 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8915 : Upper (D 9) (R 9) [34,5,192,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r8915 c8915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8915_9
  · exact m8915_33
  · exact m8915_40
  · exact m8915_129
  · exact m8915_136
  · exact m8915_160
  · exact m8915_257
  · exact m8915_264
  · exact m8915_288
  · exact u7071

def b8916 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 14 21 41 464 480 448 448 448), lower := (rows 35 14 21 41 16 32 64 128 256), losses := [] }

theorem u8916 : Upper (D 9) (R 9) [34,12,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8916 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8917 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8917 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8917 : Upper (D 9) (R 9) [34,12,17,65] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65] 13 (by decide) (choices 2) [96,160,192,384] r8917 c8917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7072
  · exact u7073
  · exact u7074
  · exact u7075

def r8918 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8918 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8918 : Upper (D 9) (R 9) [34,12,17,96] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96] 13 (by decide) (choices 2) [65,129,192,384] r8918 c8918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7076
  · exact u7077
  · exact u7078
  · exact u7079

def r8919 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8919 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8919 : Upper (D 9) (R 9) [34,12,17,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8919 c8919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7080
  · exact u7081
  · exact u7082
  · exact u7083
  · exact u7084
  · exact u7085
  · exact u7086

def b8920 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 14 37 73 464 496 464 464 464), lower := (rows 35 14 37 73 16 32 64 128 256), losses := [] }

theorem u8920 : Upper (D 9) (R 9) [34,12,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8920 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8921 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 14 37 88 465 481 449 449 449), lower := (rows 35 14 37 88 16 32 64 128 256), losses := [] }

theorem u8921 : Upper (D 9) (R 9) [34,12,33,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8921 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8922 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 14 37 200 465 497 465 465 465), lower := (rows 35 14 37 200 16 32 64 128 256), losses := [] }

theorem u8922 : Upper (D 9) (R 9) [34,12,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8922 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8923 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8923 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8923 : Upper (D 9) (R 9) [34,12,48,65] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65] 13 (by decide) (choices 2) [65,129,192,384] r8923 c8923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7087
  · exact u7088
  · exact u7089
  · exact u7090

def r8924 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8924 : Upper (D 9) (R 9) [34,12,48,192] 13 := by
  apply FastRouting.sound _ _ [34,12,48,192] 13 (by decide) (choices 2) [65,192,257,320] r8924 c8924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7091
  · exact u7092
  · exact u7093
  · exact u7094

def b8925 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 10, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(3,5),(3,7)], upper := (rows 35 14 69 73 432 432 496 432 432), lower := (rows 35 14 69 73 16 32 64 128 256), losses := [] }

theorem u8925 : Upper (D 9) (R 9) [34,12,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8925 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8926 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8926 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8926 : Upper (D 9) (R 9) [34,12,65,80] 13 := by
  apply FastRouting.sound _ _ [34,12,65,80] 13 (by decide) (choices 2) [33,129,160,384] r8926 c8926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7095
  · exact u7096
  · exact u7097
  · exact u7098

def b8927 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 104 401 433 465 401 401), lower := (rows 35 14 69 104 16 32 64 128 256), losses := [] }

theorem u8927 : Upper (D 9) (R 9) [34,12,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8927 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8928_160 : Upper (D 9) (R 9) [34,12,65,129,160] 13 :=
  permutation_upper _ _ _ [34,12,65,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7099

theorem m8928_384 : Upper (D 9) (R 9) [34,12,65,129,384] 13 :=
  permutation_upper _ _ _ [34,12,65,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7102

def r8928 : Route 9 := (fun mask => (mask,id))

def c8928 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8928 : Upper (D 9) (R 9) [34,12,65,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r8928 c8928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7099
  · exact m8928_160
  · exact u7100
  · exact u7101
  · exact u7102
  · exact m8928_384

def r8929 : Route 9 := (fun mask => (mask,id))

def c8929 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8929 : Upper (D 9) (R 9) [34,12,65,144] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r8929 c8929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7103
  · exact u7104
  · exact u7105
  · exact u7106
  · exact u7107
  · exact u7108
  · exact u7109
  · exact u7110
  · exact u7111
  · exact u7112

def r8930 : Route 9 := (fun mask => (mask,id))

def c8930 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8930 : Upper (D 9) (R 9) [34,12,65,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8930 c8930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7113
  · exact u7114
  · exact u7115
  · exact u7116
  · exact u7117
  · exact u7118

def r8931 : Route 9 := (fun mask => (mask,id))

def c8931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8931 : Upper (D 9) (R 9) [34,12,65,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192] 13 (by decide) (choices 2) [33,129,160,257,288,384] r8931 c8931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7119
  · exact u7120
  · exact u7121
  · exact u7122
  · exact u7123
  · exact u7124

def r8932 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8932 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8932 : Upper (D 9) (R 9) [34,12,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r8932 c8932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7125
  · exact u7126
  · exact u7127
  · exact u7128
  · exact u7129
  · exact u7130
  · exact u7131

def r8933 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8933 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8933 : Upper (D 9) (R 9) [34,12,80,96] 13 := by
  apply FastRouting.sound _ _ [34,12,80,96] 13 (by decide) (choices 2) [129,384] r8933 c8933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7132
  · exact u7133

def r8934 : Route 9 := (fun mask => (mask,id))

def c8934 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8934 : Upper (D 9) (R 9) [34,12,80,160] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8934 c8934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7134
  · exact u7135
  · exact u7136
  · exact u7137
  · exact u7138
  · exact u7139

def r8935 : Route 9 := (fun mask => (mask,id))

def c8935 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8935 : Upper (D 9) (R 9) [34,12,80,192] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192] 13 (by decide) (choices 2) [33,129,160,257,288,384] r8935 c8935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7140
  · exact u7141
  · exact u7142
  · exact u7143
  · exact u7144
  · exact u7145

def r8936 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8936 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8936 : Upper (D 9) (R 9) [34,12,80,384] 13 := by
  apply FastRouting.sound _ _ [34,12,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r8936 c8936
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7146
  · exact u7147
  · exact u7148
  · exact u7149
  · exact u7150
  · exact u7151
  · exact u7152

def r8937 : Route 9 := (fun mask => (mask,id))

def c8937 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8937 : Upper (D 9) (R 9) [34,12,96,192] 13 := by
  apply FastRouting.sound _ _ [34,12,96,192] 13 (by decide) (choices 2) [129,257,384] r8937 c8937
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7153
  · exact u7154
  · exact u7155

def r8938 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8938 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8938 : Upper (D 9) (R 9) [34,12,96,384] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384] 13 (by decide) (choices 2) [65,129,192,384] r8938 c8938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7156
  · exact u7157
  · exact u7158
  · exact u7159

def b8939 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 10, targets := 289 }], pairs := [(1,0),(1,5),(1,8),(3,0),(3,5)], upper := (rows 35 14 196 200 305 305 369 433 305), lower := (rows 35 14 196 200 16 32 64 128 256), losses := [] }

theorem u8939 : Upper (D 9) (R 9) [34,12,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8939 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8939
end Delivery.IrregularNine14.P09
