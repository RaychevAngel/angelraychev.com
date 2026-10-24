import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0592
import IrregularNine14P07C0593
import IrregularNine14P07C0594
import IrregularNine14P07C0595
import IrregularNine14P07C0596
import IrregularNine14P07C0597
import IrregularNine14P07C0598

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42480_5 : Upper (D 7) (R 7) [34,257,66,144,5] 13 :=
  permutation_upper _ _ _ [34,257,9,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35555

theorem m42480_9 : Upper (D 7) (R 7) [34,257,66,144,9] 13 :=
  permutation_upper _ _ _ [34,257,9,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35561

theorem m42480_12 : Upper (D 7) (R 7) [34,257,66,144,12] 13 :=
  permutation_upper _ _ _ [34,257,24,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35648

theorem m42480_33 : Upper (D 7) (R 7) [34,257,66,144,33] 13 :=
  permutation_upper _ _ _ [34,257,33,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35657

theorem m42480_36 : Upper (D 7) (R 7) [34,257,66,144,36] 13 :=
  permutation_upper _ _ _ [34,257,40,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35678

theorem m42480_40 : Upper (D 7) (R 7) [34,257,66,144,40] 13 :=
  permutation_upper _ _ _ [34,257,40,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35683

theorem m42480_65 : Upper (D 7) (R 7) [34,257,66,144,65] 13 :=
  permutation_upper _ _ _ [34,257,65,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35696

theorem m42480_68 : Upper (D 7) (R 7) [34,257,66,144,68] 13 :=
  permutation_upper _ _ _ [34,257,66,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35720

theorem m42480_72 : Upper (D 7) (R 7) [34,257,66,144,72] 13 :=
  permutation_upper _ _ _ [34,257,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35723

theorem m42480_96 : Upper (D 7) (R 7) [34,257,66,144,96] 13 :=
  permutation_upper _ _ _ [34,257,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35726

theorem m42480_129 : Upper (D 7) (R 7) [34,257,66,144,129] 13 :=
  permutation_upper _ _ _ [34,257,65,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35699

theorem m42480_132 : Upper (D 7) (R 7) [34,257,66,144,132] 13 :=
  permutation_upper _ _ _ [34,257,66,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35727

def r42480 : Route 9 := (fun mask => (mask,id))

def c42480 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42480 : Upper (D 7) (R 7) [34,257,66,144] 13 := by
  apply FastRouting.sound _ _ [34,257,66,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r42480 c42480
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42480_5
  · exact m42480_9
  · exact m42480_12
  · exact m42480_33
  · exact m42480_36
  · exact m42480_40
  · exact m42480_65
  · exact m42480_68
  · exact m42480_72
  · exact m42480_96
  · exact m42480_129
  · exact m42480_132
  · exact u35730
  · exact u35731
  · exact u35732

theorem m42481_5 : Upper (D 7) (R 7) [34,257,66,160,5] 13 :=
  permutation_upper _ _ _ [34,257,9,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35556

theorem m42481_9 : Upper (D 7) (R 7) [34,257,66,160,9] 13 :=
  permutation_upper _ _ _ [34,257,9,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35577

theorem m42481_12 : Upper (D 7) (R 7) [34,257,66,160,12] 13 :=
  permutation_upper _ _ _ [34,257,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35649

theorem m42481_65 : Upper (D 7) (R 7) [34,257,66,160,65] 13 :=
  permutation_upper _ _ _ [34,257,65,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35698

theorem m42481_68 : Upper (D 7) (R 7) [34,257,66,160,68] 13 :=
  permutation_upper _ _ _ [34,257,66,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35721

theorem m42481_72 : Upper (D 7) (R 7) [34,257,66,160,72] 13 :=
  permutation_upper _ _ _ [34,257,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35724

theorem m42481_129 : Upper (D 7) (R 7) [34,257,66,160,129] 13 :=
  permutation_upper _ _ _ [34,257,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35706

theorem m42481_132 : Upper (D 7) (R 7) [34,257,66,160,132] 13 :=
  permutation_upper _ _ _ [34,257,66,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35728

theorem m42481_136 : Upper (D 7) (R 7) [34,257,66,160,136] 13 :=
  permutation_upper _ _ _ [34,257,66,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35731

def r42481 : Route 9 := (fun mask => (mask,id))

def c42481 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42481 : Upper (D 7) (R 7) [34,257,66,160] 13 := by
  apply FastRouting.sound _ _ [34,257,66,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r42481 c42481
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42481_5
  · exact m42481_9
  · exact m42481_12
  · exact m42481_65
  · exact m42481_68
  · exact m42481_72
  · exact m42481_129
  · exact m42481_132
  · exact m42481_136
  · exact u35733

theorem m42482_5 : Upper (D 7) (R 7) [34,257,66,192,5] 13 :=
  permutation_upper _ _ _ [34,257,9,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35557

theorem m42482_9 : Upper (D 7) (R 7) [34,257,66,192,9] 13 :=
  permutation_upper _ _ _ [34,257,9,192,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35583

theorem m42482_12 : Upper (D 7) (R 7) [34,257,66,192,12] 13 :=
  permutation_upper _ _ _ [34,257,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35650

theorem m42482_33 : Upper (D 7) (R 7) [34,257,66,192,33] 13 :=
  permutation_upper _ _ _ [34,257,33,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35659

theorem m42482_36 : Upper (D 7) (R 7) [34,257,66,192,36] 13 :=
  permutation_upper _ _ _ [34,257,40,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35679

theorem m42482_40 : Upper (D 7) (R 7) [34,257,66,192,40] 13 :=
  permutation_upper _ _ _ [34,257,40,192,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35693

theorem m42482_129 : Upper (D 7) (R 7) [34,257,66,192,129] 13 :=
  permutation_upper _ _ _ [34,257,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35712

theorem m42482_132 : Upper (D 7) (R 7) [34,257,66,192,132] 13 :=
  permutation_upper _ _ _ [34,257,66,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35729

theorem m42482_136 : Upper (D 7) (R 7) [34,257,66,192,136] 13 :=
  permutation_upper _ _ _ [34,257,66,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35732

theorem m42482_160 : Upper (D 7) (R 7) [34,257,66,192,160] 13 :=
  permutation_upper _ _ _ [34,257,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35733

def r42482 : Route 9 := (fun mask => (mask,id))

def c42482 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42482 : Upper (D 7) (R 7) [34,257,66,192] 13 := by
  apply FastRouting.sound _ _ [34,257,66,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r42482 c42482
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42482_5
  · exact m42482_9
  · exact m42482_12
  · exact m42482_33
  · exact m42482_36
  · exact m42482_40
  · exact m42482_129
  · exact m42482_132
  · exact m42482_136
  · exact m42482_160

def b42483 : PairBound 9 := { available := 179, camps := [{ cop := 6, region := 12, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 76 179 179 243 179 435), lower := (rows 35 259 76 76 16 32 64 128 256), losses := [] }

theorem u42483 : Upper (D 7) (R 7) [34,257,72,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42484 : PairBound 9 := { available := 167, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 88 183 167 231 167 423), lower := (rows 35 259 76 88 16 32 64 128 256), losses := [] }

theorem u42484 : Upper (D 7) (R 7) [34,257,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42485 : PairBound 9 := { available := 151, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 104 151 183 215 151 407), lower := (rows 35 259 76 104 16 32 64 128 256), losses := [] }

theorem u42485 : Upper (D 7) (R 7) [34,257,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42486_3 : Upper (D 7) (R 7) [34,257,72,132,3] 13 :=
  permutation_upper _ _ _ [34,257,3,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35531

theorem m42486_33 : Upper (D 7) (R 7) [34,257,72,132,33] 13 :=
  permutation_upper _ _ _ [34,257,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35662

theorem m42486_34 : Upper (D 7) (R 7) [34,257,72,132,34] 13 :=
  permutation_upper _ _ _ [34,257,34,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35669

theorem m42486_65 : Upper (D 7) (R 7) [34,257,72,132,65] 13 :=
  permutation_upper _ _ _ [34,257,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35704

theorem m42486_66 : Upper (D 7) (R 7) [34,257,72,132,66] 13 :=
  permutation_upper _ _ _ [34,257,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35723

theorem m42486_129 : Upper (D 7) (R 7) [34,257,72,132,129] 13 :=
  permutation_upper _ _ _ [34,257,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35704

theorem m42486_130 : Upper (D 7) (R 7) [34,257,72,132,130] 13 :=
  permutation_upper _ _ _ [34,257,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35723

theorem m42486_160 : Upper (D 7) (R 7) [34,257,72,132,160] 13 :=
  permutation_upper _ _ _ [34,257,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35738

def r42486 : Route 9 := (fun mask => (mask,id))

def c42486 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42486 : Upper (D 7) (R 7) [34,257,72,132] 13 := by
  apply FastRouting.sound _ _ [34,257,72,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42486 c42486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42486_3
  · exact m42486_33
  · exact m42486_34
  · exact m42486_65
  · exact m42486_66
  · exact u35738
  · exact m42486_129
  · exact m42486_130
  · exact m42486_160
  · exact u35739

theorem m42487_3 : Upper (D 7) (R 7) [34,257,72,144,3] 13 :=
  permutation_upper _ _ _ [34,257,3,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35528

theorem m42487_5 : Upper (D 7) (R 7) [34,257,72,144,5] 13 :=
  permutation_upper _ _ _ [34,257,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35571

theorem m42487_6 : Upper (D 7) (R 7) [34,257,72,144,6] 13 :=
  permutation_upper _ _ _ [34,257,10,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35616

theorem m42487_33 : Upper (D 7) (R 7) [34,257,72,144,33] 13 :=
  permutation_upper _ _ _ [34,257,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35660

theorem m42487_34 : Upper (D 7) (R 7) [34,257,72,144,34] 13 :=
  permutation_upper _ _ _ [34,257,34,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35667

theorem m42487_36 : Upper (D 7) (R 7) [34,257,72,144,36] 13 :=
  permutation_upper _ _ _ [34,257,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35690

theorem m42487_65 : Upper (D 7) (R 7) [34,257,72,144,65] 13 :=
  permutation_upper _ _ _ [34,257,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35703

theorem m42487_66 : Upper (D 7) (R 7) [34,257,72,144,66] 13 :=
  permutation_upper _ _ _ [34,257,66,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35722

theorem m42487_68 : Upper (D 7) (R 7) [34,257,72,144,68] 13 :=
  permutation_upper _ _ _ [34,257,72,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35735

theorem m42487_129 : Upper (D 7) (R 7) [34,257,72,144,129] 13 :=
  permutation_upper _ _ _ [34,257,65,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35700

theorem m42487_130 : Upper (D 7) (R 7) [34,257,72,144,130] 13 :=
  permutation_upper _ _ _ [34,257,66,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35720

theorem m42487_132 : Upper (D 7) (R 7) [34,257,72,144,132] 13 :=
  permutation_upper _ _ _ [34,257,72,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35735

theorem m42487_160 : Upper (D 7) (R 7) [34,257,72,144,160] 13 :=
  permutation_upper _ _ _ [34,257,72,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35737

def r42487 : Route 9 := (fun mask => (mask,id))

def c42487 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42487 : Upper (D 7) (R 7) [34,257,72,144] 13 := by
  apply FastRouting.sound _ _ [34,257,72,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r42487 c42487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42487_3
  · exact m42487_5
  · exact m42487_6
  · exact m42487_33
  · exact m42487_34
  · exact m42487_36
  · exact m42487_65
  · exact m42487_66
  · exact m42487_68
  · exact u35740
  · exact m42487_129
  · exact m42487_130
  · exact m42487_132
  · exact m42487_160
  · exact u35741

theorem m42488_3 : Upper (D 7) (R 7) [34,257,72,160,3] 13 :=
  permutation_upper _ _ _ [34,257,3,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35532

theorem m42488_5 : Upper (D 7) (R 7) [34,257,72,160,5] 13 :=
  permutation_upper _ _ _ [34,257,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35572

theorem m42488_6 : Upper (D 7) (R 7) [34,257,72,160,6] 13 :=
  permutation_upper _ _ _ [34,257,10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35617

theorem m42488_65 : Upper (D 7) (R 7) [34,257,72,160,65] 13 :=
  permutation_upper _ _ _ [34,257,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35705

theorem m42488_66 : Upper (D 7) (R 7) [34,257,72,160,66] 13 :=
  permutation_upper _ _ _ [34,257,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35724

theorem m42488_68 : Upper (D 7) (R 7) [34,257,72,160,68] 13 :=
  permutation_upper _ _ _ [34,257,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35736

theorem m42488_129 : Upper (D 7) (R 7) [34,257,72,160,129] 13 :=
  permutation_upper _ _ _ [34,257,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35708

theorem m42488_130 : Upper (D 7) (R 7) [34,257,72,160,130] 13 :=
  permutation_upper _ _ _ [34,257,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35726

theorem m42488_132 : Upper (D 7) (R 7) [34,257,72,160,132] 13 :=
  permutation_upper _ _ _ [34,257,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35740

def r42488 : Route 9 := (fun mask => (mask,id))

def c42488 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42488 : Upper (D 7) (R 7) [34,257,72,160] 13 := by
  apply FastRouting.sound _ _ [34,257,72,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r42488 c42488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42488_3
  · exact m42488_5
  · exact m42488_6
  · exact m42488_65
  · exact m42488_66
  · exact m42488_68
  · exact m42488_129
  · exact m42488_130
  · exact m42488_132
  · exact u35742

def b42489 : PairBound 9 := { available := 183, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 200 183 183 247 183 439), lower := (rows 35 259 76 200 16 32 64 128 256), losses := [] }

theorem u42489 : Upper (D 7) (R 7) [34,257,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42490_3 : Upper (D 7) (R 7) [34,257,80,96,3] 13 :=
  permutation_upper _ _ _ [34,257,3,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35527

theorem m42490_5 : Upper (D 7) (R 7) [34,257,80,96,5] 13 :=
  permutation_upper _ _ _ [34,257,9,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35560

theorem m42490_6 : Upper (D 7) (R 7) [34,257,80,96,6] 13 :=
  permutation_upper _ _ _ [34,257,10,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35606

theorem m42490_9 : Upper (D 7) (R 7) [34,257,80,96,9] 13 :=
  permutation_upper _ _ _ [34,257,9,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35576

theorem m42490_10 : Upper (D 7) (R 7) [34,257,80,96,10] 13 :=
  permutation_upper _ _ _ [34,257,10,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35620

theorem m42490_12 : Upper (D 7) (R 7) [34,257,80,96,12] 13 :=
  permutation_upper _ _ _ [34,257,24,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35651

theorem m42490_129 : Upper (D 7) (R 7) [34,257,80,96,129] 13 :=
  permutation_upper _ _ _ [34,257,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35714

theorem m42490_130 : Upper (D 7) (R 7) [34,257,80,96,130] 13 :=
  permutation_upper _ _ _ [34,257,66,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35728

theorem m42490_132 : Upper (D 7) (R 7) [34,257,80,96,132] 13 :=
  permutation_upper _ _ _ [34,257,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35738

theorem m42490_136 : Upper (D 7) (R 7) [34,257,80,96,136] 13 :=
  permutation_upper _ _ _ [34,257,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35740

def r42490 : Route 9 := (fun mask => (mask,id))

def c42490 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42490 : Upper (D 7) (R 7) [34,257,80,96] 13 := by
  apply FastRouting.sound _ _ [34,257,80,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r42490 c42490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42490_3
  · exact m42490_5
  · exact m42490_6
  · exact m42490_9
  · exact m42490_10
  · exact m42490_12
  · exact m42490_129
  · exact m42490_130
  · exact m42490_132
  · exact m42490_136

theorem m42491_3 : Upper (D 7) (R 7) [34,257,80,160,3] 13 :=
  permutation_upper _ _ _ [34,257,3,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35529

theorem m42491_5 : Upper (D 7) (R 7) [34,257,80,160,5] 13 :=
  permutation_upper _ _ _ [34,257,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35562

theorem m42491_6 : Upper (D 7) (R 7) [34,257,80,160,6] 13 :=
  permutation_upper _ _ _ [34,257,10,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35608

theorem m42491_9 : Upper (D 7) (R 7) [34,257,80,160,9] 13 :=
  permutation_upper _ _ _ [34,257,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35578

theorem m42491_10 : Upper (D 7) (R 7) [34,257,80,160,10] 13 :=
  permutation_upper _ _ _ [34,257,10,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35622

theorem m42491_12 : Upper (D 7) (R 7) [34,257,80,160,12] 13 :=
  permutation_upper _ _ _ [34,257,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35652

theorem m42491_65 : Upper (D 7) (R 7) [34,257,80,160,65] 13 :=
  permutation_upper _ _ _ [34,257,65,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35701

theorem m42491_66 : Upper (D 7) (R 7) [34,257,80,160,66] 13 :=
  permutation_upper _ _ _ [34,257,66,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35721

theorem m42491_68 : Upper (D 7) (R 7) [34,257,80,160,68] 13 :=
  permutation_upper _ _ _ [34,257,72,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35734

theorem m42491_72 : Upper (D 7) (R 7) [34,257,80,160,72] 13 :=
  permutation_upper _ _ _ [34,257,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35736

theorem m42491_129 : Upper (D 7) (R 7) [34,257,80,160,129] 13 :=
  permutation_upper _ _ _ [34,257,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35707

theorem m42491_130 : Upper (D 7) (R 7) [34,257,80,160,130] 13 :=
  permutation_upper _ _ _ [34,257,66,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35725

theorem m42491_132 : Upper (D 7) (R 7) [34,257,80,160,132] 13 :=
  permutation_upper _ _ _ [34,257,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35738

theorem m42491_136 : Upper (D 7) (R 7) [34,257,80,160,136] 13 :=
  permutation_upper _ _ _ [34,257,72,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35737

theorem m42491_192 : Upper (D 7) (R 7) [34,257,80,160,192] 13 :=
  permutation_upper _ _ _ [34,257,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35743

def r42491 : Route 9 := (fun mask => (mask,id))

def c42491 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42491 : Upper (D 7) (R 7) [34,257,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,80,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,129,130,132,136,192] r42491 c42491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42491_3
  · exact m42491_5
  · exact m42491_6
  · exact m42491_9
  · exact m42491_10
  · exact m42491_12
  · exact m42491_65
  · exact m42491_66
  · exact m42491_68
  · exact m42491_72
  · exact m42491_129
  · exact m42491_130
  · exact m42491_132
  · exact m42491_136
  · exact m42491_192

theorem m42492_3 : Upper (D 7) (R 7) [34,257,80,192,3] 13 :=
  permutation_upper _ _ _ [34,257,3,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35530

theorem m42492_5 : Upper (D 7) (R 7) [34,257,80,192,5] 13 :=
  permutation_upper _ _ _ [34,257,9,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35563

theorem m42492_6 : Upper (D 7) (R 7) [34,257,80,192,6] 13 :=
  permutation_upper _ _ _ [34,257,10,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35609

theorem m42492_9 : Upper (D 7) (R 7) [34,257,80,192,9] 13 :=
  permutation_upper _ _ _ [34,257,9,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35584

theorem m42492_10 : Upper (D 7) (R 7) [34,257,80,192,10] 13 :=
  permutation_upper _ _ _ [34,257,10,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35627

theorem m42492_12 : Upper (D 7) (R 7) [34,257,80,192,12] 13 :=
  permutation_upper _ _ _ [34,257,24,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35653

theorem m42492_33 : Upper (D 7) (R 7) [34,257,80,192,33] 13 :=
  permutation_upper _ _ _ [34,257,33,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35661

theorem m42492_34 : Upper (D 7) (R 7) [34,257,80,192,34] 13 :=
  permutation_upper _ _ _ [34,257,34,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35668

theorem m42492_36 : Upper (D 7) (R 7) [34,257,80,192,36] 13 :=
  permutation_upper _ _ _ [34,257,40,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35684

theorem m42492_40 : Upper (D 7) (R 7) [34,257,80,192,40] 13 :=
  permutation_upper _ _ _ [34,257,40,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35694

theorem m42492_129 : Upper (D 7) (R 7) [34,257,80,192,129] 13 :=
  permutation_upper _ _ _ [34,257,65,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35715

theorem m42492_130 : Upper (D 7) (R 7) [34,257,80,192,130] 13 :=
  permutation_upper _ _ _ [34,257,66,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35729

theorem m42492_132 : Upper (D 7) (R 7) [34,257,80,192,132] 13 :=
  permutation_upper _ _ _ [34,257,72,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35739

theorem m42492_136 : Upper (D 7) (R 7) [34,257,80,192,136] 13 :=
  permutation_upper _ _ _ [34,257,72,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35741

theorem m42492_160 : Upper (D 7) (R 7) [34,257,80,192,160] 13 :=
  permutation_upper _ _ _ [34,257,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35742

def r42492 : Route 9 := (fun mask => (mask,id))

def c42492 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42492 : Upper (D 7) (R 7) [34,257,80,192] 13 := by
  apply FastRouting.sound _ _ [34,257,80,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,129,130,132,136,160] r42492 c42492
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42492_3
  · exact m42492_5
  · exact m42492_6
  · exact m42492_9
  · exact m42492_10
  · exact m42492_12
  · exact m42492_33
  · exact m42492_34
  · exact m42492_36
  · exact m42492_40
  · exact m42492_129
  · exact m42492_130
  · exact m42492_132
  · exact m42492_136
  · exact m42492_160

theorem m42493_3 : Upper (D 7) (R 7) [34,257,96,192,3] 13 :=
  permutation_upper _ _ _ [34,257,3,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35533

theorem m42493_5 : Upper (D 7) (R 7) [34,257,96,192,5] 13 :=
  permutation_upper _ _ _ [34,257,9,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35579

theorem m42493_6 : Upper (D 7) (R 7) [34,257,96,192,6] 13 :=
  permutation_upper _ _ _ [34,257,10,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35623

theorem m42493_9 : Upper (D 7) (R 7) [34,257,96,192,9] 13 :=
  permutation_upper _ _ _ [34,257,9,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35585

theorem m42493_10 : Upper (D 7) (R 7) [34,257,96,192,10] 13 :=
  permutation_upper _ _ _ [34,257,10,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35628

theorem m42493_12 : Upper (D 7) (R 7) [34,257,96,192,12] 13 :=
  permutation_upper _ _ _ [34,257,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35654

theorem m42493_129 : Upper (D 7) (R 7) [34,257,96,192,129] 13 :=
  permutation_upper _ _ _ [34,257,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35719

theorem m42493_130 : Upper (D 7) (R 7) [34,257,96,192,130] 13 :=
  permutation_upper _ _ _ [34,257,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35733

theorem m42493_132 : Upper (D 7) (R 7) [34,257,96,192,132] 13 :=
  permutation_upper _ _ _ [34,257,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35742

theorem m42493_136 : Upper (D 7) (R 7) [34,257,96,192,136] 13 :=
  permutation_upper _ _ _ [34,257,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35743

def r42493 : Route 9 := (fun mask => (mask,id))

def c42493 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42493 : Upper (D 7) (R 7) [34,257,96,192] 13 := by
  apply FastRouting.sound _ _ [34,257,96,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r42493 c42493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42493_3
  · exact m42493_5
  · exact m42493_6
  · exact m42493_9
  · exact m42493_10
  · exact m42493_12
  · exact m42493_129
  · exact m42493_130
  · exact m42493_132
  · exact m42493_136

def b42494 : PairBound 9 := { available := 63, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 35 259 196 200 63 63 127 191 319), lower := (rows 35 259 196 200 16 32 64 128 256), losses := [] }

theorem u42494 : Upper (D 7) (R 7) [34,257,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42495 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 262 13 11 240 240 240 240 496), lower := (rows 35 262 13 11 16 32 64 128 256), losses := [] }

theorem u42495 : Upper (D 7) (R 7) [34,260,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42496 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 262 13 25 242 226 226 226 482), lower := (rows 35 262 13 25 16 32 64 128 256), losses := [] }

theorem u42496 : Upper (D 7) (R 7) [34,260,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42497 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42497 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42497 : Upper (D 7) (R 7) [34,260,9,18] 13 := by
  apply FastRouting.sound _ _ [34,260,9,18] 13 (by decide) (choices 2) [33,65,96,192] r42497 c42497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u35744
  · exact u35745
  · exact u35746
  · exact u35747

def b42498 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 262 13 41 210 242 210 210 466), lower := (rows 35 262 13 41 16 32 64 128 256), losses := [] }

theorem u42498 : Upper (D 7) (R 7) [34,260,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42499 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 13 42 209 241 209 209 465), lower := (rows 35 262 13 42 16 32 64 128 256), losses := [] }

theorem u42499 : Upper (D 7) (R 7) [34,260,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42500 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42500 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42500 : Upper (D 7) (R 7) [34,260,9,48] 13 := by
  apply FastRouting.sound _ _ [34,260,9,48] 13 (by decide) (choices 2) [3,65,66,192] r42500 c42500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u35748
  · exact u35749
  · exact u35750
  · exact u35751

def b42501 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 262 13 73 242 242 242 242 498), lower := (rows 35 262 13 73 16 32 64 128 256), losses := [] }

theorem u42501 : Upper (D 7) (R 7) [34,260,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42502 : Route 9 := (fun mask => (mask,id))

def c42502 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42502 : Upper (D 7) (R 7) [34,260,9,66] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42502 c42502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35752
  · exact u35753
  · exact u35754
  · exact u35755
  · exact u35756
  · exact u35757

def r42503 : Route 9 := (fun mask => (mask,id))

def c42503 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42503 : Upper (D 7) (R 7) [34,260,9,80] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42503 c42503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35758
  · exact u35759
  · exact u35760
  · exact u35761
  · exact u35762
  · exact u35763
  · exact u35764
  · exact u35765
  · exact u35766
  · exact u35767

def r42504 : Route 9 := (fun mask => (mask,id))

def c42504 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42504 : Upper (D 7) (R 7) [34,260,9,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42504 c42504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35768
  · exact u35769
  · exact u35770
  · exact u35771
  · exact u35772
  · exact u35773

def r42505 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42505 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42505 : Upper (D 7) (R 7) [34,260,9,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r42505 c42505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35774
  · exact u35775
  · exact u35776
  · exact u35777
  · exact u35778
  · exact u35779
  · exact u35780

def r42506 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42506 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42506 : Upper (D 7) (R 7) [34,260,10,17] 13 := by
  apply FastRouting.sound _ _ [34,260,10,17] 13 (by decide) (choices 2) [33,65,96,192] r42506 c42506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u35781
  · exact u35782
  · exact u35783
  · exact u35784

def b42507 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 14 41 209 241 209 209 465), lower := (rows 35 262 14 41 16 32 64 128 256), losses := [] }

theorem u42507 : Upper (D 7) (R 7) [34,260,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42508 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42508 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42508 : Upper (D 7) (R 7) [34,260,10,48] 13 := by
  apply FastRouting.sound _ _ [34,260,10,48] 13 (by decide) (choices 2) [65,192] r42508 c42508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u35785
  · exact u35786

def r42509 : Route 9 := (fun mask => (mask,id))

def c42509 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42509 : Upper (D 7) (R 7) [34,260,10,65] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42509 c42509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35787
  · exact u35788
  · exact u35789
  · exact u35790
  · exact u35791
  · exact u35792

def r42510 : Route 9 := (fun mask => (mask,id))

def c42510 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42510 : Upper (D 7) (R 7) [34,260,10,80] 13 := by
  apply FastRouting.sound _ _ [34,260,10,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42510 c42510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35793
  · exact u35794
  · exact u35795
  · exact u35796
  · exact u35797
  · exact u35798

def r42511 : Route 9 := (fun mask => (mask,id))

def c42511 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42511 : Upper (D 7) (R 7) [34,260,10,96] 13 := by
  apply FastRouting.sound _ _ [34,260,10,96] 13 (by decide) (choices 2) [65,129,192] r42511 c42511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u35799
  · exact u35800
  · exact u35801

def r42512 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42512 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42512 : Upper (D 7) (R 7) [34,260,10,192] 13 := by
  apply FastRouting.sound _ _ [34,260,10,192] 13 (by decide) (choices 2) [33,65,96,192] r42512 c42512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u35802
  · exact u35803
  · exact u35804
  · exact u35805

def b42513 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 28 11 241 225 225 225 481), lower := (rows 35 262 28 11 16 32 64 128 256), losses := [] }

theorem u42513 : Upper (D 7) (R 7) [34,260,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42514 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 28 41 211 227 195 195 451), lower := (rows 35 262 28 41 16 32 64 128 256), losses := [] }

theorem u42514 : Upper (D 7) (R 7) [34,260,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42515 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 28 42 209 225 193 193 449), lower := (rows 35 262 28 42 16 32 64 128 256), losses := [] }

theorem u42515 : Upper (D 7) (R 7) [34,260,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42516_3 : Upper (D 7) (R 7) [34,260,24,65,3] 13 :=
  permutation_upper _ _ _ [34,260,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35806

theorem m42516_33 : Upper (D 7) (R 7) [34,260,24,65,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35809

theorem m42516_34 : Upper (D 7) (R 7) [34,260,24,65,34] 13 :=
  permutation_upper _ _ _ [34,260,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35812

def r42516 : Route 9 := (fun mask => (mask,id))

def c42516 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42516 : Upper (D 7) (R 7) [34,260,24,65] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42516 c42516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42516_3
  · exact m42516_33
  · exact m42516_34
  · exact u35814
  · exact u35815
  · exact u35816
  · exact u35817
  · exact u35818
  · exact u35819
  · exact u35820

theorem m42517_33 : Upper (D 7) (R 7) [34,260,24,66,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35810

theorem m42517_65 : Upper (D 7) (R 7) [34,260,24,66,65] 13 :=
  permutation_upper _ _ _ [34,260,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35815

theorem m42517_129 : Upper (D 7) (R 7) [34,260,24,66,129] 13 :=
  permutation_upper _ _ _ [34,260,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35818

def r42517 : Route 9 := (fun mask => (mask,id))

def c42517 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42517 : Upper (D 7) (R 7) [34,260,24,66] 13 := by
  apply FastRouting.sound _ _ [34,260,24,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42517 c42517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42517_33
  · exact m42517_65
  · exact u35821
  · exact m42517_129
  · exact u35822
  · exact u35823

theorem m42518_3 : Upper (D 7) (R 7) [34,260,24,96,3] 13 :=
  permutation_upper _ _ _ [34,260,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35807

theorem m42518_65 : Upper (D 7) (R 7) [34,260,24,96,65] 13 :=
  permutation_upper _ _ _ [34,260,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35816

theorem m42518_66 : Upper (D 7) (R 7) [34,260,24,96,66] 13 :=
  permutation_upper _ _ _ [34,260,24,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35821

theorem m42518_129 : Upper (D 7) (R 7) [34,260,24,96,129] 13 :=
  permutation_upper _ _ _ [34,260,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35819

theorem m42518_130 : Upper (D 7) (R 7) [34,260,24,96,130] 13 :=
  permutation_upper _ _ _ [34,260,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35822

def r42518 : Route 9 := (fun mask => (mask,id))

def c42518 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42518 : Upper (D 7) (R 7) [34,260,24,96] 13 := by
  apply FastRouting.sound _ _ [34,260,24,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42518 c42518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42518_3
  · exact m42518_65
  · exact m42518_66
  · exact m42518_129
  · exact m42518_130
  · exact u35824

theorem m42519_3 : Upper (D 7) (R 7) [34,260,24,192,3] 13 :=
  permutation_upper _ _ _ [34,260,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35808

theorem m42519_33 : Upper (D 7) (R 7) [34,260,24,192,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35811

theorem m42519_34 : Upper (D 7) (R 7) [34,260,24,192,34] 13 :=
  permutation_upper _ _ _ [34,260,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35813

theorem m42519_65 : Upper (D 7) (R 7) [34,260,24,192,65] 13 :=
  permutation_upper _ _ _ [34,260,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35820

theorem m42519_66 : Upper (D 7) (R 7) [34,260,24,192,66] 13 :=
  permutation_upper _ _ _ [34,260,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35823

theorem m42519_96 : Upper (D 7) (R 7) [34,260,24,192,96] 13 :=
  permutation_upper _ _ _ [34,260,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35824

def r42519 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42519 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42519 : Upper (D 7) (R 7) [34,260,24,192] 13 := by
  apply FastRouting.sound _ _ [34,260,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r42519 c42519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42519_3
  · exact m42519_33
  · exact m42519_34
  · exact m42519_65
  · exact m42519_66
  · exact m42519_96
  · exact u35825

def b42520 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 44 11 209 241 209 209 465), lower := (rows 35 262 44 11 16 32 64 128 256), losses := [] }

theorem u42520 : Upper (D 7) (R 7) [34,260,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42521 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42521 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42521 : Upper (D 7) (R 7) [34,260,40,17] 13 := by
  apply FastRouting.sound _ _ [34,260,40,17] 13 (by decide) (choices 2) [3,65,66,192] r42521 c42521
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u35826
  · exact u35827
  · exact u35828
  · exact u35829

def r42522 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42522 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42522 : Upper (D 7) (R 7) [34,260,40,18] 13 := by
  apply FastRouting.sound _ _ [34,260,40,18] 13 (by decide) (choices 2) [65,192] r42522 c42522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u35830
  · exact u35831

def r42523 : Route 9 := (fun mask => (mask,id))

def c42523 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42523 : Upper (D 7) (R 7) [34,260,40,65] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42523 c42523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35832
  · exact u35833
  · exact u35834
  · exact u35835
  · exact u35836
  · exact u35837

def r42524 : Route 9 := (fun mask => (mask,id))

def c42524 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42524 : Upper (D 7) (R 7) [34,260,40,66] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66] 13 (by decide) (choices 2) [65,129,192] r42524 c42524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u35838
  · exact u35839
  · exact u35840

def r42525 : Route 9 := (fun mask => (mask,id))

def c42525 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42525 : Upper (D 7) (R 7) [34,260,40,80] 13 := by
  apply FastRouting.sound _ _ [34,260,40,80] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42525 c42525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35841
  · exact u35842
  · exact u35843
  · exact u35844
  · exact u35845
  · exact u35846

def r42526 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42526 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42526 : Upper (D 7) (R 7) [34,260,40,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,192] 13 (by decide) (choices 2) [3,65,66,192] r42526 c42526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u35847
  · exact u35848
  · exact u35849
  · exact u35850

def b42527 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 69 11 248 248 248 248 504), lower := (rows 35 262 69 11 16 32 64 128 256), losses := [] }

theorem u42527 : Upper (D 7) (R 7) [34,260,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42528 : Route 9 := (fun mask => (mask,id))

def c42528 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42528 : Upper (D 7) (R 7) [34,260,65,17] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r42528 c42528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35857
  · exact u35858
  · exact u35859
  · exact u35860
  · exact u35861
  · exact u35862
  · exact u35863
  · exact u35864
  · exact u35865
  · exact u35866

theorem m42529_9 : Upper (D 7) (R 7) [34,260,65,18,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35857

def r42529 : Route 9 := (fun mask => (mask,id))

def c42529 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42529 : Upper (D 7) (R 7) [34,260,65,18] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42529 c42529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42529_9
  · exact u35867
  · exact u35868
  · exact u35869
  · exact u35870
  · exact u35871
  · exact u35872
  · exact u35873
  · exact u35874
  · exact u35875

def b42530 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 69 41 218 250 218 218 474), lower := (rows 35 262 69 41 16 32 64 128 256), losses := [] }

theorem u42530 : Upper (D 7) (R 7) [34,260,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42531 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 69 42 217 249 217 217 473), lower := (rows 35 262 69 42 16 32 64 128 256), losses := [] }

theorem u42531 : Upper (D 7) (R 7) [34,260,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42532_3 : Upper (D 7) (R 7) [34,260,65,48,3] 13 :=
  permutation_upper _ _ _ [34,260,65,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35851

theorem m42532_9 : Upper (D 7) (R 7) [34,260,65,48,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35859

theorem m42532_10 : Upper (D 7) (R 7) [34,260,65,48,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35868

def r42532 : Route 9 := (fun mask => (mask,id))

def c42532 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42532 : Upper (D 7) (R 7) [34,260,65,48] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42532 c42532
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42532_3
  · exact m42532_9
  · exact m42532_10
  · exact u35885
  · exact u35886
  · exact u35887
  · exact u35888
  · exact u35889
  · exact u35890
  · exact u35891

def b42533 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 35 262 69 73 186 186 250 186 442), lower := (rows 35 262 69 73 16 32 64 128 256), losses := [] }

theorem u42533 : Upper (D 7) (R 7) [34,260,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42534_9 : Upper (D 7) (R 7) [34,260,65,66,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35860

theorem m42534_33 : Upper (D 7) (R 7) [34,260,65,66,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35876

theorem m42534_40 : Upper (D 7) (R 7) [34,260,65,66,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35886

def r42534 : Route 9 := (fun mask => (mask,id))

def c42534 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42534 : Upper (D 7) (R 7) [34,260,65,66] 13 := by
  apply FastRouting.sound _ _ [34,260,65,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r42534 c42534
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42534_9
  · exact m42534_33
  · exact m42534_40
  · exact u35895
  · exact u35896
  · exact u35897

theorem m42535_3 : Upper (D 7) (R 7) [34,260,65,80,3] 13 :=
  permutation_upper _ _ _ [34,260,65,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35852

theorem m42535_9 : Upper (D 7) (R 7) [34,260,65,80,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35861

theorem m42535_10 : Upper (D 7) (R 7) [34,260,65,80,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35870

theorem m42535_33 : Upper (D 7) (R 7) [34,260,65,80,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35877

theorem m42535_34 : Upper (D 7) (R 7) [34,260,65,80,34] 13 :=
  permutation_upper _ _ _ [34,260,65,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35881

theorem m42535_40 : Upper (D 7) (R 7) [34,260,65,80,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35887

def r42535 : Route 9 := (fun mask => (mask,id))

def c42535 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42535 : Upper (D 7) (R 7) [34,260,65,80] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42535 c42535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42535_3
  · exact m42535_9
  · exact m42535_10
  · exact m42535_33
  · exact m42535_34
  · exact m42535_40
  · exact u35898
  · exact u35899
  · exact u35900
  · exact u35901

theorem m42536_3 : Upper (D 7) (R 7) [34,260,65,96,3] 13 :=
  permutation_upper _ _ _ [34,260,65,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35853

theorem m42536_9 : Upper (D 7) (R 7) [34,260,65,96,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35862

theorem m42536_10 : Upper (D 7) (R 7) [34,260,65,96,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35871

def r42536 : Route 9 := (fun mask => (mask,id))

def c42536 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42536 : Upper (D 7) (R 7) [34,260,65,96] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42536 c42536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42536_3
  · exact m42536_9
  · exact m42536_10
  · exact u35902
  · exact u35903
  · exact u35904

theorem m42537_10 : Upper (D 7) (R 7) [34,260,65,129,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35872

theorem m42537_34 : Upper (D 7) (R 7) [34,260,65,129,34] 13 :=
  permutation_upper _ _ _ [34,260,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35882

theorem m42537_40 : Upper (D 7) (R 7) [34,260,65,129,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35888

theorem m42537_66 : Upper (D 7) (R 7) [34,260,65,129,66] 13 :=
  permutation_upper _ _ _ [34,260,65,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35895

theorem m42537_72 : Upper (D 7) (R 7) [34,260,65,129,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35898

theorem m42537_96 : Upper (D 7) (R 7) [34,260,65,129,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35902

def r42537 : Route 9 := (fun mask => (mask,id))

def c42537 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42537 : Upper (D 7) (R 7) [34,260,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r42537 c42537
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42537_10
  · exact m42537_34
  · exact m42537_40
  · exact m42537_66
  · exact m42537_72
  · exact m42537_96
  · exact u35905
  · exact u35906
  · exact u35907
  · exact u35908

theorem m42538_9 : Upper (D 7) (R 7) [34,260,65,130,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35863

theorem m42538_33 : Upper (D 7) (R 7) [34,260,65,130,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35878

theorem m42538_40 : Upper (D 7) (R 7) [34,260,65,130,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35889

theorem m42538_65 : Upper (D 7) (R 7) [34,260,65,130,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35892

theorem m42538_72 : Upper (D 7) (R 7) [34,260,65,130,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35899

theorem m42538_96 : Upper (D 7) (R 7) [34,260,65,130,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35903

theorem m42538_129 : Upper (D 7) (R 7) [34,260,65,130,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35905

def r42538 : Route 9 := (fun mask => (mask,id))

def c42538 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42538 : Upper (D 7) (R 7) [34,260,65,130] 13 := by
  apply FastRouting.sound _ _ [34,260,65,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42538 c42538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42538_9
  · exact m42538_33
  · exact m42538_40
  · exact m42538_65
  · exact m42538_72
  · exact m42538_96
  · exact m42538_129
  · exact u35909
  · exact u35910
  · exact u35911

theorem m42539_3 : Upper (D 7) (R 7) [34,260,65,144,3] 13 :=
  permutation_upper _ _ _ [34,260,65,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35854

theorem m42539_9 : Upper (D 7) (R 7) [34,260,65,144,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35864

theorem m42539_10 : Upper (D 7) (R 7) [34,260,65,144,10] 13 :=
  permutation_upper _ _ _ [34,260,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35873

theorem m42539_33 : Upper (D 7) (R 7) [34,260,65,144,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35879

theorem m42539_34 : Upper (D 7) (R 7) [34,260,65,144,34] 13 :=
  permutation_upper _ _ _ [34,260,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35883

theorem m42539_40 : Upper (D 7) (R 7) [34,260,65,144,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35890

theorem m42539_65 : Upper (D 7) (R 7) [34,260,65,144,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35893

theorem m42539_66 : Upper (D 7) (R 7) [34,260,65,144,66] 13 :=
  permutation_upper _ _ _ [34,260,65,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35896

theorem m42539_72 : Upper (D 7) (R 7) [34,260,65,144,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35900

theorem m42539_96 : Upper (D 7) (R 7) [34,260,65,144,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35904

theorem m42539_129 : Upper (D 7) (R 7) [34,260,65,144,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35906

theorem m42539_130 : Upper (D 7) (R 7) [34,260,65,144,130] 13 :=
  permutation_upper _ _ _ [34,260,65,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35909

def r42539 : Route 9 := (fun mask => (mask,id))

def c42539 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42539 : Upper (D 7) (R 7) [34,260,65,144] 13 := by
  apply FastRouting.sound _ _ [34,260,65,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r42539 c42539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42539_3
  · exact m42539_9
  · exact m42539_10
  · exact m42539_33
  · exact m42539_34
  · exact m42539_40
  · exact m42539_65
  · exact m42539_66
  · exact m42539_72
  · exact m42539_96
  · exact m42539_129
  · exact m42539_130
  · exact u35912
  · exact u35913
  · exact u35914

#print axioms u42539
end Delivery.IrregularNine14.P07
