import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0216
import IrregularNine14P08C0218
import IrregularNine14P08C0219
import IrregularNine14P08C0221
import IrregularNine14P08C0223
import IrregularNine14P08C0224
import IrregularNine14P08C0225
import IrregularNine14P08C0226
import IrregularNine14P08C0227
import IrregularNine14P08C0228
import IrregularNine14P08C0233
import IrregularNine14P08C0234
import IrregularNine14P08C0235
import IrregularNine14P08C0236
import IrregularNine14P08C0237
import IrregularNine14P08C0239
import IrregularNine14P08C0240
import IrregularNine14P08C0242
import IrregularNine14P08C0244
import IrregularNine14P08C0245
import IrregularNine14P08C0246
import IrregularNine14P08C0247
import IrregularNine14P08C0248
import IrregularNine14P08C0249
import IrregularNine14P08C0250

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m21840_3 : Upper (D 8) (R 8) [96,80,160,260,3] 13 :=
  permutation_upper _ _ _ [96,5,66,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12993

theorem m21840_9 : Upper (D 8) (R 8) [96,80,160,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13570

theorem m21840_10 : Upper (D 8) (R 8) [96,80,160,260,10] 13 :=
  permutation_upper _ _ _ [96,12,66,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13998

theorem m21840_33 : Upper (D 8) (R 8) [96,80,160,260,33] 13 :=
  permutation_upper _ _ _ [96,33,66,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14377

theorem m21840_34 : Upper (D 8) (R 8) [96,80,160,260,34] 13 :=
  permutation_upper _ _ _ [96,36,66,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14550

theorem m21840_40 : Upper (D 8) (R 8) [96,80,160,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14882

theorem m21840_129 : Upper (D 8) (R 8) [96,80,160,260,129] 13 :=
  permutation_upper _ _ _ [96,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14946

theorem m21840_130 : Upper (D 8) (R 8) [96,80,160,260,130] 13 :=
  permutation_upper _ _ _ [96,68,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14955

theorem m21840_136 : Upper (D 8) (R 8) [96,80,160,260,136] 13 :=
  permutation_upper _ _ _ [96,68,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14975

theorem m21840_160 : Upper (D 8) (R 8) [96,80,160,260,160] 13 :=
  permutation_upper _ _ _ [96,68,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14992

def r21840 : Route 9 := (fun mask => (mask,id))

def c21840 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21840 : Upper (D 8) (R 8) [96,80,160,260] 13 := by
  apply FastRouting.sound _ _ [96,80,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21840 c21840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21840_3
  · exact m21840_9
  · exact m21840_10
  · exact m21840_33
  · exact m21840_34
  · exact m21840_40
  · exact m21840_129
  · exact m21840_130
  · exact m21840_136
  · exact m21840_160

theorem m21841_3 : Upper (D 8) (R 8) [96,80,160,288,3] 13 :=
  permutation_upper _ _ _ [96,5,66,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12994

theorem m21841_5 : Upper (D 8) (R 8) [96,80,160,288,5] 13 :=
  permutation_upper _ _ _ [96,5,160,66,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13383

theorem m21841_6 : Upper (D 8) (R 8) [96,80,160,288,6] 13 :=
  permutation_upper _ _ _ [96,12,66,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13993

theorem m21841_9 : Upper (D 8) (R 8) [96,80,160,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13611

theorem m21841_10 : Upper (D 8) (R 8) [96,80,160,288,10] 13 :=
  permutation_upper _ _ _ [96,12,66,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14000

theorem m21841_12 : Upper (D 8) (R 8) [96,80,160,288,12] 13 :=
  permutation_upper _ _ _ [96,12,160,288,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14236

theorem m21841_129 : Upper (D 8) (R 8) [96,80,160,288,129] 13 :=
  permutation_upper _ _ _ [96,68,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14947

theorem m21841_130 : Upper (D 8) (R 8) [96,80,160,288,130] 13 :=
  permutation_upper _ _ _ [96,68,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14956

theorem m21841_132 : Upper (D 8) (R 8) [96,80,160,288,132] 13 :=
  permutation_upper _ _ _ [96,68,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14967

theorem m21841_136 : Upper (D 8) (R 8) [96,80,160,288,136] 13 :=
  permutation_upper _ _ _ [96,68,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14978

def r21841 : Route 9 := (fun mask => (mask,id))

def c21841 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21841 : Upper (D 8) (R 8) [96,80,160,288] 13 := by
  apply FastRouting.sound _ _ [96,80,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r21841 c21841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21841_3
  · exact m21841_5
  · exact m21841_6
  · exact m21841_9
  · exact m21841_10
  · exact m21841_12
  · exact m21841_129
  · exact m21841_130
  · exact m21841_132
  · exact m21841_136

theorem m21842_3 : Upper (D 8) (R 8) [96,80,160,384,3] 13 :=
  permutation_upper _ _ _ [96,5,66,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12995

theorem m21842_5 : Upper (D 8) (R 8) [96,80,160,384,5] 13 :=
  permutation_upper _ _ _ [96,5,160,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13384

theorem m21842_6 : Upper (D 8) (R 8) [96,80,160,384,6] 13 :=
  permutation_upper _ _ _ [96,12,66,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13994

theorem m21842_9 : Upper (D 8) (R 8) [96,80,160,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13681

theorem m21842_10 : Upper (D 8) (R 8) [96,80,160,384,10] 13 :=
  permutation_upper _ _ _ [96,12,66,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14002

theorem m21842_12 : Upper (D 8) (R 8) [96,80,160,384,12] 13 :=
  permutation_upper _ _ _ [96,12,160,384,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14246

theorem m21842_33 : Upper (D 8) (R 8) [96,80,160,384,33] 13 :=
  permutation_upper _ _ _ [96,33,66,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14378

theorem m21842_34 : Upper (D 8) (R 8) [96,80,160,384,34] 13 :=
  permutation_upper _ _ _ [96,36,66,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14551

theorem m21842_36 : Upper (D 8) (R 8) [96,80,160,384,36] 13 :=
  permutation_upper _ _ _ [96,36,160,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14774

theorem m21842_40 : Upper (D 8) (R 8) [96,80,160,384,40] 13 :=
  permutation_upper _ _ _ [96,36,384,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14909

def r21842 : Route 9 := (fun mask => (mask,id))

def c21842 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21842 : Upper (D 8) (R 8) [96,80,160,384] 13 := by
  apply FastRouting.sound _ _ [96,80,160,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21842 c21842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21842_3
  · exact m21842_5
  · exact m21842_6
  · exact m21842_9
  · exact m21842_10
  · exact m21842_12
  · exact m21842_33
  · exact m21842_34
  · exact m21842_36
  · exact m21842_40

def b21843 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 317 317 381 445 317), lower := (rows 97 98 133 138 16 32 64 128 256), losses := [] }

theorem u21843 : Upper (D 8) (R 8) [96,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21844 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 168 287 319 351 415 287), lower := (rows 97 98 133 168 16 32 64 128 256), losses := [] }

theorem u21844 : Upper (D 8) (R 8) [96,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21845 : PairBound 9 := { available := 190, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 265 190 190 254 190 446), lower := (rows 97 98 133 265 16 32 64 128 256), losses := [] }

theorem u21845 : Upper (D 8) (R 8) [96,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21846 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 266 189 189 253 189 445), lower := (rows 97 98 133 266 16 32 64 128 256), losses := [] }

theorem u21846 : Upper (D 8) (R 8) [96,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21847 : PairBound 9 := { available := 187, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 268 187 187 251 187 443), lower := (rows 97 98 133 268 16 32 64 128 256), losses := [] }

theorem u21847 : Upper (D 8) (R 8) [96,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21848 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 296 159 191 223 159 415), lower := (rows 97 98 133 296 16 32 64 128 256), losses := [] }

theorem u21848 : Upper (D 8) (R 8) [96,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21849 : PairBound 9 := { available := 63, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 392 63 63 127 191 319), lower := (rows 97 98 133 392 16 32 64 128 256), losses := [] }

theorem u21849 : Upper (D 8) (R 8) [96,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21850 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 168 285 317 349 413 285), lower := (rows 97 98 134 168 16 32 64 128 256), losses := [] }

theorem u21850 : Upper (D 8) (R 8) [96,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21851 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 265 189 189 253 189 445), lower := (rows 97 98 134 265 16 32 64 128 256), losses := [] }

theorem u21851 : Upper (D 8) (R 8) [96,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21852 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 268 185 185 249 185 441), lower := (rows 97 98 134 268 16 32 64 128 256), losses := [] }

theorem u21852 : Upper (D 8) (R 8) [96,96,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21853 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 296 157 189 221 157 413), lower := (rows 97 98 134 296 16 32 64 128 256), losses := [] }

theorem u21853 : Upper (D 8) (R 8) [96,96,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21854 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 392 61 61 125 189 317), lower := (rows 97 98 134 392 16 32 64 128 256), losses := [] }

theorem u21854 : Upper (D 8) (R 8) [96,96,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21855 : PairBound 9 := { available := 183, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 265 183 183 247 183 439), lower := (rows 97 98 140 265 16 32 64 128 256), losses := [] }

theorem u21855 : Upper (D 8) (R 8) [96,96,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21856 : PairBound 9 := { available := 181, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 266 181 181 245 181 437), lower := (rows 97 98 140 266 16 32 64 128 256), losses := [] }

theorem u21856 : Upper (D 8) (R 8) [96,96,136,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21857 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 268 179 179 243 179 435), lower := (rows 97 98 140 268 16 32 64 128 256), losses := [] }

theorem u21857 : Upper (D 8) (R 8) [96,96,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21858 : PairBound 9 := { available := 151, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 296 151 183 215 151 407), lower := (rows 97 98 140 296 16 32 64 128 256), losses := [] }

theorem u21858 : Upper (D 8) (R 8) [96,96,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21859 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 164 265 159 191 223 159 415), lower := (rows 97 98 164 265 16 32 64 128 256), losses := [] }

theorem u21859 : Upper (D 8) (R 8) [96,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21860 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 164 266 157 189 221 157 413), lower := (rows 97 98 164 266 16 32 64 128 256), losses := [] }

theorem u21860 : Upper (D 8) (R 8) [96,96,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21861 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 164 268 155 187 219 155 411), lower := (rows 97 98 164 268 16 32 64 128 256), losses := [] }

theorem u21861 : Upper (D 8) (R 8) [96,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21862 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 164 392 31 63 95 159 287), lower := (rows 97 98 164 392 16 32 64 128 256), losses := [] }

theorem u21862 : Upper (D 8) (R 8) [96,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21863 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 97 131 133 266 124 124 124 252 380), lower := (rows 97 131 133 266 16 32 64 128 256), losses := [] }

theorem u21863 : Upper (D 8) (R 8) [96,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21864 : PairBound 9 := { available := 126, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 97 131 133 296 126 126 126 254 382), lower := (rows 97 131 133 296 16 32 64 128 256), losses := [] }

theorem u21864 : Upper (D 8) (R 8) [96,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21865 : PairBound 9 := { available := 62, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 97 131 133 328 62 62 126 190 318), lower := (rows 97 131 133 328 16 32 64 128 256), losses := [] }

theorem u21865 : Upper (D 8) (R 8) [96,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21866 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 265 124 124 124 252 380), lower := (rows 97 131 134 265 16 32 64 128 256), losses := [] }

theorem u21866 : Upper (D 8) (R 8) [96,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21867 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 268 121 121 121 249 377), lower := (rows 97 131 134 268 16 32 64 128 256), losses := [] }

theorem u21867 : Upper (D 8) (R 8) [96,129,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21868 : PairBound 9 := { available := 125, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 296 125 125 125 253 381), lower := (rows 97 131 134 296 16 32 64 128 256), losses := [] }

theorem u21868 : Upper (D 8) (R 8) [96,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21869 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 328 61 61 125 189 317), lower := (rows 97 131 134 328 16 32 64 128 256), losses := [] }

theorem u21869 : Upper (D 8) (R 8) [96,129,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21870_6 : Upper (D 8) (R 8) [96,129,136,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14084

theorem m21870_34 : Upper (D 8) (R 8) [96,129,136,257,34] 13 :=
  permutation_upper _ _ _ [96,36,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14649

theorem m21870_36 : Upper (D 8) (R 8) [96,129,136,257,36] 13 :=
  permutation_upper _ _ _ [96,36,136,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14745

theorem m21870_66 : Upper (D 8) (R 8) [96,129,136,257,66] 13 :=
  permutation_upper _ _ _ [96,68,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14940

theorem m21870_68 : Upper (D 8) (R 8) [96,129,136,257,68] 13 :=
  permutation_upper _ _ _ [96,68,136,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14968

theorem m21870_96 : Upper (D 8) (R 8) [96,129,136,257,96] 13 :=
  permutation_upper _ _ _ [96,96,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15025

def r21870 : Route 9 := (fun mask => (mask,id))

def c21870 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21870 : Upper (D 8) (R 8) [96,129,136,257] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r21870 c21870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21870_6
  · exact m21870_34
  · exact m21870_36
  · exact m21870_66
  · exact m21870_68
  · exact m21870_96

def b21871 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 131 140 266 117 117 117 245 373), lower := (rows 97 131 140 266 16 32 64 128 256), losses := [] }

theorem u21871 : Upper (D 8) (R 8) [96,129,136,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21872 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 131 140 268 115 115 115 243 371), lower := (rows 97 131 140 268 16 32 64 128 256), losses := [] }

theorem u21872 : Upper (D 8) (R 8) [96,129,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21873_3 : Upper (D 8) (R 8) [96,129,136,272,3] 13 :=
  permutation_upper _ _ _ [96,5,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13132

theorem m21873_5 : Upper (D 8) (R 8) [96,129,136,272,5] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13296

theorem m21873_6 : Upper (D 8) (R 8) [96,129,136,272,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14085

theorem m21873_33 : Upper (D 8) (R 8) [96,129,136,272,33] 13 :=
  permutation_upper _ _ _ [96,33,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14419

theorem m21873_34 : Upper (D 8) (R 8) [96,129,136,272,34] 13 :=
  permutation_upper _ _ _ [96,36,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14650

theorem m21873_36 : Upper (D 8) (R 8) [96,129,136,272,36] 13 :=
  permutation_upper _ _ _ [96,36,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14751

theorem m21873_65 : Upper (D 8) (R 8) [96,129,136,272,65] 13 :=
  permutation_upper _ _ _ [96,65,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14919

theorem m21873_66 : Upper (D 8) (R 8) [96,129,136,272,66] 13 :=
  permutation_upper _ _ _ [96,68,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14941

theorem m21873_68 : Upper (D 8) (R 8) [96,129,136,272,68] 13 :=
  permutation_upper _ _ _ [96,68,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14971

theorem m21873_96 : Upper (D 8) (R 8) [96,129,136,272,96] 13 :=
  permutation_upper _ _ _ [96,96,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15026

def r21873 : Route 9 := (fun mask => (mask,id))

def c21873 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21873 : Upper (D 8) (R 8) [96,129,136,272] 13 := by
  apply FastRouting.sound _ _ [96,129,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r21873 c21873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21873_3
  · exact m21873_5
  · exact m21873_6
  · exact m21873_33
  · exact m21873_34
  · exact m21873_36
  · exact m21873_65
  · exact m21873_66
  · exact m21873_68
  · exact m21873_96

theorem m21874_3 : Upper (D 8) (R 8) [96,129,136,288,3] 13 :=
  permutation_upper _ _ _ [96,5,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13134

theorem m21874_5 : Upper (D 8) (R 8) [96,129,136,288,5] 13 :=
  permutation_upper _ _ _ [96,5,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13313

theorem m21874_6 : Upper (D 8) (R 8) [96,129,136,288,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14086

theorem m21874_33 : Upper (D 8) (R 8) [96,129,136,288,33] 13 :=
  permutation_upper _ _ _ [96,33,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14420

theorem m21874_34 : Upper (D 8) (R 8) [96,129,136,288,34] 13 :=
  permutation_upper _ _ _ [96,36,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14652

theorem m21874_36 : Upper (D 8) (R 8) [96,129,136,288,36] 13 :=
  permutation_upper _ _ _ [96,36,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14763

theorem m21874_65 : Upper (D 8) (R 8) [96,129,136,288,65] 13 :=
  permutation_upper _ _ _ [96,65,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14920

theorem m21874_66 : Upper (D 8) (R 8) [96,129,136,288,66] 13 :=
  permutation_upper _ _ _ [96,68,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14943

theorem m21874_68 : Upper (D 8) (R 8) [96,129,136,288,68] 13 :=
  permutation_upper _ _ _ [96,68,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14976

theorem m21874_96 : Upper (D 8) (R 8) [96,129,136,288,96] 13 :=
  permutation_upper _ _ _ [96,96,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15027

def r21874 : Route 9 := (fun mask => (mask,id))

def c21874 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21874 : Upper (D 8) (R 8) [96,129,136,288] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r21874 c21874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21874_3
  · exact m21874_5
  · exact m21874_6
  · exact m21874_33
  · exact m21874_34
  · exact m21874_36
  · exact m21874_65
  · exact m21874_66
  · exact m21874_68
  · exact m21874_96

theorem m21875_3 : Upper (D 8) (R 8) [96,129,136,320,3] 13 :=
  permutation_upper _ _ _ [96,5,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13135

theorem m21875_5 : Upper (D 8) (R 8) [96,129,136,320,5] 13 :=
  permutation_upper _ _ _ [96,5,136,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13318

theorem m21875_6 : Upper (D 8) (R 8) [96,129,136,320,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14087

theorem m21875_33 : Upper (D 8) (R 8) [96,129,136,320,33] 13 :=
  permutation_upper _ _ _ [96,33,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14421

theorem m21875_34 : Upper (D 8) (R 8) [96,129,136,320,34] 13 :=
  permutation_upper _ _ _ [96,36,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14653

theorem m21875_36 : Upper (D 8) (R 8) [96,129,136,320,36] 13 :=
  permutation_upper _ _ _ [96,36,136,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14766

def r21875 : Route 9 := (fun mask => (mask,id))

def c21875 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21875 : Upper (D 8) (R 8) [96,129,136,320] 13 := by
  apply FastRouting.sound _ _ [96,129,136,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r21875 c21875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21875_3
  · exact m21875_5
  · exact m21875_6
  · exact m21875_33
  · exact m21875_34
  · exact m21875_36

theorem m21876_6 : Upper (D 8) (R 8) [96,129,144,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14079

theorem m21876_10 : Upper (D 8) (R 8) [96,129,144,257,10] 13 :=
  permutation_upper _ _ _ [96,12,129,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14100

theorem m21876_12 : Upper (D 8) (R 8) [96,129,144,257,12] 13 :=
  permutation_upper _ _ _ [96,12,130,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14145

theorem m21876_34 : Upper (D 8) (R 8) [96,129,144,257,34] 13 :=
  permutation_upper _ _ _ [96,36,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14645

theorem m21876_36 : Upper (D 8) (R 8) [96,129,144,257,36] 13 :=
  permutation_upper _ _ _ [96,36,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14680

theorem m21876_40 : Upper (D 8) (R 8) [96,129,144,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14825

theorem m21876_66 : Upper (D 8) (R 8) [96,129,144,257,66] 13 :=
  permutation_upper _ _ _ [96,68,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14937

theorem m21876_68 : Upper (D 8) (R 8) [96,129,144,257,68] 13 :=
  permutation_upper _ _ _ [96,68,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14948

theorem m21876_72 : Upper (D 8) (R 8) [96,129,144,257,72] 13 :=
  permutation_upper _ _ _ [96,68,257,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14993

theorem m21876_96 : Upper (D 8) (R 8) [96,129,144,257,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15021

def r21876 : Route 9 := (fun mask => (mask,id))

def c21876 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21876 : Upper (D 8) (R 8) [96,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,129,144,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r21876 c21876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21876_6
  · exact m21876_10
  · exact m21876_12
  · exact m21876_34
  · exact m21876_36
  · exact m21876_40
  · exact m21876_66
  · exact m21876_68
  · exact m21876_72
  · exact m21876_96

theorem m21877_5 : Upper (D 8) (R 8) [96,129,144,258,5] 13 :=
  permutation_upper _ _ _ [96,5,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13177

theorem m21877_9 : Upper (D 8) (R 8) [96,129,144,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13549

theorem m21877_12 : Upper (D 8) (R 8) [96,129,144,258,12] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14151

theorem m21877_33 : Upper (D 8) (R 8) [96,129,144,258,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14415

theorem m21877_36 : Upper (D 8) (R 8) [96,129,144,258,36] 13 :=
  permutation_upper _ _ _ [96,36,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14681

theorem m21877_40 : Upper (D 8) (R 8) [96,129,144,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14866

theorem m21877_65 : Upper (D 8) (R 8) [96,129,144,258,65] 13 :=
  permutation_upper _ _ _ [96,65,129,130,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14916

theorem m21877_68 : Upper (D 8) (R 8) [96,129,144,258,68] 13 :=
  permutation_upper _ _ _ [96,68,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14949

theorem m21877_72 : Upper (D 8) (R 8) [96,129,144,258,72] 13 :=
  permutation_upper _ _ _ [96,68,264,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15003

theorem m21877_96 : Upper (D 8) (R 8) [96,129,144,258,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15022

def r21877 : Route 9 := (fun mask => (mask,id))

def c21877 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21877 : Upper (D 8) (R 8) [96,129,144,258] 13 := by
  apply FastRouting.sound _ _ [96,129,144,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r21877 c21877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21877_5
  · exact m21877_9
  · exact m21877_12
  · exact m21877_33
  · exact m21877_36
  · exact m21877_40
  · exact m21877_65
  · exact m21877_68
  · exact m21877_72
  · exact m21877_96

theorem m21878_3 : Upper (D 8) (R 8) [96,129,144,260,3] 13 :=
  permutation_upper _ _ _ [96,5,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13129

theorem m21878_9 : Upper (D 8) (R 8) [96,129,144,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13555

theorem m21878_10 : Upper (D 8) (R 8) [96,129,144,260,10] 13 :=
  permutation_upper _ _ _ [96,12,129,272,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14115

theorem m21878_33 : Upper (D 8) (R 8) [96,129,144,260,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14416

theorem m21878_34 : Upper (D 8) (R 8) [96,129,144,260,34] 13 :=
  permutation_upper _ _ _ [96,36,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14646

theorem m21878_40 : Upper (D 8) (R 8) [96,129,144,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14871

theorem m21878_65 : Upper (D 8) (R 8) [96,129,144,260,65] 13 :=
  permutation_upper _ _ _ [96,65,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14917

theorem m21878_66 : Upper (D 8) (R 8) [96,129,144,260,66] 13 :=
  permutation_upper _ _ _ [96,68,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14938

theorem m21878_72 : Upper (D 8) (R 8) [96,129,144,260,72] 13 :=
  permutation_upper _ _ _ [96,68,264,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15005

theorem m21878_96 : Upper (D 8) (R 8) [96,129,144,260,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15023

def r21878 : Route 9 := (fun mask => (mask,id))

def c21878 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21878 : Upper (D 8) (R 8) [96,129,144,260] 13 := by
  apply FastRouting.sound _ _ [96,129,144,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21878 c21878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21878_3
  · exact m21878_9
  · exact m21878_10
  · exact m21878_33
  · exact m21878_34
  · exact m21878_40
  · exact m21878_65
  · exact m21878_66
  · exact m21878_72
  · exact m21878_96

theorem m21879_3 : Upper (D 8) (R 8) [96,129,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13130

theorem m21879_5 : Upper (D 8) (R 8) [96,129,144,288,5] 13 :=
  permutation_upper _ _ _ [96,5,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13178

theorem m21879_6 : Upper (D 8) (R 8) [96,129,144,288,6] 13 :=
  permutation_upper _ _ _ [96,12,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14080

theorem m21879_9 : Upper (D 8) (R 8) [96,129,144,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13619

theorem m21879_10 : Upper (D 8) (R 8) [96,129,144,288,10] 13 :=
  permutation_upper _ _ _ [96,12,129,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14124

theorem m21879_12 : Upper (D 8) (R 8) [96,129,144,288,12] 13 :=
  permutation_upper _ _ _ [96,12,130,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14157

theorem m21879_33 : Upper (D 8) (R 8) [96,129,144,288,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14417

theorem m21879_34 : Upper (D 8) (R 8) [96,129,144,288,34] 13 :=
  permutation_upper _ _ _ [96,36,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14647

theorem m21879_36 : Upper (D 8) (R 8) [96,129,144,288,36] 13 :=
  permutation_upper _ _ _ [96,36,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14682

theorem m21879_40 : Upper (D 8) (R 8) [96,129,144,288,40] 13 :=
  permutation_upper _ _ _ [96,36,288,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14893

theorem m21879_65 : Upper (D 8) (R 8) [96,129,144,288,65] 13 :=
  permutation_upper _ _ _ [96,65,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14918

theorem m21879_66 : Upper (D 8) (R 8) [96,129,144,288,66] 13 :=
  permutation_upper _ _ _ [96,68,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14939

theorem m21879_68 : Upper (D 8) (R 8) [96,129,144,288,68] 13 :=
  permutation_upper _ _ _ [96,68,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14950

theorem m21879_72 : Upper (D 8) (R 8) [96,129,144,288,72] 13 :=
  permutation_upper _ _ _ [96,68,288,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15014

theorem m21879_96 : Upper (D 8) (R 8) [96,129,144,288,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15024

def r21879 : Route 9 := (fun mask => (mask,id))

def c21879 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21879 : Upper (D 8) (R 8) [96,129,144,288] 13 := by
  apply FastRouting.sound _ _ [96,129,144,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r21879 c21879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21879_3
  · exact m21879_5
  · exact m21879_6
  · exact m21879_9
  · exact m21879_10
  · exact m21879_12
  · exact m21879_33
  · exact m21879_34
  · exact m21879_36
  · exact m21879_40
  · exact m21879_65
  · exact m21879_66
  · exact m21879_68
  · exact m21879_72
  · exact m21879_96

theorem m21880_3 : Upper (D 8) (R 8) [96,129,144,320,3] 13 :=
  permutation_upper _ _ _ [96,5,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13131

theorem m21880_5 : Upper (D 8) (R 8) [96,129,144,320,5] 13 :=
  permutation_upper _ _ _ [96,5,130,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13179

theorem m21880_6 : Upper (D 8) (R 8) [96,129,144,320,6] 13 :=
  permutation_upper _ _ _ [96,12,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14081

theorem m21880_9 : Upper (D 8) (R 8) [96,129,144,320,9] 13 :=
  permutation_upper _ _ _ [96,5,320,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13640

theorem m21880_10 : Upper (D 8) (R 8) [96,129,144,320,10] 13 :=
  permutation_upper _ _ _ [96,12,129,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14130

theorem m21880_12 : Upper (D 8) (R 8) [96,129,144,320,12] 13 :=
  permutation_upper _ _ _ [96,12,130,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14160

theorem m21880_33 : Upper (D 8) (R 8) [96,129,144,320,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14418

theorem m21880_34 : Upper (D 8) (R 8) [96,129,144,320,34] 13 :=
  permutation_upper _ _ _ [96,36,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14648

theorem m21880_36 : Upper (D 8) (R 8) [96,129,144,320,36] 13 :=
  permutation_upper _ _ _ [96,36,130,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14683

theorem m21880_40 : Upper (D 8) (R 8) [96,129,144,320,40] 13 :=
  permutation_upper _ _ _ [96,36,320,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14897

def r21880 : Route 9 := (fun mask => (mask,id))

def c21880 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21880 : Upper (D 8) (R 8) [96,129,144,320] 13 := by
  apply FastRouting.sound _ _ [96,129,144,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21880 c21880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21880_3
  · exact m21880_5
  · exact m21880_6
  · exact m21880_9
  · exact m21880_10
  · exact m21880_12
  · exact m21880_33
  · exact m21880_34
  · exact m21880_36
  · exact m21880_40

theorem m21881_6 : Upper (D 8) (R 8) [96,129,160,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14090

theorem m21881_10 : Upper (D 8) (R 8) [96,129,160,257,10] 13 :=
  permutation_upper _ _ _ [96,12,129,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14101

theorem m21881_12 : Upper (D 8) (R 8) [96,129,160,257,12] 13 :=
  permutation_upper _ _ _ [96,12,160,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14216

theorem m21881_34 : Upper (D 8) (R 8) [96,129,160,257,34] 13 :=
  permutation_upper _ _ _ [96,36,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14654

theorem m21881_36 : Upper (D 8) (R 8) [96,129,160,257,36] 13 :=
  permutation_upper _ _ _ [96,36,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14780

theorem m21881_40 : Upper (D 8) (R 8) [96,129,160,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14827

theorem m21881_66 : Upper (D 8) (R 8) [96,129,160,257,66] 13 :=
  permutation_upper _ _ _ [96,68,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14944

theorem m21881_68 : Upper (D 8) (R 8) [96,129,160,257,68] 13 :=
  permutation_upper _ _ _ [96,68,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14979

theorem m21881_72 : Upper (D 8) (R 8) [96,129,160,257,72] 13 :=
  permutation_upper _ _ _ [96,68,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14995

theorem m21881_96 : Upper (D 8) (R 8) [96,129,160,257,96] 13 :=
  permutation_upper _ _ _ [96,96,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15028

def r21881 : Route 9 := (fun mask => (mask,id))

def c21881 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21881 : Upper (D 8) (R 8) [96,129,160,257] 13 := by
  apply FastRouting.sound _ _ [96,129,160,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r21881 c21881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21881_6
  · exact m21881_10
  · exact m21881_12
  · exact m21881_34
  · exact m21881_36
  · exact m21881_40
  · exact m21881_66
  · exact m21881_68
  · exact m21881_72
  · exact m21881_96

theorem m21882_5 : Upper (D 8) (R 8) [96,129,160,258,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13401

theorem m21882_9 : Upper (D 8) (R 8) [96,129,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13550

theorem m21882_12 : Upper (D 8) (R 8) [96,129,160,258,12] 13 :=
  permutation_upper _ _ _ [96,12,160,272,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14231

theorem m21882_33 : Upper (D 8) (R 8) [96,129,160,258,33] 13 :=
  permutation_upper _ _ _ [96,33,129,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14423

theorem m21882_36 : Upper (D 8) (R 8) [96,129,160,258,36] 13 :=
  permutation_upper _ _ _ [96,36,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14782

theorem m21882_40 : Upper (D 8) (R 8) [96,129,160,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14867

theorem m21882_65 : Upper (D 8) (R 8) [96,129,160,258,65] 13 :=
  permutation_upper _ _ _ [96,65,129,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14922

theorem m21882_68 : Upper (D 8) (R 8) [96,129,160,258,68] 13 :=
  permutation_upper _ _ _ [96,68,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14981

theorem m21882_72 : Upper (D 8) (R 8) [96,129,160,258,72] 13 :=
  permutation_upper _ _ _ [96,68,264,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15004

theorem m21882_96 : Upper (D 8) (R 8) [96,129,160,258,96] 13 :=
  permutation_upper _ _ _ [96,96,129,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15030

def r21882 : Route 9 := (fun mask => (mask,id))

def c21882 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21882 : Upper (D 8) (R 8) [96,129,160,258] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r21882 c21882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21882_5
  · exact m21882_9
  · exact m21882_12
  · exact m21882_33
  · exact m21882_36
  · exact m21882_40
  · exact m21882_65
  · exact m21882_68
  · exact m21882_72
  · exact m21882_96

theorem m21883_3 : Upper (D 8) (R 8) [96,129,160,260,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13137

theorem m21883_9 : Upper (D 8) (R 8) [96,129,160,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13572

theorem m21883_10 : Upper (D 8) (R 8) [96,129,160,260,10] 13 :=
  permutation_upper _ _ _ [96,12,129,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14116

theorem m21883_33 : Upper (D 8) (R 8) [96,129,160,260,33] 13 :=
  permutation_upper _ _ _ [96,33,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14424

theorem m21883_34 : Upper (D 8) (R 8) [96,129,160,260,34] 13 :=
  permutation_upper _ _ _ [96,36,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14656

theorem m21883_40 : Upper (D 8) (R 8) [96,129,160,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14883

theorem m21883_65 : Upper (D 8) (R 8) [96,129,160,260,65] 13 :=
  permutation_upper _ _ _ [96,65,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14923

theorem m21883_66 : Upper (D 8) (R 8) [96,129,160,260,66] 13 :=
  permutation_upper _ _ _ [96,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14946

theorem m21883_72 : Upper (D 8) (R 8) [96,129,160,260,72] 13 :=
  permutation_upper _ _ _ [96,68,264,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15010

theorem m21883_96 : Upper (D 8) (R 8) [96,129,160,260,96] 13 :=
  permutation_upper _ _ _ [96,96,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15031

def r21883 : Route 9 := (fun mask => (mask,id))

def c21883 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21883 : Upper (D 8) (R 8) [96,129,160,260] 13 := by
  apply FastRouting.sound _ _ [96,129,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21883 c21883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21883_3
  · exact m21883_9
  · exact m21883_10
  · exact m21883_33
  · exact m21883_34
  · exact m21883_40
  · exact m21883_65
  · exact m21883_66
  · exact m21883_72
  · exact m21883_96

theorem m21884_3 : Upper (D 8) (R 8) [96,129,160,272,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13136

theorem m21884_5 : Upper (D 8) (R 8) [96,129,160,272,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13400

theorem m21884_6 : Upper (D 8) (R 8) [96,129,160,272,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14091

theorem m21884_9 : Upper (D 8) (R 8) [96,129,160,272,9] 13 :=
  permutation_upper _ _ _ [96,5,258,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13501

theorem m21884_10 : Upper (D 8) (R 8) [96,129,160,272,10] 13 :=
  permutation_upper _ _ _ [96,12,129,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14107

theorem m21884_12 : Upper (D 8) (R 8) [96,129,160,272,12] 13 :=
  permutation_upper _ _ _ [96,12,160,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14223

theorem m21884_33 : Upper (D 8) (R 8) [96,129,160,272,33] 13 :=
  permutation_upper _ _ _ [96,33,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14422

theorem m21884_34 : Upper (D 8) (R 8) [96,129,160,272,34] 13 :=
  permutation_upper _ _ _ [96,36,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14655

theorem m21884_36 : Upper (D 8) (R 8) [96,129,160,272,36] 13 :=
  permutation_upper _ _ _ [96,36,160,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14781

theorem m21884_40 : Upper (D 8) (R 8) [96,129,160,272,40] 13 :=
  permutation_upper _ _ _ [96,36,258,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14846

theorem m21884_65 : Upper (D 8) (R 8) [96,129,160,272,65] 13 :=
  permutation_upper _ _ _ [96,65,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14921

theorem m21884_66 : Upper (D 8) (R 8) [96,129,160,272,66] 13 :=
  permutation_upper _ _ _ [96,68,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14945

theorem m21884_68 : Upper (D 8) (R 8) [96,129,160,272,68] 13 :=
  permutation_upper _ _ _ [96,68,160,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14980

theorem m21884_72 : Upper (D 8) (R 8) [96,129,160,272,72] 13 :=
  permutation_upper _ _ _ [96,68,258,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15001

theorem m21884_96 : Upper (D 8) (R 8) [96,129,160,272,96] 13 :=
  permutation_upper _ _ _ [96,96,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15029

def r21884 : Route 9 := (fun mask => (mask,id))

def c21884 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21884 : Upper (D 8) (R 8) [96,129,160,272] 13 := by
  apply FastRouting.sound _ _ [96,129,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r21884 c21884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21884_3
  · exact m21884_5
  · exact m21884_6
  · exact m21884_9
  · exact m21884_10
  · exact m21884_12
  · exact m21884_33
  · exact m21884_34
  · exact m21884_36
  · exact m21884_40
  · exact m21884_65
  · exact m21884_66
  · exact m21884_68
  · exact m21884_72
  · exact m21884_96

theorem m21885_3 : Upper (D 8) (R 8) [96,129,160,288,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13138

theorem m21885_5 : Upper (D 8) (R 8) [96,129,160,288,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13402

theorem m21885_6 : Upper (D 8) (R 8) [96,129,160,288,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14092

theorem m21885_9 : Upper (D 8) (R 8) [96,129,160,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13621

theorem m21885_10 : Upper (D 8) (R 8) [96,129,160,288,10] 13 :=
  permutation_upper _ _ _ [96,12,129,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14125

theorem m21885_12 : Upper (D 8) (R 8) [96,129,160,288,12] 13 :=
  permutation_upper _ _ _ [96,12,160,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14237

theorem m21885_65 : Upper (D 8) (R 8) [96,129,160,288,65] 13 :=
  permutation_upper _ _ _ [96,65,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14924

theorem m21885_66 : Upper (D 8) (R 8) [96,129,160,288,66] 13 :=
  permutation_upper _ _ _ [96,68,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14947

theorem m21885_68 : Upper (D 8) (R 8) [96,129,160,288,68] 13 :=
  permutation_upper _ _ _ [96,68,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14982

theorem m21885_72 : Upper (D 8) (R 8) [96,129,160,288,72] 13 :=
  permutation_upper _ _ _ [96,68,288,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15016

def r21885 : Route 9 := (fun mask => (mask,id))

def c21885 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21885 : Upper (D 8) (R 8) [96,129,160,288] 13 := by
  apply FastRouting.sound _ _ [96,129,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r21885 c21885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21885_3
  · exact m21885_5
  · exact m21885_6
  · exact m21885_9
  · exact m21885_10
  · exact m21885_12
  · exact m21885_65
  · exact m21885_66
  · exact m21885_68
  · exact m21885_72

theorem m21886_3 : Upper (D 8) (R 8) [96,129,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13139

theorem m21886_5 : Upper (D 8) (R 8) [96,129,160,320,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13403

theorem m21886_6 : Upper (D 8) (R 8) [96,129,160,320,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14093

theorem m21886_9 : Upper (D 8) (R 8) [96,129,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13641

theorem m21886_10 : Upper (D 8) (R 8) [96,129,160,320,10] 13 :=
  permutation_upper _ _ _ [96,12,129,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14131

theorem m21886_12 : Upper (D 8) (R 8) [96,129,160,320,12] 13 :=
  permutation_upper _ _ _ [96,12,160,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14242

theorem m21886_33 : Upper (D 8) (R 8) [96,129,160,320,33] 13 :=
  permutation_upper _ _ _ [96,33,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14425

theorem m21886_34 : Upper (D 8) (R 8) [96,129,160,320,34] 13 :=
  permutation_upper _ _ _ [96,36,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14657

theorem m21886_36 : Upper (D 8) (R 8) [96,129,160,320,36] 13 :=
  permutation_upper _ _ _ [96,36,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14783

theorem m21886_40 : Upper (D 8) (R 8) [96,129,160,320,40] 13 :=
  permutation_upper _ _ _ [96,36,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14899

def r21886 : Route 9 := (fun mask => (mask,id))

def c21886 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21886 : Upper (D 8) (R 8) [96,129,160,320] 13 := by
  apply FastRouting.sound _ _ [96,129,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21886 c21886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21886_3
  · exact m21886_5
  · exact m21886_6
  · exact m21886_9
  · exact m21886_10
  · exact m21886_12
  · exact m21886_33
  · exact m21886_34
  · exact m21886_36
  · exact m21886_40

theorem m21887_6 : Upper (D 8) (R 8) [96,129,192,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14095

theorem m21887_10 : Upper (D 8) (R 8) [96,129,192,257,10] 13 :=
  permutation_upper _ _ _ [96,12,129,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14102

theorem m21887_12 : Upper (D 8) (R 8) [96,129,192,257,12] 13 :=
  permutation_upper _ _ _ [96,12,192,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14249

theorem m21887_34 : Upper (D 8) (R 8) [96,129,192,257,34] 13 :=
  permutation_upper _ _ _ [96,36,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14658

theorem m21887_36 : Upper (D 8) (R 8) [96,129,192,257,36] 13 :=
  permutation_upper _ _ _ [96,36,192,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14798

theorem m21887_40 : Upper (D 8) (R 8) [96,129,192,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14828

def r21887 : Route 9 := (fun mask => (mask,id))

def c21887 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21887 : Upper (D 8) (R 8) [96,129,192,257] 13 := by
  apply FastRouting.sound _ _ [96,129,192,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r21887 c21887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21887_6
  · exact m21887_10
  · exact m21887_12
  · exact m21887_34
  · exact m21887_36
  · exact m21887_40

theorem m21888_5 : Upper (D 8) (R 8) [96,129,192,258,5] 13 :=
  permutation_upper _ _ _ [96,5,192,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13448

theorem m21888_9 : Upper (D 8) (R 8) [96,129,192,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13551

theorem m21888_12 : Upper (D 8) (R 8) [96,129,192,258,12] 13 :=
  permutation_upper _ _ _ [96,12,192,272,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14256

theorem m21888_33 : Upper (D 8) (R 8) [96,129,192,258,33] 13 :=
  permutation_upper _ _ _ [96,33,129,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14427

theorem m21888_36 : Upper (D 8) (R 8) [96,129,192,258,36] 13 :=
  permutation_upper _ _ _ [96,36,192,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14800

theorem m21888_40 : Upper (D 8) (R 8) [96,129,192,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14868

def r21888 : Route 9 := (fun mask => (mask,id))

def c21888 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21888 : Upper (D 8) (R 8) [96,129,192,258] 13 := by
  apply FastRouting.sound _ _ [96,129,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r21888 c21888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21888_5
  · exact m21888_9
  · exact m21888_12
  · exact m21888_33
  · exact m21888_36
  · exact m21888_40

theorem m21889_3 : Upper (D 8) (R 8) [96,129,192,260,3] 13 :=
  permutation_upper _ _ _ [96,5,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13141

theorem m21889_9 : Upper (D 8) (R 8) [96,129,192,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13577

theorem m21889_10 : Upper (D 8) (R 8) [96,129,192,260,10] 13 :=
  permutation_upper _ _ _ [96,12,129,272,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14117

theorem m21889_33 : Upper (D 8) (R 8) [96,129,192,260,33] 13 :=
  permutation_upper _ _ _ [96,33,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14428

theorem m21889_34 : Upper (D 8) (R 8) [96,129,192,260,34] 13 :=
  permutation_upper _ _ _ [96,36,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14660

theorem m21889_40 : Upper (D 8) (R 8) [96,129,192,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14886

def r21889 : Route 9 := (fun mask => (mask,id))

def c21889 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21889 : Upper (D 8) (R 8) [96,129,192,260] 13 := by
  apply FastRouting.sound _ _ [96,129,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21889 c21889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21889_3
  · exact m21889_9
  · exact m21889_10
  · exact m21889_33
  · exact m21889_34
  · exact m21889_40

theorem m21890_3 : Upper (D 8) (R 8) [96,129,192,272,3] 13 :=
  permutation_upper _ _ _ [96,5,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13140

theorem m21890_5 : Upper (D 8) (R 8) [96,129,192,272,5] 13 :=
  permutation_upper _ _ _ [96,5,192,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13447

theorem m21890_6 : Upper (D 8) (R 8) [96,129,192,272,6] 13 :=
  permutation_upper _ _ _ [96,12,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14096

theorem m21890_9 : Upper (D 8) (R 8) [96,129,192,272,9] 13 :=
  permutation_upper _ _ _ [96,5,258,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13502

theorem m21890_10 : Upper (D 8) (R 8) [96,129,192,272,10] 13 :=
  permutation_upper _ _ _ [96,12,129,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14108

theorem m21890_12 : Upper (D 8) (R 8) [96,129,192,272,12] 13 :=
  permutation_upper _ _ _ [96,12,192,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14252

theorem m21890_33 : Upper (D 8) (R 8) [96,129,192,272,33] 13 :=
  permutation_upper _ _ _ [96,33,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14426

theorem m21890_34 : Upper (D 8) (R 8) [96,129,192,272,34] 13 :=
  permutation_upper _ _ _ [96,36,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14659

theorem m21890_36 : Upper (D 8) (R 8) [96,129,192,272,36] 13 :=
  permutation_upper _ _ _ [96,36,192,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14799

theorem m21890_40 : Upper (D 8) (R 8) [96,129,192,272,40] 13 :=
  permutation_upper _ _ _ [96,36,258,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14847

def r21890 : Route 9 := (fun mask => (mask,id))

def c21890 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21890 : Upper (D 8) (R 8) [96,129,192,272] 13 := by
  apply FastRouting.sound _ _ [96,129,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21890 c21890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21890_3
  · exact m21890_5
  · exact m21890_6
  · exact m21890_9
  · exact m21890_10
  · exact m21890_12
  · exact m21890_33
  · exact m21890_34
  · exact m21890_36
  · exact m21890_40

theorem m21891_3 : Upper (D 8) (R 8) [96,129,192,288,3] 13 :=
  permutation_upper _ _ _ [96,5,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13142

theorem m21891_5 : Upper (D 8) (R 8) [96,129,192,288,5] 13 :=
  permutation_upper _ _ _ [96,5,192,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13449

theorem m21891_6 : Upper (D 8) (R 8) [96,129,192,288,6] 13 :=
  permutation_upper _ _ _ [96,12,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14097

theorem m21891_9 : Upper (D 8) (R 8) [96,129,192,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13622

theorem m21891_10 : Upper (D 8) (R 8) [96,129,192,288,10] 13 :=
  permutation_upper _ _ _ [96,12,129,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14126

theorem m21891_12 : Upper (D 8) (R 8) [96,129,192,288,12] 13 :=
  permutation_upper _ _ _ [96,12,192,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14261

theorem m21891_33 : Upper (D 8) (R 8) [96,129,192,288,33] 13 :=
  permutation_upper _ _ _ [96,33,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14429

theorem m21891_34 : Upper (D 8) (R 8) [96,129,192,288,34] 13 :=
  permutation_upper _ _ _ [96,36,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14661

theorem m21891_36 : Upper (D 8) (R 8) [96,129,192,288,36] 13 :=
  permutation_upper _ _ _ [96,36,192,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14801

theorem m21891_40 : Upper (D 8) (R 8) [96,129,192,288,40] 13 :=
  permutation_upper _ _ _ [96,36,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14894

def r21891 : Route 9 := (fun mask => (mask,id))

def c21891 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21891 : Upper (D 8) (R 8) [96,129,192,288] 13 := by
  apply FastRouting.sound _ _ [96,129,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21891 c21891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21891_3
  · exact m21891_5
  · exact m21891_6
  · exact m21891_9
  · exact m21891_10
  · exact m21891_12
  · exact m21891_33
  · exact m21891_34
  · exact m21891_36
  · exact m21891_40

def b21892 : PairBound 9 := { available := 121, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 134 134 265 121 121 121 249 377), lower := (rows 97 134 134 265 16 32 64 128 256), losses := [] }

theorem u21892 : Upper (D 8) (R 8) [96,132,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21893 : PairBound 9 := { available := 121, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 134 134 296 121 121 121 249 377), lower := (rows 97 134 134 296 16 32 64 128 256), losses := [] }

theorem u21893 : Upper (D 8) (R 8) [96,132,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21894 : PairBound 9 := { available := 57, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 134 134 328 57 57 121 185 313), lower := (rows 97 134 134 328 16 32 64 128 256), losses := [] }

theorem u21894 : Upper (D 8) (R 8) [96,132,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21895 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 265 115 115 115 243 371), lower := (rows 97 134 140 265 16 32 64 128 256), losses := [] }

theorem u21895 : Upper (D 8) (R 8) [96,132,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21896 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 266 113 113 113 241 369), lower := (rows 97 134 140 266 16 32 64 128 256), losses := [] }

theorem u21896 : Upper (D 8) (R 8) [96,132,136,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21897 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 296 115 115 115 243 371), lower := (rows 97 134 140 296 16 32 64 128 256), losses := [] }

theorem u21897 : Upper (D 8) (R 8) [96,132,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21898 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 328 51 51 115 179 307), lower := (rows 97 134 140 328 16 32 64 128 256), losses := [] }

theorem u21898 : Upper (D 8) (R 8) [96,132,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21899 : PairBound 9 := { available := 107, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 265 123 107 107 235 363), lower := (rows 97 134 148 265 16 32 64 128 256), losses := [] }

theorem u21899 : Upper (D 8) (R 8) [96,132,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u21899
end Delivery.IrregularNine14.P08
