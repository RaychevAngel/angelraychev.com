import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0183
import IrregularNine14P08C0184
import IrregularNine14P08C0185
import IrregularNine14P08C0186
import IrregularNine14P08C0187
import IrregularNine14P08C0188

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m20280_5 : Upper (D 8) (R 8) [66,129,96,160,5] 13 :=
  permutation_upper _ _ _ [66,129,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10982

theorem m20280_9 : Upper (D 8) (R 8) [66,129,96,160,9] 13 :=
  permutation_upper _ _ _ [66,129,9,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10997

theorem m20280_12 : Upper (D 8) (R 8) [66,129,96,160,12] 13 :=
  permutation_upper _ _ _ [66,129,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11044

theorem m20280_33 : Upper (D 8) (R 8) [66,129,96,160,33] 13 :=
  permutation_upper _ _ _ [66,129,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11086

theorem m20280_36 : Upper (D 8) (R 8) [66,129,96,160,36] 13 :=
  permutation_upper _ _ _ [66,129,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11130

theorem m20280_40 : Upper (D 8) (R 8) [66,129,96,160,40] 13 :=
  permutation_upper _ _ _ [66,129,40,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11150

def r20280 : Route 9 := (fun mask => (mask,id))

def c20280 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20280 : Upper (D 8) (R 8) [66,129,96,160] 13 := by
  apply FastRouting.sound _ _ [66,129,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r20280 c20280
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20280_5
  · exact m20280_9
  · exact m20280_12
  · exact m20280_33
  · exact m20280_36
  · exact m20280_40
  · exact u11217
  · exact u11218
  · exact u11219
  · exact u11220

def b20281 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 265 188 188 252 188 444), lower := (rows 67 131 100 265 16 32 64 128 256), losses := [] }

theorem u20281 : Upper (D 8) (R 8) [66,129,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20282_9 : Upper (D 8) (R 8) [66,129,96,260,9] 13 :=
  permutation_upper _ _ _ [66,129,9,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11005

theorem m20282_33 : Upper (D 8) (R 8) [66,129,96,260,33] 13 :=
  permutation_upper _ _ _ [66,129,33,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11088

theorem m20282_40 : Upper (D 8) (R 8) [66,129,96,260,40] 13 :=
  permutation_upper _ _ _ [66,129,40,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11167

theorem m20282_129 : Upper (D 8) (R 8) [66,129,96,260,129] 13 :=
  permutation_upper _ _ _ [66,129,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11207

theorem m20282_136 : Upper (D 8) (R 8) [66,129,96,260,136] 13 :=
  permutation_upper _ _ _ [66,129,96,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11214

theorem m20282_160 : Upper (D 8) (R 8) [66,129,96,260,160] 13 :=
  permutation_upper _ _ _ [66,129,96,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11218

def r20282 : Route 9 := (fun mask => (mask,id))

def c20282 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20282 : Upper (D 8) (R 8) [66,129,96,260] 13 := by
  apply FastRouting.sound _ _ [66,129,96,260] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20282 c20282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20282_9
  · exact m20282_33
  · exact m20282_40
  · exact m20282_129
  · exact m20282_136
  · exact m20282_160

theorem m20283_5 : Upper (D 8) (R 8) [66,129,96,272,5] 13 :=
  permutation_upper _ _ _ [66,129,9,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10983

theorem m20283_9 : Upper (D 8) (R 8) [66,129,96,272,9] 13 :=
  permutation_upper _ _ _ [66,129,9,260,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11001

theorem m20283_12 : Upper (D 8) (R 8) [66,129,96,272,12] 13 :=
  permutation_upper _ _ _ [66,129,24,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11046

theorem m20283_33 : Upper (D 8) (R 8) [66,129,96,272,33] 13 :=
  permutation_upper _ _ _ [66,129,33,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11087

theorem m20283_36 : Upper (D 8) (R 8) [66,129,96,272,36] 13 :=
  permutation_upper _ _ _ [66,129,40,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11131

theorem m20283_40 : Upper (D 8) (R 8) [66,129,96,272,40] 13 :=
  permutation_upper _ _ _ [66,129,40,260,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11161

theorem m20283_129 : Upper (D 8) (R 8) [66,129,96,272,129] 13 :=
  permutation_upper _ _ _ [66,129,96,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11208

theorem m20283_132 : Upper (D 8) (R 8) [66,129,96,272,132] 13 :=
  permutation_upper _ _ _ [66,129,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11211

theorem m20283_136 : Upper (D 8) (R 8) [66,129,96,272,136] 13 :=
  permutation_upper _ _ _ [66,129,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11215

theorem m20283_160 : Upper (D 8) (R 8) [66,129,96,272,160] 13 :=
  permutation_upper _ _ _ [66,129,96,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11219

def r20283 : Route 9 := (fun mask => (mask,id))

def c20283 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20283 : Upper (D 8) (R 8) [66,129,96,272] 13 := by
  apply FastRouting.sound _ _ [66,129,96,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20283 c20283
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20283_5
  · exact m20283_9
  · exact m20283_12
  · exact m20283_33
  · exact m20283_36
  · exact m20283_40
  · exact m20283_129
  · exact m20283_132
  · exact m20283_136
  · exact m20283_160

theorem m20284_5 : Upper (D 8) (R 8) [66,129,96,288,5] 13 :=
  permutation_upper _ _ _ [66,129,9,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10984

theorem m20284_9 : Upper (D 8) (R 8) [66,129,96,288,9] 13 :=
  permutation_upper _ _ _ [66,129,9,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11010

theorem m20284_12 : Upper (D 8) (R 8) [66,129,96,288,12] 13 :=
  permutation_upper _ _ _ [66,129,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11047

theorem m20284_33 : Upper (D 8) (R 8) [66,129,96,288,33] 13 :=
  permutation_upper _ _ _ [66,129,33,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11089

theorem m20284_36 : Upper (D 8) (R 8) [66,129,96,288,36] 13 :=
  permutation_upper _ _ _ [66,129,40,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11132

theorem m20284_40 : Upper (D 8) (R 8) [66,129,96,288,40] 13 :=
  permutation_upper _ _ _ [66,129,40,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11173

theorem m20284_129 : Upper (D 8) (R 8) [66,129,96,288,129] 13 :=
  permutation_upper _ _ _ [66,129,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11209

theorem m20284_132 : Upper (D 8) (R 8) [66,129,96,288,132] 13 :=
  permutation_upper _ _ _ [66,129,96,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11212

theorem m20284_136 : Upper (D 8) (R 8) [66,129,96,288,136] 13 :=
  permutation_upper _ _ _ [66,129,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11216

theorem m20284_160 : Upper (D 8) (R 8) [66,129,96,288,160] 13 :=
  permutation_upper _ _ _ [66,129,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11220

def r20284 : Route 9 := (fun mask => (mask,id))

def c20284 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20284 : Upper (D 8) (R 8) [66,129,96,288] 13 := by
  apply FastRouting.sound _ _ [66,129,96,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20284 c20284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20284_5
  · exact m20284_9
  · exact m20284_12
  · exact m20284_33
  · exact m20284_36
  · exact m20284_40
  · exact m20284_129
  · exact m20284_132
  · exact m20284_136
  · exact m20284_160

theorem m20285_5 : Upper (D 8) (R 8) [66,129,96,384,5] 13 :=
  permutation_upper _ _ _ [66,129,9,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10985

theorem m20285_9 : Upper (D 8) (R 8) [66,129,96,384,9] 13 :=
  permutation_upper _ _ _ [66,129,9,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11018

theorem m20285_12 : Upper (D 8) (R 8) [66,129,96,384,12] 13 :=
  permutation_upper _ _ _ [66,129,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11048

theorem m20285_33 : Upper (D 8) (R 8) [66,129,96,384,33] 13 :=
  permutation_upper _ _ _ [66,129,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11090

theorem m20285_36 : Upper (D 8) (R 8) [66,129,96,384,36] 13 :=
  permutation_upper _ _ _ [66,129,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11133

theorem m20285_40 : Upper (D 8) (R 8) [66,129,96,384,40] 13 :=
  permutation_upper _ _ _ [66,129,40,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11181

def r20285 : Route 9 := (fun mask => (mask,id))

def c20285 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20285 : Upper (D 8) (R 8) [66,129,96,384] 13 := by
  apply FastRouting.sound _ _ [66,129,96,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20285 c20285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20285_5
  · exact m20285_9
  · exact m20285_12
  · exact m20285_33
  · exact m20285_36
  · exact m20285_40

def b20286 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 133 268 120 120 120 248 376), lower := (rows 67 131 133 268 16 32 64 128 256), losses := [] }

theorem u20286 : Upper (D 8) (R 8) [66,129,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20287 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 133 296 124 124 124 252 380), lower := (rows 67 131 133 296 16 32 64 128 256), losses := [] }

theorem u20287 : Upper (D 8) (R 8) [66,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20288 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 133 328 60 60 124 188 316), lower := (rows 67 131 133 328 16 32 64 128 256), losses := [] }

theorem u20288 : Upper (D 8) (R 8) [66,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20289 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 140 265 116 116 116 244 372), lower := (rows 67 131 140 265 16 32 64 128 256), losses := [] }

theorem u20289 : Upper (D 8) (R 8) [66,129,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20290 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 140 268 113 113 113 241 369), lower := (rows 67 131 140 268 16 32 64 128 256), losses := [] }

theorem u20290 : Upper (D 8) (R 8) [66,129,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20291_5 : Upper (D 8) (R 8) [66,129,136,272,5] 13 :=
  permutation_upper _ _ _ [66,129,9,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10992

theorem m20291_33 : Upper (D 8) (R 8) [66,129,136,272,33] 13 :=
  permutation_upper _ _ _ [66,129,33,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11094

theorem m20291_36 : Upper (D 8) (R 8) [66,129,136,272,36] 13 :=
  permutation_upper _ _ _ [66,129,40,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11146

theorem m20291_65 : Upper (D 8) (R 8) [66,129,136,272,65] 13 :=
  permutation_upper _ _ _ [66,129,65,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11184

theorem m20291_68 : Upper (D 8) (R 8) [66,129,136,272,68] 13 :=
  permutation_upper _ _ _ [66,129,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11193

theorem m20291_96 : Upper (D 8) (R 8) [66,129,136,272,96] 13 :=
  permutation_upper _ _ _ [66,129,96,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11214

def r20291 : Route 9 := (fun mask => (mask,id))

def c20291 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20291 : Upper (D 8) (R 8) [66,129,136,272] 13 := by
  apply FastRouting.sound _ _ [66,129,136,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r20291 c20291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20291_5
  · exact m20291_33
  · exact m20291_36
  · exact m20291_65
  · exact m20291_68
  · exact m20291_96

theorem m20292_5 : Upper (D 8) (R 8) [66,129,136,288,5] 13 :=
  permutation_upper _ _ _ [66,129,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10993

theorem m20292_33 : Upper (D 8) (R 8) [66,129,136,288,33] 13 :=
  permutation_upper _ _ _ [66,129,33,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11095

theorem m20292_36 : Upper (D 8) (R 8) [66,129,136,288,36] 13 :=
  permutation_upper _ _ _ [66,129,40,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11147

theorem m20292_65 : Upper (D 8) (R 8) [66,129,136,288,65] 13 :=
  permutation_upper _ _ _ [66,129,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11185

theorem m20292_68 : Upper (D 8) (R 8) [66,129,136,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11194

theorem m20292_96 : Upper (D 8) (R 8) [66,129,136,288,96] 13 :=
  permutation_upper _ _ _ [66,129,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11216

def r20292 : Route 9 := (fun mask => (mask,id))

def c20292 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20292 : Upper (D 8) (R 8) [66,129,136,288] 13 := by
  apply FastRouting.sound _ _ [66,129,136,288] 13 (by decide) (choices 2) [5,33,36,65,68,96] r20292 c20292
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20292_5
  · exact m20292_33
  · exact m20292_36
  · exact m20292_65
  · exact m20292_68
  · exact m20292_96

theorem m20293_5 : Upper (D 8) (R 8) [66,129,136,320,5] 13 :=
  permutation_upper _ _ _ [66,129,9,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10994

theorem m20293_33 : Upper (D 8) (R 8) [66,129,136,320,33] 13 :=
  permutation_upper _ _ _ [66,129,33,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11096

theorem m20293_36 : Upper (D 8) (R 8) [66,129,136,320,36] 13 :=
  permutation_upper _ _ _ [66,129,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11148

def r20293 : Route 9 := (fun mask => (mask,id))

def c20293 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20293 : Upper (D 8) (R 8) [66,129,136,320] 13 := by
  apply FastRouting.sound _ _ [66,129,136,320] 13 (by decide) (choices 2) [5,33,36] r20293 c20293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m20293_5
  · exact m20293_33
  · exact m20293_36

theorem m20294_9 : Upper (D 8) (R 8) [66,129,144,260,9] 13 :=
  permutation_upper _ _ _ [66,129,9,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11006

theorem m20294_33 : Upper (D 8) (R 8) [66,129,144,260,33] 13 :=
  permutation_upper _ _ _ [66,129,33,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11091

theorem m20294_40 : Upper (D 8) (R 8) [66,129,144,260,40] 13 :=
  permutation_upper _ _ _ [66,129,40,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11169

theorem m20294_65 : Upper (D 8) (R 8) [66,129,144,260,65] 13 :=
  permutation_upper _ _ _ [66,129,65,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11182

theorem m20294_72 : Upper (D 8) (R 8) [66,129,144,260,72] 13 :=
  permutation_upper _ _ _ [66,129,72,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11202

theorem m20294_96 : Upper (D 8) (R 8) [66,129,144,260,96] 13 :=
  permutation_upper _ _ _ [66,129,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11211

def r20294 : Route 9 := (fun mask => (mask,id))

def c20294 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20294 : Upper (D 8) (R 8) [66,129,144,260] 13 := by
  apply FastRouting.sound _ _ [66,129,144,260] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20294 c20294
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20294_9
  · exact m20294_33
  · exact m20294_40
  · exact m20294_65
  · exact m20294_72
  · exact m20294_96

theorem m20295_5 : Upper (D 8) (R 8) [66,129,144,288,5] 13 :=
  permutation_upper _ _ _ [66,129,9,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10987

theorem m20295_9 : Upper (D 8) (R 8) [66,129,144,288,9] 13 :=
  permutation_upper _ _ _ [66,129,9,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11011

theorem m20295_12 : Upper (D 8) (R 8) [66,129,144,288,12] 13 :=
  permutation_upper _ _ _ [66,129,24,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11052

theorem m20295_33 : Upper (D 8) (R 8) [66,129,144,288,33] 13 :=
  permutation_upper _ _ _ [66,129,33,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11092

theorem m20295_36 : Upper (D 8) (R 8) [66,129,144,288,36] 13 :=
  permutation_upper _ _ _ [66,129,40,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11140

theorem m20295_40 : Upper (D 8) (R 8) [66,129,144,288,40] 13 :=
  permutation_upper _ _ _ [66,129,40,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11174

theorem m20295_65 : Upper (D 8) (R 8) [66,129,144,288,65] 13 :=
  permutation_upper _ _ _ [66,129,65,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11183

theorem m20295_68 : Upper (D 8) (R 8) [66,129,144,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11191

theorem m20295_72 : Upper (D 8) (R 8) [66,129,144,288,72] 13 :=
  permutation_upper _ _ _ [66,129,72,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11205

theorem m20295_96 : Upper (D 8) (R 8) [66,129,144,288,96] 13 :=
  permutation_upper _ _ _ [66,129,96,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11212

def r20295 : Route 9 := (fun mask => (mask,id))

def c20295 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20295 : Upper (D 8) (R 8) [66,129,144,288] 13 := by
  apply FastRouting.sound _ _ [66,129,144,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r20295 c20295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20295_5
  · exact m20295_9
  · exact m20295_12
  · exact m20295_33
  · exact m20295_36
  · exact m20295_40
  · exact m20295_65
  · exact m20295_68
  · exact m20295_72
  · exact m20295_96

theorem m20296_5 : Upper (D 8) (R 8) [66,129,144,320,5] 13 :=
  permutation_upper _ _ _ [66,129,9,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10988

theorem m20296_9 : Upper (D 8) (R 8) [66,129,144,320,9] 13 :=
  permutation_upper _ _ _ [66,129,9,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11014

theorem m20296_12 : Upper (D 8) (R 8) [66,129,144,320,12] 13 :=
  permutation_upper _ _ _ [66,129,24,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11053

theorem m20296_33 : Upper (D 8) (R 8) [66,129,144,320,33] 13 :=
  permutation_upper _ _ _ [66,129,33,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11093

theorem m20296_36 : Upper (D 8) (R 8) [66,129,144,320,36] 13 :=
  permutation_upper _ _ _ [66,129,40,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11141

theorem m20296_40 : Upper (D 8) (R 8) [66,129,144,320,40] 13 :=
  permutation_upper _ _ _ [66,129,40,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11177

def r20296 : Route 9 := (fun mask => (mask,id))

def c20296 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20296 : Upper (D 8) (R 8) [66,129,144,320] 13 := by
  apply FastRouting.sound _ _ [66,129,144,320] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20296 c20296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20296_5
  · exact m20296_9
  · exact m20296_12
  · exact m20296_33
  · exact m20296_36
  · exact m20296_40

def b20297 : PairBound 9 := { available := 124, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 164 265 124 124 124 252 380), lower := (rows 67 131 164 265 16 32 64 128 256), losses := [] }

theorem u20297 : Upper (D 8) (R 8) [66,129,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20298_9 : Upper (D 8) (R 8) [66,129,160,260,9] 13 :=
  permutation_upper _ _ _ [66,129,9,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11007

theorem m20298_33 : Upper (D 8) (R 8) [66,129,160,260,33] 13 :=
  permutation_upper _ _ _ [66,129,33,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11098

theorem m20298_40 : Upper (D 8) (R 8) [66,129,160,260,40] 13 :=
  permutation_upper _ _ _ [66,129,40,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11170

theorem m20298_65 : Upper (D 8) (R 8) [66,129,160,260,65] 13 :=
  permutation_upper _ _ _ [66,129,65,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11187

theorem m20298_72 : Upper (D 8) (R 8) [66,129,160,260,72] 13 :=
  permutation_upper _ _ _ [66,129,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11203

theorem m20298_96 : Upper (D 8) (R 8) [66,129,160,260,96] 13 :=
  permutation_upper _ _ _ [66,129,96,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11219

def r20298 : Route 9 := (fun mask => (mask,id))

def c20298 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20298 : Upper (D 8) (R 8) [66,129,160,260] 13 := by
  apply FastRouting.sound _ _ [66,129,160,260] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20298 c20298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20298_9
  · exact m20298_33
  · exact m20298_40
  · exact m20298_65
  · exact m20298_72
  · exact m20298_96

theorem m20299_5 : Upper (D 8) (R 8) [66,129,160,272,5] 13 :=
  permutation_upper _ _ _ [66,129,9,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10998

theorem m20299_9 : Upper (D 8) (R 8) [66,129,160,272,9] 13 :=
  permutation_upper _ _ _ [66,129,9,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11002

theorem m20299_12 : Upper (D 8) (R 8) [66,129,160,272,12] 13 :=
  permutation_upper _ _ _ [66,129,24,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11055

theorem m20299_33 : Upper (D 8) (R 8) [66,129,160,272,33] 13 :=
  permutation_upper _ _ _ [66,129,33,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11097

theorem m20299_36 : Upper (D 8) (R 8) [66,129,160,272,36] 13 :=
  permutation_upper _ _ _ [66,129,40,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11151

theorem m20299_40 : Upper (D 8) (R 8) [66,129,160,272,40] 13 :=
  permutation_upper _ _ _ [66,129,40,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11163

theorem m20299_65 : Upper (D 8) (R 8) [66,129,160,272,65] 13 :=
  permutation_upper _ _ _ [66,129,65,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11186

theorem m20299_68 : Upper (D 8) (R 8) [66,129,160,272,68] 13 :=
  permutation_upper _ _ _ [66,129,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11196

theorem m20299_72 : Upper (D 8) (R 8) [66,129,160,272,72] 13 :=
  permutation_upper _ _ _ [66,129,72,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11200

theorem m20299_96 : Upper (D 8) (R 8) [66,129,160,272,96] 13 :=
  permutation_upper _ _ _ [66,129,96,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11218

def r20299 : Route 9 := (fun mask => (mask,id))

def c20299 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20299 : Upper (D 8) (R 8) [66,129,160,272] 13 := by
  apply FastRouting.sound _ _ [66,129,160,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r20299 c20299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20299_5
  · exact m20299_9
  · exact m20299_12
  · exact m20299_33
  · exact m20299_36
  · exact m20299_40
  · exact m20299_65
  · exact m20299_68
  · exact m20299_72
  · exact m20299_96

theorem m20300_5 : Upper (D 8) (R 8) [66,129,160,288,5] 13 :=
  permutation_upper _ _ _ [66,129,9,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10999

theorem m20300_9 : Upper (D 8) (R 8) [66,129,160,288,9] 13 :=
  permutation_upper _ _ _ [66,129,9,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11012

theorem m20300_12 : Upper (D 8) (R 8) [66,129,160,288,12] 13 :=
  permutation_upper _ _ _ [66,129,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11056

theorem m20300_33 : Upper (D 8) (R 8) [66,129,160,288,33] 13 :=
  permutation_upper _ _ _ [66,129,33,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11099

theorem m20300_36 : Upper (D 8) (R 8) [66,129,160,288,36] 13 :=
  permutation_upper _ _ _ [66,129,40,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11152

theorem m20300_40 : Upper (D 8) (R 8) [66,129,160,288,40] 13 :=
  permutation_upper _ _ _ [66,129,40,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11175

theorem m20300_65 : Upper (D 8) (R 8) [66,129,160,288,65] 13 :=
  permutation_upper _ _ _ [66,129,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11188

theorem m20300_68 : Upper (D 8) (R 8) [66,129,160,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11197

theorem m20300_72 : Upper (D 8) (R 8) [66,129,160,288,72] 13 :=
  permutation_upper _ _ _ [66,129,72,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11206

theorem m20300_96 : Upper (D 8) (R 8) [66,129,160,288,96] 13 :=
  permutation_upper _ _ _ [66,129,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11220

def r20300 : Route 9 := (fun mask => (mask,id))

def c20300 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20300 : Upper (D 8) (R 8) [66,129,160,288] 13 := by
  apply FastRouting.sound _ _ [66,129,160,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r20300 c20300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20300_5
  · exact m20300_9
  · exact m20300_12
  · exact m20300_33
  · exact m20300_36
  · exact m20300_40
  · exact m20300_65
  · exact m20300_68
  · exact m20300_72
  · exact m20300_96

theorem m20301_5 : Upper (D 8) (R 8) [66,129,160,320,5] 13 :=
  permutation_upper _ _ _ [66,129,9,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11000

theorem m20301_9 : Upper (D 8) (R 8) [66,129,160,320,9] 13 :=
  permutation_upper _ _ _ [66,129,9,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11015

theorem m20301_12 : Upper (D 8) (R 8) [66,129,160,320,12] 13 :=
  permutation_upper _ _ _ [66,129,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11057

theorem m20301_33 : Upper (D 8) (R 8) [66,129,160,320,33] 13 :=
  permutation_upper _ _ _ [66,129,33,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11100

theorem m20301_36 : Upper (D 8) (R 8) [66,129,160,320,36] 13 :=
  permutation_upper _ _ _ [66,129,40,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11153

theorem m20301_40 : Upper (D 8) (R 8) [66,129,160,320,40] 13 :=
  permutation_upper _ _ _ [66,129,40,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11178

def r20301 : Route 9 := (fun mask => (mask,id))

def c20301 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20301 : Upper (D 8) (R 8) [66,129,160,320] 13 := by
  apply FastRouting.sound _ _ [66,129,160,320] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20301 c20301
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20301_5
  · exact m20301_9
  · exact m20301_12
  · exact m20301_33
  · exact m20301_36
  · exact m20301_40

def b20302 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 196 268 57 57 121 185 313), lower := (rows 67 131 196 268 16 32 64 128 256), losses := [] }

theorem u20302 : Upper (D 8) (R 8) [66,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20303 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 196 296 61 61 125 189 317), lower := (rows 67 131 196 296 16 32 64 128 256), losses := [] }

theorem u20303 : Upper (D 8) (R 8) [66,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20304 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 134 13 25 496 480 480 480 480), lower := (rows 67 134 13 25 16 32 64 128 256), losses := [] }

theorem u20304 : Upper (D 8) (R 8) [66,132,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20305 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 134 13 41 496 496 496 496 496), lower := (rows 67 134 13 41 16 32 64 128 256), losses := [] }

theorem u20305 : Upper (D 8) (R 8) [66,132,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20306 : Route 9 := (fun mask => (mask,id))

def c20306 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20306 : Upper (D 8) (R 8) [66,132,9,48] 13 := by
  apply FastRouting.sound _ _ [66,132,9,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20306 c20306
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11221
  · exact u11222
  · exact u11223
  · exact u11224
  · exact u11225
  · exact u11226
  · exact u11227
  · exact u11228
  · exact u11229
  · exact u11230

def b20307 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 134 13 73 432 432 496 432 432), lower := (rows 67 134 13 73 16 32 64 128 256), losses := [] }

theorem u20307 : Upper (D 8) (R 8) [66,132,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20308 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 88 433 417 481 417 417), lower := (rows 67 134 13 88 16 32 64 128 256), losses := [] }

theorem u20308 : Upper (D 8) (R 8) [66,132,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20309 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 104 433 433 497 433 433), lower := (rows 67 134 13 104 16 32 64 128 256), losses := [] }

theorem u20309 : Upper (D 8) (R 8) [66,132,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20310 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 67 134 13 137 368 368 368 496 368), lower := (rows 67 134 13 137 16 32 64 128 256), losses := [] }

theorem u20310 : Upper (D 8) (R 8) [66,132,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20311 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 152 369 353 353 481 353), lower := (rows 67 134 13 152 16 32 64 128 256), losses := [] }

theorem u20311 : Upper (D 8) (R 8) [66,132,9,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20312 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 168 369 369 369 497 369), lower := (rows 67 134 13 168 16 32 64 128 256), losses := [] }

theorem u20312 : Upper (D 8) (R 8) [66,132,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20313 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5)], upper := (rows 67 134 13 200 305 305 369 433 305), lower := (rows 67 134 13 200 16 32 64 128 256), losses := [] }

theorem u20313 : Upper (D 8) (R 8) [66,132,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20314 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 134 13 265 240 240 240 240 496), lower := (rows 67 134 13 265 16 32 64 128 256), losses := [] }

theorem u20314 : Upper (D 8) (R 8) [66,132,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20315 : Route 9 := (fun mask => (mask,id))

def c20315 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20315 : Upper (D 8) (R 8) [66,132,9,272] 13 := by
  apply FastRouting.sound _ _ [66,132,9,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20315 c20315
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11231
  · exact u11232
  · exact u11233
  · exact u11234
  · exact u11235
  · exact u11236

def r20316 : Route 9 := (fun mask => (mask,id))

def c20316 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20316 : Upper (D 8) (R 8) [66,132,9,288] 13 := by
  apply FastRouting.sound _ _ [66,132,9,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20316 c20316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11237
  · exact u11238
  · exact u11239
  · exact u11240
  · exact u11241
  · exact u11242

def b20317 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 328 177 177 241 177 433), lower := (rows 67 134 13 328 16 32 64 128 256), losses := [] }

theorem u20317 : Upper (D 8) (R 8) [66,132,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20318 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 392 113 113 113 241 369), lower := (rows 67 134 13 392 16 32 64 128 256), losses := [] }

theorem u20318 : Upper (D 8) (R 8) [66,132,9,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20319 : Route 9 := (fun mask => (mask,id))

def c20319 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20319 : Upper (D 8) (R 8) [66,132,24,33] 13 := by
  apply FastRouting.sound _ _ [66,132,24,33] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20319 c20319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11243
  · exact u11244
  · exact u11245
  · exact u11246
  · exact u11247
  · exact u11248
  · exact u11249
  · exact u11250
  · exact u11251
  · exact u11252

def b20320 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 28 73 433 417 481 417 417), lower := (rows 67 134 28 73 16 32 64 128 256), losses := [] }

theorem u20320 : Upper (D 8) (R 8) [66,132,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20321 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 28 104 433 417 481 417 417), lower := (rows 67 134 28 104 16 32 64 128 256), losses := [] }

theorem u20321 : Upper (D 8) (R 8) [66,132,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20322 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 137 369 353 353 481 353), lower := (rows 67 134 28 137 16 32 64 128 256), losses := [] }

theorem u20322 : Upper (D 8) (R 8) [66,132,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20323 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 168 369 353 353 481 353), lower := (rows 67 134 28 168 16 32 64 128 256), losses := [] }

theorem u20323 : Upper (D 8) (R 8) [66,132,24,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20324 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 200 305 289 353 417 289), lower := (rows 67 134 28 200 16 32 64 128 256), losses := [] }

theorem u20324 : Upper (D 8) (R 8) [66,132,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20325_33 : Upper (D 8) (R 8) [66,132,24,257,33] 13 :=
  permutation_upper _ _ _ [66,132,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11249

theorem m20325_65 : Upper (D 8) (R 8) [66,132,24,257,65] 13 :=
  permutation_upper _ _ _ [66,132,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11253

theorem m20325_96 : Upper (D 8) (R 8) [66,132,24,257,96] 13 :=
  permutation_upper _ _ _ [66,132,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11255

theorem m20325_129 : Upper (D 8) (R 8) [66,132,24,257,129] 13 :=
  permutation_upper _ _ _ [66,132,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11257

theorem m20325_160 : Upper (D 8) (R 8) [66,132,24,257,160] 13 :=
  permutation_upper _ _ _ [66,132,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11259

theorem m20325_192 : Upper (D 8) (R 8) [66,132,24,257,192] 13 :=
  permutation_upper _ _ _ [66,132,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11261

def r20325 : Route 9 := (fun mask => (mask,id))

def c20325 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20325 : Upper (D 8) (R 8) [66,132,24,257] 13 := by
  apply FastRouting.sound _ _ [66,132,24,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20325 c20325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20325_33
  · exact m20325_65
  · exact m20325_96
  · exact m20325_129
  · exact m20325_160
  · exact m20325_192

theorem m20326_33 : Upper (D 8) (R 8) [66,132,24,288,33] 13 :=
  permutation_upper _ _ _ [66,132,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11250

theorem m20326_65 : Upper (D 8) (R 8) [66,132,24,288,65] 13 :=
  permutation_upper _ _ _ [66,132,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11254

theorem m20326_96 : Upper (D 8) (R 8) [66,132,24,288,96] 13 :=
  permutation_upper _ _ _ [66,132,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11256

theorem m20326_129 : Upper (D 8) (R 8) [66,132,24,288,129] 13 :=
  permutation_upper _ _ _ [66,132,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11258

theorem m20326_160 : Upper (D 8) (R 8) [66,132,24,288,160] 13 :=
  permutation_upper _ _ _ [66,132,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11260

theorem m20326_192 : Upper (D 8) (R 8) [66,132,24,288,192] 13 :=
  permutation_upper _ _ _ [66,132,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11262

def r20326 : Route 9 := (fun mask => (mask,id))

def c20326 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20326 : Upper (D 8) (R 8) [66,132,24,288] 13 := by
  apply FastRouting.sound _ _ [66,132,24,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20326 c20326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20326_33
  · exact m20326_65
  · exact m20326_96
  · exact m20326_129
  · exact m20326_160
  · exact m20326_192

def b20327 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 28 328 177 161 225 161 417), lower := (rows 67 134 28 328 16 32 64 128 256), losses := [] }

theorem u20327 : Upper (D 8) (R 8) [66,132,24,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20328 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 392 113 97 97 225 353), lower := (rows 67 134 28 392 16 32 64 128 256), losses := [] }

theorem u20328 : Upper (D 8) (R 8) [66,132,24,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20329 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 37 25 504 488 488 488 488), lower := (rows 67 134 37 25 16 32 64 128 256), losses := [] }

theorem u20329 : Upper (D 8) (R 8) [66,132,33,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20330 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 504 504 504 504 504), lower := (rows 67 134 37 41 16 32 64 128 256), losses := [] }

theorem u20330 : Upper (D 8) (R 8) [66,132,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20331_9 : Upper (D 8) (R 8) [66,132,33,48,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11263

theorem m20331_33 : Upper (D 8) (R 8) [66,132,33,48,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11273

def r20331 : Route 9 := (fun mask => (mask,id))

def c20331 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20331 : Upper (D 8) (R 8) [66,132,33,48] 13 := by
  apply FastRouting.sound _ _ [66,132,33,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r20331 c20331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20331_9
  · exact m20331_33
  · exact u11283
  · exact u11284
  · exact u11285
  · exact u11286
  · exact u11287
  · exact u11288
  · exact u11289
  · exact u11290
  · exact u11291
  · exact u11292
  · exact u11293
  · exact u11294
  · exact u11295

def b20332 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 73 440 440 504 440 440), lower := (rows 67 134 37 73 16 32 64 128 256), losses := [] }

theorem u20332 : Upper (D 8) (R 8) [66,132,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20333_9 : Upper (D 8) (R 8) [66,132,33,80,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11264

theorem m20333_33 : Upper (D 8) (R 8) [66,132,33,80,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11274

theorem m20333_40 : Upper (D 8) (R 8) [66,132,33,80,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11285

def r20333 : Route 9 := (fun mask => (mask,id))

def c20333 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20333 : Upper (D 8) (R 8) [66,132,33,80] 13 := by
  apply FastRouting.sound _ _ [66,132,33,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20333 c20333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20333_9
  · exact m20333_33
  · exact m20333_40
  · exact u11301
  · exact u11302
  · exact u11303
  · exact u11304
  · exact u11305
  · exact u11306
  · exact u11307

theorem m20334_9 : Upper (D 8) (R 8) [66,132,33,96,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11265

theorem m20334_33 : Upper (D 8) (R 8) [66,132,33,96,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11275

theorem m20334_40 : Upper (D 8) (R 8) [66,132,33,96,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11286

def r20334 : Route 9 := (fun mask => (mask,id))

def c20334 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20334 : Upper (D 8) (R 8) [66,132,33,96] 13 := by
  apply FastRouting.sound _ _ [66,132,33,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20334 c20334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20334_9
  · exact m20334_33
  · exact m20334_40
  · exact u11308
  · exact u11309
  · exact u11310
  · exact u11311
  · exact u11312
  · exact u11313
  · exact u11314

def b20335 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 137 376 376 376 504 376), lower := (rows 67 134 37 137 16 32 64 128 256), losses := [] }

theorem u20335 : Upper (D 8) (R 8) [66,132,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20336_9 : Upper (D 8) (R 8) [66,132,33,144,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11266

theorem m20336_33 : Upper (D 8) (R 8) [66,132,33,144,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11276

theorem m20336_40 : Upper (D 8) (R 8) [66,132,33,144,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11288

theorem m20336_65 : Upper (D 8) (R 8) [66,132,33,144,65] 13 :=
  permutation_upper _ _ _ [66,132,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11296

theorem m20336_72 : Upper (D 8) (R 8) [66,132,33,144,72] 13 :=
  permutation_upper _ _ _ [66,132,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11302

theorem m20336_96 : Upper (D 8) (R 8) [66,132,33,144,96] 13 :=
  permutation_upper _ _ _ [66,132,33,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11309

def r20336 : Route 9 := (fun mask => (mask,id))

def c20336 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u20336 : Upper (D 8) (R 8) [66,132,33,144] 13 := by
  apply FastRouting.sound _ _ [66,132,33,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r20336 c20336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20336_9
  · exact m20336_33
  · exact m20336_40
  · exact m20336_65
  · exact m20336_72
  · exact m20336_96
  · exact u11318
  · exact u11319
  · exact u11320
  · exact u11321

theorem m20337_9 : Upper (D 8) (R 8) [66,132,33,160,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11267

theorem m20337_33 : Upper (D 8) (R 8) [66,132,33,160,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11277

theorem m20337_40 : Upper (D 8) (R 8) [66,132,33,160,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11289

theorem m20337_65 : Upper (D 8) (R 8) [66,132,33,160,65] 13 :=
  permutation_upper _ _ _ [66,132,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11297

theorem m20337_72 : Upper (D 8) (R 8) [66,132,33,160,72] 13 :=
  permutation_upper _ _ _ [66,132,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11303

theorem m20337_96 : Upper (D 8) (R 8) [66,132,33,160,96] 13 :=
  permutation_upper _ _ _ [66,132,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11310

def r20337 : Route 9 := (fun mask => (mask,id))

def c20337 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u20337 : Upper (D 8) (R 8) [66,132,33,160] 13 := by
  apply FastRouting.sound _ _ [66,132,33,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r20337 c20337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20337_9
  · exact m20337_33
  · exact m20337_40
  · exact m20337_65
  · exact m20337_72
  · exact m20337_96
  · exact u11322
  · exact u11323
  · exact u11324
  · exact u11325

theorem m20338_9 : Upper (D 8) (R 8) [66,132,33,192,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11268

theorem m20338_33 : Upper (D 8) (R 8) [66,132,33,192,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11278

theorem m20338_40 : Upper (D 8) (R 8) [66,132,33,192,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11290

def r20338 : Route 9 := (fun mask => (mask,id))

def c20338 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20338 : Upper (D 8) (R 8) [66,132,33,192] 13 := by
  apply FastRouting.sound _ _ [66,132,33,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r20338 c20338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20338_9
  · exact m20338_33
  · exact m20338_40
  · exact u11326
  · exact u11327
  · exact u11328

def b20339 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 37 265 248 248 248 248 504), lower := (rows 67 134 37 265 16 32 64 128 256), losses := [] }

theorem u20339 : Upper (D 8) (R 8) [66,132,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u20339
end Delivery.IrregularNine14.P08
