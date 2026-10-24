import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0336
import IrregularNine14P08C0337
import IrregularNine14P08C0338
import IrregularNine14P08C0339
import IrregularNine14P08C0340
import IrregularNine14P08C0341
import IrregularNine14P08C0342
import IrregularNine14P08C0343
import IrregularNine14P08C0344

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24060 : PairBound 9 := { available := 380, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 133 380 380 380 380 508 380), lower := (rows 67 131 133 8 16 32 64 128 256), losses := [] }

theorem u24060 : Upper (D 8) (R 8) [66,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24061_5 : Upper (D 8) (R 8) [66,129,136,5] 13 :=
  permutation_upper _ _ _ [66,129,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20195

theorem m24061_17 : Upper (D 8) (R 8) [66,129,136,17] 13 :=
  permutation_upper _ _ _ [66,129,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20204

theorem m24061_20 : Upper (D 8) (R 8) [66,129,136,20] 13 :=
  permutation_upper _ _ _ [66,129,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20216

theorem m24061_33 : Upper (D 8) (R 8) [66,129,136,33] 13 :=
  permutation_upper _ _ _ [66,129,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20227

theorem m24061_36 : Upper (D 8) (R 8) [66,129,136,36] 13 :=
  permutation_upper _ _ _ [66,129,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20240

theorem m24061_48 : Upper (D 8) (R 8) [66,129,136,48] 13 :=
  permutation_upper _ _ _ [66,129,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20252

theorem m24061_65 : Upper (D 8) (R 8) [66,129,136,65] 13 :=
  permutation_upper _ _ _ [66,129,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20258

theorem m24061_68 : Upper (D 8) (R 8) [66,129,136,68] 13 :=
  permutation_upper _ _ _ [66,129,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20264

theorem m24061_80 : Upper (D 8) (R 8) [66,129,136,80] 13 :=
  permutation_upper _ _ _ [66,129,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20272

theorem m24061_96 : Upper (D 8) (R 8) [66,129,136,96] 13 :=
  permutation_upper _ _ _ [66,129,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20278

def r24061 : Route 9 := (fun mask => (mask,id))

def c24061 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u24061 : Upper (D 8) (R 8) [66,129,136] 13 := by
  apply FastRouting.sound _ _ [66,129,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r24061 c24061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24061_5
  · exact m24061_17
  · exact m24061_20
  · exact m24061_33
  · exact m24061_36
  · exact m24061_48
  · exact m24061_65
  · exact m24061_68
  · exact m24061_80
  · exact m24061_96
  · exact u20289
  · exact u20290
  · exact u20291
  · exact u20292
  · exact u20293

theorem m24062_5 : Upper (D 8) (R 8) [66,129,160,5] 13 :=
  permutation_upper _ _ _ [66,129,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20196

theorem m24062_17 : Upper (D 8) (R 8) [66,129,160,17] 13 :=
  permutation_upper _ _ _ [66,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20205

theorem m24062_20 : Upper (D 8) (R 8) [66,129,160,20] 13 :=
  permutation_upper _ _ _ [66,129,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20217

theorem m24062_33 : Upper (D 8) (R 8) [66,129,160,33] 13 :=
  permutation_upper _ _ _ [66,129,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20228

theorem m24062_36 : Upper (D 8) (R 8) [66,129,160,36] 13 :=
  permutation_upper _ _ _ [66,129,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20242

theorem m24062_48 : Upper (D 8) (R 8) [66,129,160,48] 13 :=
  permutation_upper _ _ _ [66,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20253

theorem m24062_65 : Upper (D 8) (R 8) [66,129,160,65] 13 :=
  permutation_upper _ _ _ [66,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20259

theorem m24062_68 : Upper (D 8) (R 8) [66,129,160,68] 13 :=
  permutation_upper _ _ _ [66,129,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20266

theorem m24062_80 : Upper (D 8) (R 8) [66,129,160,80] 13 :=
  permutation_upper _ _ _ [66,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20273

theorem m24062_96 : Upper (D 8) (R 8) [66,129,160,96] 13 :=
  permutation_upper _ _ _ [66,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20280

def r24062 : Route 9 := (fun mask => (mask,id))

def c24062 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u24062 : Upper (D 8) (R 8) [66,129,160] 13 := by
  apply FastRouting.sound _ _ [66,129,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r24062 c24062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24062_5
  · exact m24062_17
  · exact m24062_20
  · exact m24062_33
  · exact m24062_36
  · exact m24062_48
  · exact m24062_65
  · exact m24062_68
  · exact m24062_80
  · exact m24062_96
  · exact u20297
  · exact u20298
  · exact u20299
  · exact u20300
  · exact u20301

def b24063 : PairBound 9 := { available := 317, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 196 317 317 317 381 445 317), lower := (rows 67 131 196 8 16 32 64 128 256), losses := [] }

theorem u24063 : Upper (D 8) (R 8) [66,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24064 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 261 252 252 252 252 252 508), lower := (rows 67 131 261 8 16 32 64 128 256), losses := [] }

theorem u24064 : Upper (D 8) (R 8) [66,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24065_5 : Upper (D 8) (R 8) [66,129,264,5] 13 :=
  permutation_upper _ _ _ [66,129,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20197

theorem m24065_17 : Upper (D 8) (R 8) [66,129,264,17] 13 :=
  permutation_upper _ _ _ [66,129,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20206

theorem m24065_20 : Upper (D 8) (R 8) [66,129,264,20] 13 :=
  permutation_upper _ _ _ [66,129,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20220

theorem m24065_33 : Upper (D 8) (R 8) [66,129,264,33] 13 :=
  permutation_upper _ _ _ [66,129,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20229

theorem m24065_36 : Upper (D 8) (R 8) [66,129,264,36] 13 :=
  permutation_upper _ _ _ [66,129,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20245

theorem m24065_48 : Upper (D 8) (R 8) [66,129,264,48] 13 :=
  permutation_upper _ _ _ [66,129,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20254

theorem m24065_65 : Upper (D 8) (R 8) [66,129,264,65] 13 :=
  permutation_upper _ _ _ [66,129,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20260

theorem m24065_68 : Upper (D 8) (R 8) [66,129,264,68] 13 :=
  permutation_upper _ _ _ [66,129,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20268

theorem m24065_80 : Upper (D 8) (R 8) [66,129,264,80] 13 :=
  permutation_upper _ _ _ [66,129,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20274

theorem m24065_96 : Upper (D 8) (R 8) [66,129,264,96] 13 :=
  permutation_upper _ _ _ [66,129,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20282

theorem m24065_129 : Upper (D 8) (R 8) [66,129,264,129] 13 :=
  permutation_upper _ _ _ [66,129,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20286

theorem m24065_132 : Upper (D 8) (R 8) [66,129,264,132] 13 :=
  permutation_upper _ _ _ [66,129,136,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20290

theorem m24065_144 : Upper (D 8) (R 8) [66,129,264,144] 13 :=
  permutation_upper _ _ _ [66,129,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20294

theorem m24065_160 : Upper (D 8) (R 8) [66,129,264,160] 13 :=
  permutation_upper _ _ _ [66,129,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20298

theorem m24065_192 : Upper (D 8) (R 8) [66,129,264,192] 13 :=
  permutation_upper _ _ _ [66,129,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20302

def r24065 : Route 9 := (fun mask => (mask,id))

def c24065 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24065 : Upper (D 8) (R 8) [66,129,264] 13 := by
  apply FastRouting.sound _ _ [66,129,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24065 c24065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24065_5
  · exact m24065_17
  · exact m24065_20
  · exact m24065_33
  · exact m24065_36
  · exact m24065_48
  · exact m24065_65
  · exact m24065_68
  · exact m24065_80
  · exact m24065_96
  · exact m24065_129
  · exact m24065_132
  · exact m24065_144
  · exact m24065_160
  · exact m24065_192

theorem m24066_5 : Upper (D 8) (R 8) [66,129,288,5] 13 :=
  permutation_upper _ _ _ [66,129,9,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20198

theorem m24066_17 : Upper (D 8) (R 8) [66,129,288,17] 13 :=
  permutation_upper _ _ _ [66,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20207

theorem m24066_20 : Upper (D 8) (R 8) [66,129,288,20] 13 :=
  permutation_upper _ _ _ [66,129,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20221

theorem m24066_33 : Upper (D 8) (R 8) [66,129,288,33] 13 :=
  permutation_upper _ _ _ [66,129,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20230

theorem m24066_36 : Upper (D 8) (R 8) [66,129,288,36] 13 :=
  permutation_upper _ _ _ [66,129,40,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20247

theorem m24066_48 : Upper (D 8) (R 8) [66,129,288,48] 13 :=
  permutation_upper _ _ _ [66,129,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20255

theorem m24066_65 : Upper (D 8) (R 8) [66,129,288,65] 13 :=
  permutation_upper _ _ _ [66,129,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20261

theorem m24066_68 : Upper (D 8) (R 8) [66,129,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20270

theorem m24066_80 : Upper (D 8) (R 8) [66,129,288,80] 13 :=
  permutation_upper _ _ _ [66,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20275

theorem m24066_96 : Upper (D 8) (R 8) [66,129,288,96] 13 :=
  permutation_upper _ _ _ [66,129,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20284

theorem m24066_129 : Upper (D 8) (R 8) [66,129,288,129] 13 :=
  permutation_upper _ _ _ [66,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20287

theorem m24066_132 : Upper (D 8) (R 8) [66,129,288,132] 13 :=
  permutation_upper _ _ _ [66,129,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20292

theorem m24066_144 : Upper (D 8) (R 8) [66,129,288,144] 13 :=
  permutation_upper _ _ _ [66,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20295

theorem m24066_160 : Upper (D 8) (R 8) [66,129,288,160] 13 :=
  permutation_upper _ _ _ [66,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20300

theorem m24066_192 : Upper (D 8) (R 8) [66,129,288,192] 13 :=
  permutation_upper _ _ _ [66,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20303

def r24066 : Route 9 := (fun mask => (mask,id))

def c24066 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24066 : Upper (D 8) (R 8) [66,129,288] 13 := by
  apply FastRouting.sound _ _ [66,129,288] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24066 c24066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24066_5
  · exact m24066_17
  · exact m24066_20
  · exact m24066_33
  · exact m24066_36
  · exact m24066_48
  · exact m24066_65
  · exact m24066_68
  · exact m24066_80
  · exact m24066_96
  · exact m24066_129
  · exact m24066_132
  · exact m24066_144
  · exact m24066_160
  · exact m24066_192

theorem m24067_5 : Upper (D 8) (R 8) [66,129,320,5] 13 :=
  permutation_upper _ _ _ [66,129,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20199

theorem m24067_17 : Upper (D 8) (R 8) [66,129,320,17] 13 :=
  permutation_upper _ _ _ [66,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20208

theorem m24067_20 : Upper (D 8) (R 8) [66,129,320,20] 13 :=
  permutation_upper _ _ _ [66,129,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20222

theorem m24067_33 : Upper (D 8) (R 8) [66,129,320,33] 13 :=
  permutation_upper _ _ _ [66,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20231

theorem m24067_36 : Upper (D 8) (R 8) [66,129,320,36] 13 :=
  permutation_upper _ _ _ [66,129,40,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20248

theorem m24067_48 : Upper (D 8) (R 8) [66,129,320,48] 13 :=
  permutation_upper _ _ _ [66,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20256

theorem m24067_129 : Upper (D 8) (R 8) [66,129,320,129] 13 :=
  permutation_upper _ _ _ [66,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20288

theorem m24067_132 : Upper (D 8) (R 8) [66,129,320,132] 13 :=
  permutation_upper _ _ _ [66,129,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20293

theorem m24067_144 : Upper (D 8) (R 8) [66,129,320,144] 13 :=
  permutation_upper _ _ _ [66,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20296

theorem m24067_160 : Upper (D 8) (R 8) [66,129,320,160] 13 :=
  permutation_upper _ _ _ [66,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20301

def r24067 : Route 9 := (fun mask => (mask,id))

def c24067 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24067 : Upper (D 8) (R 8) [66,129,320] 13 := by
  apply FastRouting.sound _ _ [66,129,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24067 c24067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24067_5
  · exact m24067_17
  · exact m24067_20
  · exact m24067_33
  · exact m24067_36
  · exact m24067_48
  · exact m24067_129
  · exact m24067_132
  · exact m24067_144
  · exact m24067_160

theorem m24068_5 : Upper (D 8) (R 8) [66,129,384,5] 13 :=
  permutation_upper _ _ _ [66,129,9,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20200

theorem m24068_17 : Upper (D 8) (R 8) [66,129,384,17] 13 :=
  permutation_upper _ _ _ [66,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20209

theorem m24068_20 : Upper (D 8) (R 8) [66,129,384,20] 13 :=
  permutation_upper _ _ _ [66,129,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20223

theorem m24068_33 : Upper (D 8) (R 8) [66,129,384,33] 13 :=
  permutation_upper _ _ _ [66,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20232

theorem m24068_36 : Upper (D 8) (R 8) [66,129,384,36] 13 :=
  permutation_upper _ _ _ [66,129,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20249

theorem m24068_48 : Upper (D 8) (R 8) [66,129,384,48] 13 :=
  permutation_upper _ _ _ [66,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20257

theorem m24068_65 : Upper (D 8) (R 8) [66,129,384,65] 13 :=
  permutation_upper _ _ _ [66,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20262

theorem m24068_68 : Upper (D 8) (R 8) [66,129,384,68] 13 :=
  permutation_upper _ _ _ [66,129,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20271

theorem m24068_80 : Upper (D 8) (R 8) [66,129,384,80] 13 :=
  permutation_upper _ _ _ [66,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20276

theorem m24068_96 : Upper (D 8) (R 8) [66,129,384,96] 13 :=
  permutation_upper _ _ _ [66,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20285

def r24068 : Route 9 := (fun mask => (mask,id))

def c24068 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u24068 : Upper (D 8) (R 8) [66,129,384] 13 := by
  apply FastRouting.sound _ _ [66,129,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r24068 c24068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24068_5
  · exact m24068_17
  · exact m24068_20
  · exact m24068_33
  · exact m24068_36
  · exact m24068_48
  · exact m24068_65
  · exact m24068_68
  · exact m24068_80
  · exact m24068_96

def r24069 : Route 9 := (fun mask => (mask,id))

def c24069 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24069 : Upper (D 8) (R 8) [66,132,9] 13 := by
  apply FastRouting.sound _ _ [66,132,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24069 c24069
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20304
  · exact u20305
  · exact u20306
  · exact u20307
  · exact u20308
  · exact u20309
  · exact u20310
  · exact u20311
  · exact u20312
  · exact u20313
  · exact u20314
  · exact u20315
  · exact u20316
  · exact u20317
  · exact u20318

def r24070 : Route 9 := (fun mask => (mask,id))

def c24070 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24070 : Upper (D 8) (R 8) [66,132,24] 13 := by
  apply FastRouting.sound _ _ [66,132,24] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r24070 c24070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20319
  · exact u20320
  · exact u20321
  · exact u20322
  · exact u20323
  · exact u20324
  · exact u20325
  · exact u20326
  · exact u20327
  · exact u20328

def r24071 : Route 9 := (fun mask => (mask,id))

def c24071 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24071 : Upper (D 8) (R 8) [66,132,33] 13 := by
  apply FastRouting.sound _ _ [66,132,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24071 c24071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20329
  · exact u20330
  · exact u20331
  · exact u20332
  · exact u20333
  · exact u20334
  · exact u20335
  · exact u20336
  · exact u20337
  · exact u20338
  · exact u20339
  · exact u20340
  · exact u20341
  · exact u20342
  · exact u20343

def r24072 : Route 9 := (fun mask => (mask,id))

def c24072 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24072 : Upper (D 8) (R 8) [66,132,40] 13 := by
  apply FastRouting.sound _ _ [66,132,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24072 c24072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20344
  · exact u20345
  · exact u20346
  · exact u20347
  · exact u20348
  · exact u20349
  · exact u20350
  · exact u20351
  · exact u20352
  · exact u20353
  · exact u20354
  · exact u20355
  · exact u20356
  · exact u20357
  · exact u20358

def b24073 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 69 441 441 441 505 441 441), lower := (rows 67 134 69 8 16 32 64 128 256), losses := [] }

theorem u24073 : Upper (D 8) (R 8) [66,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24074 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 76 441 433 433 497 433 433), lower := (rows 67 134 76 8 16 32 64 128 256), losses := [] }

theorem u24074 : Upper (D 8) (R 8) [66,132,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24075 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 100 441 441 441 505 441 441), lower := (rows 67 134 100 8 16 32 64 128 256), losses := [] }

theorem u24075 : Upper (D 8) (R 8) [66,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24076 : PairBound 9 := { available := 377, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 133 377 377 377 377 505 377), lower := (rows 67 134 133 8 16 32 64 128 256), losses := [] }

theorem u24076 : Upper (D 8) (R 8) [66,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24077 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 140 377 369 369 369 497 369), lower := (rows 67 134 140 8 16 32 64 128 256), losses := [] }

theorem u24077 : Upper (D 8) (R 8) [66,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24078 : PairBound 9 := { available := 377, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 164 377 377 377 377 505 377), lower := (rows 67 134 164 8 16 32 64 128 256), losses := [] }

theorem u24078 : Upper (D 8) (R 8) [66,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24079 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 196 313 313 313 377 441 313), lower := (rows 67 134 196 8 16 32 64 128 256), losses := [] }

theorem u24079 : Upper (D 8) (R 8) [66,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24080 : Route 9 := (fun mask => (mask,id))

def c24080 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24080 : Upper (D 8) (R 8) [66,132,257] 13 := by
  apply FastRouting.sound _ _ [66,132,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24080 c24080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20359
  · exact u20360
  · exact u20361
  · exact u20362
  · exact u20363
  · exact u20364
  · exact u20365
  · exact u20366
  · exact u20367
  · exact u20368

def r24081 : Route 9 := (fun mask => (mask,id))

def c24081 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24081 : Upper (D 8) (R 8) [66,132,264] 13 := by
  apply FastRouting.sound _ _ [66,132,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24081 c24081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20369
  · exact u20370
  · exact u20371
  · exact u20372
  · exact u20373
  · exact u20374
  · exact u20375
  · exact u20376
  · exact u20377
  · exact u20378

def r24082 : Route 9 := (fun mask => (mask,id))

def c24082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24082 : Upper (D 8) (R 8) [66,132,288] 13 := by
  apply FastRouting.sound _ _ [66,132,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24082 c24082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20379
  · exact u20380
  · exact u20381
  · exact u20382
  · exact u20383
  · exact u20384
  · exact u20385
  · exact u20386
  · exact u20387
  · exact u20388

def b24083 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 324 185 185 185 249 185 441), lower := (rows 67 134 324 8 16 32 64 128 256), losses := [] }

theorem u24083 : Upper (D 8) (R 8) [66,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24084 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 121, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 388 121 121 121 121 249 377), lower := (rows 67 134 388 8 16 32 64 128 256), losses := [] }

theorem u24084 : Upper (D 8) (R 8) [66,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24085 : Route 9 := (fun mask => (mask,id))

def c24085 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24085 : Upper (D 8) (R 8) [66,160,9] 13 := by
  apply FastRouting.sound _ _ [66,160,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24085 c24085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20389
  · exact u20390
  · exact u20391
  · exact u20392
  · exact u20393
  · exact u20394
  · exact u20395
  · exact u20396
  · exact u20397
  · exact u20398
  · exact u20399
  · exact u20400
  · exact u20401
  · exact u20402
  · exact u20403
  · exact u20404
  · exact u20405
  · exact u20406
  · exact u20407
  · exact u20408
  · exact u20409

theorem m24086_5 : Upper (D 8) (R 8) [66,160,24,5] 13 :=
  permutation_upper _ _ _ [66,160,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20391

def r24086 : Route 9 := (fun mask => (mask,id))

def c24086 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24086 : Upper (D 8) (R 8) [66,160,24] 13 := by
  apply FastRouting.sound _ _ [66,160,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r24086 c24086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24086_5
  · exact u20421
  · exact u20422
  · exact u20423
  · exact u20424
  · exact u20425
  · exact u20426
  · exact u20427
  · exact u20428
  · exact u20429
  · exact u20430
  · exact u20431
  · exact u20432
  · exact u20433
  · exact u20434

theorem m24087_5 : Upper (D 8) (R 8) [66,160,33,5] 13 :=
  permutation_upper _ _ _ [66,160,9,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20392

theorem m24087_17 : Upper (D 8) (R 8) [66,160,33,17] 13 :=
  permutation_upper _ _ _ [66,160,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20410

theorem m24087_20 : Upper (D 8) (R 8) [66,160,33,20] 13 :=
  permutation_upper _ _ _ [66,160,24,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20421

def r24087 : Route 9 := (fun mask => (mask,id))

def c24087 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24087 : Upper (D 8) (R 8) [66,160,33] 13 := by
  apply FastRouting.sound _ _ [66,160,33] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24087 c24087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24087_5
  · exact m24087_17
  · exact m24087_20
  · exact u20435
  · exact u20436
  · exact u20437
  · exact u20438
  · exact u20439
  · exact u20440
  · exact u20441
  · exact u20442
  · exact u20443
  · exact u20444
  · exact u20445
  · exact u20446
  · exact u20447
  · exact u20448
  · exact u20449
  · exact u20450
  · exact u20451
  · exact u20452

theorem m24088_5 : Upper (D 8) (R 8) [66,160,40,5] 13 :=
  permutation_upper _ _ _ [66,160,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20393

theorem m24088_17 : Upper (D 8) (R 8) [66,160,40,17] 13 :=
  permutation_upper _ _ _ [66,160,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20411

theorem m24088_20 : Upper (D 8) (R 8) [66,160,40,20] 13 :=
  permutation_upper _ _ _ [66,160,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20422

theorem m24088_33 : Upper (D 8) (R 8) [66,160,40,33] 13 :=
  permutation_upper _ _ _ [66,160,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20436

def r24088 : Route 9 := (fun mask => (mask,id))

def c24088 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24088 : Upper (D 8) (R 8) [66,160,40] 13 := by
  apply FastRouting.sound _ _ [66,160,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24088 c24088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24088_5
  · exact m24088_17
  · exact m24088_20
  · exact m24088_33
  · exact u20453
  · exact u20454
  · exact u20455
  · exact u20456
  · exact u20457
  · exact u20458
  · exact u20459
  · exact u20460
  · exact u20461
  · exact u20462
  · exact u20463
  · exact u20464
  · exact u20465
  · exact u20466
  · exact u20467
  · exact u20468
  · exact u20469

def b24089 : PairBound 9 := { available := 445, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 445 445 445 509 445 445), lower := (rows 67 162 69 8 16 32 64 128 256), losses := [] }

theorem u24089 : Upper (D 8) (R 8) [66,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24090_5 : Upper (D 8) (R 8) [66,160,72,5] 13 :=
  permutation_upper _ _ _ [66,160,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20396

theorem m24090_17 : Upper (D 8) (R 8) [66,160,72,17] 13 :=
  permutation_upper _ _ _ [66,160,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20412

theorem m24090_20 : Upper (D 8) (R 8) [66,160,72,20] 13 :=
  permutation_upper _ _ _ [66,160,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20424

theorem m24090_33 : Upper (D 8) (R 8) [66,160,72,33] 13 :=
  permutation_upper _ _ _ [66,160,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20439

theorem m24090_36 : Upper (D 8) (R 8) [66,160,72,36] 13 :=
  permutation_upper _ _ _ [66,160,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20456

theorem m24090_48 : Upper (D 8) (R 8) [66,160,72,48] 13 :=
  permutation_upper _ _ _ [66,160,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20470

def r24090 : Route 9 := (fun mask => (mask,id))

def c24090 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u24090 : Upper (D 8) (R 8) [66,160,72] 13 := by
  apply FastRouting.sound _ _ [66,160,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r24090 c24090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24090_5
  · exact m24090_17
  · exact m24090_20
  · exact m24090_33
  · exact m24090_36
  · exact m24090_48
  · exact u20484
  · exact u20485
  · exact u20486
  · exact u20487
  · exact u20488
  · exact u20489
  · exact u20490
  · exact u20491
  · exact u20492

theorem m24091_5 : Upper (D 8) (R 8) [66,160,96,5] 13 :=
  permutation_upper _ _ _ [66,160,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20398

theorem m24091_17 : Upper (D 8) (R 8) [66,160,96,17] 13 :=
  permutation_upper _ _ _ [66,160,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20413

theorem m24091_20 : Upper (D 8) (R 8) [66,160,96,20] 13 :=
  permutation_upper _ _ _ [66,160,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20425

theorem m24091_33 : Upper (D 8) (R 8) [66,160,96,33] 13 :=
  permutation_upper _ _ _ [66,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20441

theorem m24091_36 : Upper (D 8) (R 8) [66,160,96,36] 13 :=
  permutation_upper _ _ _ [66,160,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20458

theorem m24091_48 : Upper (D 8) (R 8) [66,160,96,48] 13 :=
  permutation_upper _ _ _ [66,160,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20471

def r24091 : Route 9 := (fun mask => (mask,id))

def c24091 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u24091 : Upper (D 8) (R 8) [66,160,96] 13 := by
  apply FastRouting.sound _ _ [66,160,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r24091 c24091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24091_5
  · exact m24091_17
  · exact m24091_20
  · exact m24091_33
  · exact m24091_36
  · exact m24091_48
  · exact u20498
  · exact u20499
  · exact u20500
  · exact u20501
  · exact u20502
  · exact u20503
  · exact u20504
  · exact u20505
  · exact u20506

def b24092 : PairBound 9 := { available := 381, camps := [{ cop := 2, region := 376, targets := 128 }], pairs := [(3,7)], upper := (rows 67 162 133 381 381 381 381 509 381), lower := (rows 67 162 133 8 16 32 64 128 256), losses := [] }

theorem u24092 : Upper (D 8) (R 8) [66,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24093_5 : Upper (D 8) (R 8) [66,160,136,5] 13 :=
  permutation_upper _ _ _ [66,160,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20400

theorem m24093_17 : Upper (D 8) (R 8) [66,160,136,17] 13 :=
  permutation_upper _ _ _ [66,160,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20414

theorem m24093_20 : Upper (D 8) (R 8) [66,160,136,20] 13 :=
  permutation_upper _ _ _ [66,160,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20427

theorem m24093_33 : Upper (D 8) (R 8) [66,160,136,33] 13 :=
  permutation_upper _ _ _ [66,160,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20443

theorem m24093_36 : Upper (D 8) (R 8) [66,160,136,36] 13 :=
  permutation_upper _ _ _ [66,160,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20460

theorem m24093_48 : Upper (D 8) (R 8) [66,160,136,48] 13 :=
  permutation_upper _ _ _ [66,160,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20472

theorem m24093_65 : Upper (D 8) (R 8) [66,160,136,65] 13 :=
  permutation_upper _ _ _ [66,160,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20479

theorem m24093_68 : Upper (D 8) (R 8) [66,160,136,68] 13 :=
  permutation_upper _ _ _ [66,160,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20485

theorem m24093_80 : Upper (D 8) (R 8) [66,160,136,80] 13 :=
  permutation_upper _ _ _ [66,160,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20493

theorem m24093_96 : Upper (D 8) (R 8) [66,160,136,96] 13 :=
  permutation_upper _ _ _ [66,160,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20499

def r24093 : Route 9 := (fun mask => (mask,id))

def c24093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u24093 : Upper (D 8) (R 8) [66,160,136] 13 := by
  apply FastRouting.sound _ _ [66,160,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r24093 c24093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24093_5
  · exact m24093_17
  · exact m24093_20
  · exact m24093_33
  · exact m24093_36
  · exact m24093_48
  · exact m24093_65
  · exact m24093_68
  · exact m24093_80
  · exact m24093_96
  · exact u20511
  · exact u20512
  · exact u20513
  · exact u20514
  · exact u20515

def b24094 : PairBound 9 := { available := 381, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 164 381 381 381 381 509 381), lower := (rows 67 162 164 8 16 32 64 128 256), losses := [] }

theorem u24094 : Upper (D 8) (R 8) [66,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24095_5 : Upper (D 8) (R 8) [66,160,192,5] 13 :=
  permutation_upper _ _ _ [66,160,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20403

theorem m24095_17 : Upper (D 8) (R 8) [66,160,192,17] 13 :=
  permutation_upper _ _ _ [66,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20415

theorem m24095_20 : Upper (D 8) (R 8) [66,160,192,20] 13 :=
  permutation_upper _ _ _ [66,160,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20429

theorem m24095_33 : Upper (D 8) (R 8) [66,160,192,33] 13 :=
  permutation_upper _ _ _ [66,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20446

theorem m24095_36 : Upper (D 8) (R 8) [66,160,192,36] 13 :=
  permutation_upper _ _ _ [66,160,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20463

theorem m24095_48 : Upper (D 8) (R 8) [66,160,192,48] 13 :=
  permutation_upper _ _ _ [66,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20473

def r24095 : Route 9 := (fun mask => (mask,id))

def c24095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u24095 : Upper (D 8) (R 8) [66,160,192] 13 := by
  apply FastRouting.sound _ _ [66,160,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r24095 c24095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24095_5
  · exact m24095_17
  · exact m24095_20
  · exact m24095_33
  · exact m24095_36
  · exact m24095_48
  · exact u20524
  · exact u20525
  · exact u20526
  · exact u20527

theorem m24096_5 : Upper (D 8) (R 8) [66,160,257,5] 13 :=
  permutation_upper _ _ _ [66,160,9,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20404

theorem m24096_17 : Upper (D 8) (R 8) [66,160,257,17] 13 :=
  permutation_upper _ _ _ [66,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20416

theorem m24096_20 : Upper (D 8) (R 8) [66,160,257,20] 13 :=
  permutation_upper _ _ _ [66,160,24,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20430

theorem m24096_33 : Upper (D 8) (R 8) [66,160,257,33] 13 :=
  permutation_upper _ _ _ [66,160,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20447

theorem m24096_36 : Upper (D 8) (R 8) [66,160,257,36] 13 :=
  permutation_upper _ _ _ [66,160,40,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20464

theorem m24096_48 : Upper (D 8) (R 8) [66,160,257,48] 13 :=
  permutation_upper _ _ _ [66,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20474

theorem m24096_65 : Upper (D 8) (R 8) [66,160,257,65] 13 :=
  permutation_upper _ _ _ [66,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20480

theorem m24096_68 : Upper (D 8) (R 8) [66,160,257,68] 13 :=
  permutation_upper _ _ _ [66,160,72,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20488

theorem m24096_80 : Upper (D 8) (R 8) [66,160,257,80] 13 :=
  permutation_upper _ _ _ [66,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20494

theorem m24096_96 : Upper (D 8) (R 8) [66,160,257,96] 13 :=
  permutation_upper _ _ _ [66,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20502

theorem m24096_129 : Upper (D 8) (R 8) [66,160,257,129] 13 :=
  permutation_upper _ _ _ [66,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20507

theorem m24096_132 : Upper (D 8) (R 8) [66,160,257,132] 13 :=
  permutation_upper _ _ _ [66,160,136,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20511

theorem m24096_144 : Upper (D 8) (R 8) [66,160,257,144] 13 :=
  permutation_upper _ _ _ [66,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20516

theorem m24096_160 : Upper (D 8) (R 8) [66,160,257,160] 13 :=
  permutation_upper _ _ _ [66,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20520

theorem m24096_192 : Upper (D 8) (R 8) [66,160,257,192] 13 :=
  permutation_upper _ _ _ [66,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20524

def r24096 : Route 9 := (fun mask => (mask,id))

def c24096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24096 : Upper (D 8) (R 8) [66,160,257] 13 := by
  apply FastRouting.sound _ _ [66,160,257] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24096 c24096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24096_5
  · exact m24096_17
  · exact m24096_20
  · exact m24096_33
  · exact m24096_36
  · exact m24096_48
  · exact m24096_65
  · exact m24096_68
  · exact m24096_80
  · exact m24096_96
  · exact m24096_129
  · exact m24096_132
  · exact m24096_144
  · exact m24096_160
  · exact m24096_192

theorem m24097_5 : Upper (D 8) (R 8) [66,160,264,5] 13 :=
  permutation_upper _ _ _ [66,160,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20405

theorem m24097_17 : Upper (D 8) (R 8) [66,160,264,17] 13 :=
  permutation_upper _ _ _ [66,160,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20417

theorem m24097_20 : Upper (D 8) (R 8) [66,160,264,20] 13 :=
  permutation_upper _ _ _ [66,160,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20431

theorem m24097_33 : Upper (D 8) (R 8) [66,160,264,33] 13 :=
  permutation_upper _ _ _ [66,160,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20448

theorem m24097_36 : Upper (D 8) (R 8) [66,160,264,36] 13 :=
  permutation_upper _ _ _ [66,160,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20465

theorem m24097_48 : Upper (D 8) (R 8) [66,160,264,48] 13 :=
  permutation_upper _ _ _ [66,160,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20475

theorem m24097_65 : Upper (D 8) (R 8) [66,160,264,65] 13 :=
  permutation_upper _ _ _ [66,160,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20481

theorem m24097_68 : Upper (D 8) (R 8) [66,160,264,68] 13 :=
  permutation_upper _ _ _ [66,160,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20489

theorem m24097_80 : Upper (D 8) (R 8) [66,160,264,80] 13 :=
  permutation_upper _ _ _ [66,160,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20495

theorem m24097_96 : Upper (D 8) (R 8) [66,160,264,96] 13 :=
  permutation_upper _ _ _ [66,160,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20503

theorem m24097_129 : Upper (D 8) (R 8) [66,160,264,129] 13 :=
  permutation_upper _ _ _ [66,160,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20508

theorem m24097_132 : Upper (D 8) (R 8) [66,160,264,132] 13 :=
  permutation_upper _ _ _ [66,160,136,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20512

theorem m24097_144 : Upper (D 8) (R 8) [66,160,264,144] 13 :=
  permutation_upper _ _ _ [66,160,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20517

theorem m24097_160 : Upper (D 8) (R 8) [66,160,264,160] 13 :=
  permutation_upper _ _ _ [66,160,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20521

theorem m24097_192 : Upper (D 8) (R 8) [66,160,264,192] 13 :=
  permutation_upper _ _ _ [66,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20525

def r24097 : Route 9 := (fun mask => (mask,id))

def c24097 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24097 : Upper (D 8) (R 8) [66,160,264] 13 := by
  apply FastRouting.sound _ _ [66,160,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24097 c24097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24097_5
  · exact m24097_17
  · exact m24097_20
  · exact m24097_33
  · exact m24097_36
  · exact m24097_48
  · exact m24097_65
  · exact m24097_68
  · exact m24097_80
  · exact m24097_96
  · exact m24097_129
  · exact m24097_132
  · exact m24097_144
  · exact m24097_160
  · exact m24097_192

theorem m24098_5 : Upper (D 8) (R 8) [66,160,288,5] 13 :=
  permutation_upper _ _ _ [66,160,9,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20407

theorem m24098_17 : Upper (D 8) (R 8) [66,160,288,17] 13 :=
  permutation_upper _ _ _ [66,160,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20418

theorem m24098_20 : Upper (D 8) (R 8) [66,160,288,20] 13 :=
  permutation_upper _ _ _ [66,160,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20432

theorem m24098_33 : Upper (D 8) (R 8) [66,160,288,33] 13 :=
  permutation_upper _ _ _ [66,160,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20450

theorem m24098_36 : Upper (D 8) (R 8) [66,160,288,36] 13 :=
  permutation_upper _ _ _ [66,160,40,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20467

theorem m24098_48 : Upper (D 8) (R 8) [66,160,288,48] 13 :=
  permutation_upper _ _ _ [66,160,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20476

theorem m24098_65 : Upper (D 8) (R 8) [66,160,288,65] 13 :=
  permutation_upper _ _ _ [66,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20482

theorem m24098_68 : Upper (D 8) (R 8) [66,160,288,68] 13 :=
  permutation_upper _ _ _ [66,160,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20491

theorem m24098_80 : Upper (D 8) (R 8) [66,160,288,80] 13 :=
  permutation_upper _ _ _ [66,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20496

theorem m24098_96 : Upper (D 8) (R 8) [66,160,288,96] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20505

theorem m24098_129 : Upper (D 8) (R 8) [66,160,288,129] 13 :=
  permutation_upper _ _ _ [66,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20509

theorem m24098_132 : Upper (D 8) (R 8) [66,160,288,132] 13 :=
  permutation_upper _ _ _ [66,160,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20514

theorem m24098_144 : Upper (D 8) (R 8) [66,160,288,144] 13 :=
  permutation_upper _ _ _ [66,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20518

theorem m24098_160 : Upper (D 8) (R 8) [66,160,288,160] 13 :=
  permutation_upper _ _ _ [66,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20522

theorem m24098_192 : Upper (D 8) (R 8) [66,160,288,192] 13 :=
  permutation_upper _ _ _ [66,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20527

def r24098 : Route 9 := (fun mask => (mask,id))

def c24098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24098 : Upper (D 8) (R 8) [66,160,288] 13 := by
  apply FastRouting.sound _ _ [66,160,288] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24098 c24098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24098_5
  · exact m24098_17
  · exact m24098_20
  · exact m24098_33
  · exact m24098_36
  · exact m24098_48
  · exact m24098_65
  · exact m24098_68
  · exact m24098_80
  · exact m24098_96
  · exact m24098_129
  · exact m24098_132
  · exact m24098_144
  · exact m24098_160
  · exact m24098_192

theorem m24099_5 : Upper (D 8) (R 8) [66,160,320,5] 13 :=
  permutation_upper _ _ _ [66,160,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20408

theorem m24099_17 : Upper (D 8) (R 8) [66,160,320,17] 13 :=
  permutation_upper _ _ _ [66,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20419

theorem m24099_20 : Upper (D 8) (R 8) [66,160,320,20] 13 :=
  permutation_upper _ _ _ [66,160,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20433

theorem m24099_33 : Upper (D 8) (R 8) [66,160,320,33] 13 :=
  permutation_upper _ _ _ [66,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20451

theorem m24099_36 : Upper (D 8) (R 8) [66,160,320,36] 13 :=
  permutation_upper _ _ _ [66,160,40,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20468

theorem m24099_48 : Upper (D 8) (R 8) [66,160,320,48] 13 :=
  permutation_upper _ _ _ [66,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20477

theorem m24099_129 : Upper (D 8) (R 8) [66,160,320,129] 13 :=
  permutation_upper _ _ _ [66,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20510

theorem m24099_132 : Upper (D 8) (R 8) [66,160,320,132] 13 :=
  permutation_upper _ _ _ [66,160,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20515

theorem m24099_144 : Upper (D 8) (R 8) [66,160,320,144] 13 :=
  permutation_upper _ _ _ [66,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20519

theorem m24099_160 : Upper (D 8) (R 8) [66,160,320,160] 13 :=
  permutation_upper _ _ _ [66,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20523

def r24099 : Route 9 := (fun mask => (mask,id))

def c24099 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24099 : Upper (D 8) (R 8) [66,160,320] 13 := by
  apply FastRouting.sound _ _ [66,160,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24099 c24099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24099_5
  · exact m24099_17
  · exact m24099_20
  · exact m24099_33
  · exact m24099_36
  · exact m24099_48
  · exact m24099_129
  · exact m24099_132
  · exact m24099_144
  · exact m24099_160

theorem m24100_5 : Upper (D 8) (R 8) [66,160,384,5] 13 :=
  permutation_upper _ _ _ [66,160,9,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20409

theorem m24100_17 : Upper (D 8) (R 8) [66,160,384,17] 13 :=
  permutation_upper _ _ _ [66,160,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20420

theorem m24100_20 : Upper (D 8) (R 8) [66,160,384,20] 13 :=
  permutation_upper _ _ _ [66,160,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20434

theorem m24100_33 : Upper (D 8) (R 8) [66,160,384,33] 13 :=
  permutation_upper _ _ _ [66,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20452

theorem m24100_36 : Upper (D 8) (R 8) [66,160,384,36] 13 :=
  permutation_upper _ _ _ [66,160,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20469

theorem m24100_48 : Upper (D 8) (R 8) [66,160,384,48] 13 :=
  permutation_upper _ _ _ [66,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20478

theorem m24100_65 : Upper (D 8) (R 8) [66,160,384,65] 13 :=
  permutation_upper _ _ _ [66,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20483

theorem m24100_68 : Upper (D 8) (R 8) [66,160,384,68] 13 :=
  permutation_upper _ _ _ [66,160,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20492

theorem m24100_80 : Upper (D 8) (R 8) [66,160,384,80] 13 :=
  permutation_upper _ _ _ [66,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20497

theorem m24100_96 : Upper (D 8) (R 8) [66,160,384,96] 13 :=
  permutation_upper _ _ _ [66,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20506

def r24100 : Route 9 := (fun mask => (mask,id))

def c24100 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u24100 : Upper (D 8) (R 8) [66,160,384] 13 := by
  apply FastRouting.sound _ _ [66,160,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r24100 c24100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24100_5
  · exact m24100_17
  · exact m24100_20
  · exact m24100_33
  · exact m24100_36
  · exact m24100_48
  · exact m24100_65
  · exact m24100_68
  · exact m24100_80
  · exact m24100_96

def b24101 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 252 244 244 244 244 500), lower := (rows 67 259 13 8 16 32 64 128 256), losses := [] }

theorem u24101 : Upper (D 8) (R 8) [66,257,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24102_5 : Upper (D 8) (R 8) [66,257,24,5] 13 :=
  permutation_upper _ _ _ [66,257,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20528

def r24102 : Route 9 := (fun mask => (mask,id))

def c24102 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24102 : Upper (D 8) (R 8) [66,257,24] 13 := by
  apply FastRouting.sound _ _ [66,257,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r24102 c24102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24102_5
  · exact u20541
  · exact u20542
  · exact u20543
  · exact u20544
  · exact u20545
  · exact u20546
  · exact u20547
  · exact u20548
  · exact u20549

def b24103 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 252 252 252 252 252 508), lower := (rows 67 259 37 8 16 32 64 128 256), losses := [] }

theorem u24103 : Upper (D 8) (R 8) [66,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24104_5 : Upper (D 8) (R 8) [66,257,40,5] 13 :=
  permutation_upper _ _ _ [66,257,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20529

theorem m24104_17 : Upper (D 8) (R 8) [66,257,40,17] 13 :=
  permutation_upper _ _ _ [66,257,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20535

theorem m24104_20 : Upper (D 8) (R 8) [66,257,40,20] 13 :=
  permutation_upper _ _ _ [66,257,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20542

theorem m24104_33 : Upper (D 8) (R 8) [66,257,40,33] 13 :=
  permutation_upper _ _ _ [66,257,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20550

def r24104 : Route 9 := (fun mask => (mask,id))

def c24104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24104 : Upper (D 8) (R 8) [66,257,40] 13 := by
  apply FastRouting.sound _ _ [66,257,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24104 c24104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24104_5
  · exact m24104_17
  · exact m24104_20
  · exact m24104_33
  · exact u20556
  · exact u20557
  · exact u20558
  · exact u20559
  · exact u20560
  · exact u20561
  · exact u20562
  · exact u20563
  · exact u20564
  · exact u20565
  · exact u20566

def b24105 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 69 188 188 188 252 188 444), lower := (rows 67 259 69 8 16 32 64 128 256), losses := [] }

theorem u24105 : Upper (D 8) (R 8) [66,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24106_5 : Upper (D 8) (R 8) [66,257,72,5] 13 :=
  permutation_upper _ _ _ [66,257,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20530

theorem m24106_17 : Upper (D 8) (R 8) [66,257,72,17] 13 :=
  permutation_upper _ _ _ [66,257,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20536

theorem m24106_20 : Upper (D 8) (R 8) [66,257,72,20] 13 :=
  permutation_upper _ _ _ [66,257,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20544

theorem m24106_33 : Upper (D 8) (R 8) [66,257,72,33] 13 :=
  permutation_upper _ _ _ [66,257,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20551

theorem m24106_36 : Upper (D 8) (R 8) [66,257,72,36] 13 :=
  permutation_upper _ _ _ [66,257,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20559

theorem m24106_48 : Upper (D 8) (R 8) [66,257,72,48] 13 :=
  permutation_upper _ _ _ [66,257,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20567

def r24106 : Route 9 := (fun mask => (mask,id))

def c24106 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24106 : Upper (D 8) (R 8) [66,257,72] 13 := by
  apply FastRouting.sound _ _ [66,257,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24106 c24106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24106_5
  · exact m24106_17
  · exact m24106_20
  · exact m24106_33
  · exact m24106_36
  · exact m24106_48
  · exact u20574
  · exact u20575
  · exact u20576
  · exact u20577

theorem m24107_5 : Upper (D 8) (R 8) [66,257,96,5] 13 :=
  permutation_upper _ _ _ [66,257,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20531

theorem m24107_17 : Upper (D 8) (R 8) [66,257,96,17] 13 :=
  permutation_upper _ _ _ [66,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20537

theorem m24107_20 : Upper (D 8) (R 8) [66,257,96,20] 13 :=
  permutation_upper _ _ _ [66,257,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20545

theorem m24107_33 : Upper (D 8) (R 8) [66,257,96,33] 13 :=
  permutation_upper _ _ _ [66,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20552

theorem m24107_36 : Upper (D 8) (R 8) [66,257,96,36] 13 :=
  permutation_upper _ _ _ [66,257,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20561

theorem m24107_48 : Upper (D 8) (R 8) [66,257,96,48] 13 :=
  permutation_upper _ _ _ [66,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20568

def r24107 : Route 9 := (fun mask => (mask,id))

def c24107 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24107 : Upper (D 8) (R 8) [66,257,96] 13 := by
  apply FastRouting.sound _ _ [66,257,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24107 c24107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24107_5
  · exact m24107_17
  · exact m24107_20
  · exact m24107_33
  · exact m24107_36
  · exact m24107_48
  · exact u20580
  · exact u20581
  · exact u20582
  · exact u20583

def b24108 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 133 252 252 252 252 252 508), lower := (rows 67 259 133 8 16 32 64 128 256), losses := [] }

theorem u24108 : Upper (D 8) (R 8) [66,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24109_5 : Upper (D 8) (R 8) [66,257,136,5] 13 :=
  permutation_upper _ _ _ [66,257,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20532

theorem m24109_17 : Upper (D 8) (R 8) [66,257,136,17] 13 :=
  permutation_upper _ _ _ [66,257,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20538

theorem m24109_20 : Upper (D 8) (R 8) [66,257,136,20] 13 :=
  permutation_upper _ _ _ [66,257,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20547

theorem m24109_33 : Upper (D 8) (R 8) [66,257,136,33] 13 :=
  permutation_upper _ _ _ [66,257,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20553

theorem m24109_36 : Upper (D 8) (R 8) [66,257,136,36] 13 :=
  permutation_upper _ _ _ [66,257,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20563

theorem m24109_48 : Upper (D 8) (R 8) [66,257,136,48] 13 :=
  permutation_upper _ _ _ [66,257,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20569

theorem m24109_65 : Upper (D 8) (R 8) [66,257,136,65] 13 :=
  permutation_upper _ _ _ [66,257,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20572

theorem m24109_68 : Upper (D 8) (R 8) [66,257,136,68] 13 :=
  permutation_upper _ _ _ [66,257,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20575

theorem m24109_80 : Upper (D 8) (R 8) [66,257,136,80] 13 :=
  permutation_upper _ _ _ [66,257,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20578

theorem m24109_96 : Upper (D 8) (R 8) [66,257,136,96] 13 :=
  permutation_upper _ _ _ [66,257,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20581

theorem m24109_129 : Upper (D 8) (R 8) [66,257,136,129] 13 :=
  permutation_upper _ _ _ [66,257,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20584

def r24109 : Route 9 := (fun mask => (mask,id))

def c24109 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24109 : Upper (D 8) (R 8) [66,257,136] 13 := by
  apply FastRouting.sound _ _ [66,257,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24109 c24109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24109_5
  · exact m24109_17
  · exact m24109_20
  · exact m24109_33
  · exact m24109_36
  · exact m24109_48
  · exact m24109_65
  · exact m24109_68
  · exact m24109_80
  · exact m24109_96
  · exact m24109_129
  · exact u20587
  · exact u20588
  · exact u20589
  · exact u20590

theorem m24110_5 : Upper (D 8) (R 8) [66,257,160,5] 13 :=
  permutation_upper _ _ _ [66,257,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20533

theorem m24110_17 : Upper (D 8) (R 8) [66,257,160,17] 13 :=
  permutation_upper _ _ _ [66,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20539

theorem m24110_20 : Upper (D 8) (R 8) [66,257,160,20] 13 :=
  permutation_upper _ _ _ [66,257,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20548

theorem m24110_33 : Upper (D 8) (R 8) [66,257,160,33] 13 :=
  permutation_upper _ _ _ [66,257,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20554

theorem m24110_36 : Upper (D 8) (R 8) [66,257,160,36] 13 :=
  permutation_upper _ _ _ [66,257,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20565

theorem m24110_48 : Upper (D 8) (R 8) [66,257,160,48] 13 :=
  permutation_upper _ _ _ [66,257,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20570

theorem m24110_65 : Upper (D 8) (R 8) [66,257,160,65] 13 :=
  permutation_upper _ _ _ [66,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20573

theorem m24110_68 : Upper (D 8) (R 8) [66,257,160,68] 13 :=
  permutation_upper _ _ _ [66,257,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20577

theorem m24110_80 : Upper (D 8) (R 8) [66,257,160,80] 13 :=
  permutation_upper _ _ _ [66,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20579

theorem m24110_96 : Upper (D 8) (R 8) [66,257,160,96] 13 :=
  permutation_upper _ _ _ [66,257,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20583

theorem m24110_129 : Upper (D 8) (R 8) [66,257,160,129] 13 :=
  permutation_upper _ _ _ [66,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20585

theorem m24110_132 : Upper (D 8) (R 8) [66,257,160,132] 13 :=
  permutation_upper _ _ _ [66,257,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20589

theorem m24110_144 : Upper (D 8) (R 8) [66,257,160,144] 13 :=
  permutation_upper _ _ _ [66,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20591

def r24110 : Route 9 := (fun mask => (mask,id))

def c24110 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24110 : Upper (D 8) (R 8) [66,257,160] 13 := by
  apply FastRouting.sound _ _ [66,257,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24110 c24110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24110_5
  · exact m24110_17
  · exact m24110_20
  · exact m24110_33
  · exact m24110_36
  · exact m24110_48
  · exact m24110_65
  · exact m24110_68
  · exact m24110_80
  · exact m24110_96
  · exact m24110_129
  · exact m24110_132
  · exact m24110_144
  · exact u20593
  · exact u20594

theorem m24111_5 : Upper (D 8) (R 8) [66,257,192,5] 13 :=
  permutation_upper _ _ _ [66,257,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20534

theorem m24111_17 : Upper (D 8) (R 8) [66,257,192,17] 13 :=
  permutation_upper _ _ _ [66,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20540

theorem m24111_20 : Upper (D 8) (R 8) [66,257,192,20] 13 :=
  permutation_upper _ _ _ [66,257,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20549

theorem m24111_33 : Upper (D 8) (R 8) [66,257,192,33] 13 :=
  permutation_upper _ _ _ [66,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20555

theorem m24111_36 : Upper (D 8) (R 8) [66,257,192,36] 13 :=
  permutation_upper _ _ _ [66,257,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20566

theorem m24111_48 : Upper (D 8) (R 8) [66,257,192,48] 13 :=
  permutation_upper _ _ _ [66,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20571

theorem m24111_129 : Upper (D 8) (R 8) [66,257,192,129] 13 :=
  permutation_upper _ _ _ [66,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20586

theorem m24111_132 : Upper (D 8) (R 8) [66,257,192,132] 13 :=
  permutation_upper _ _ _ [66,257,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20590

theorem m24111_144 : Upper (D 8) (R 8) [66,257,192,144] 13 :=
  permutation_upper _ _ _ [66,257,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20592

theorem m24111_160 : Upper (D 8) (R 8) [66,257,192,160] 13 :=
  permutation_upper _ _ _ [66,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20594

def r24111 : Route 9 := (fun mask => (mask,id))

def c24111 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24111 : Upper (D 8) (R 8) [66,257,192] 13 := by
  apply FastRouting.sound _ _ [66,257,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24111 c24111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24111_5
  · exact m24111_17
  · exact m24111_20
  · exact m24111_33
  · exact m24111_36
  · exact m24111_48
  · exact m24111_129
  · exact m24111_132
  · exact m24111_144
  · exact m24111_160

def r24112 : Route 9 := (fun mask => (mask,id))

def c24112 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24112 : Upper (D 8) (R 8) [66,260,9] 13 := by
  apply FastRouting.sound _ _ [66,260,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24112 c24112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20595
  · exact u20596
  · exact u20597
  · exact u20598
  · exact u20599
  · exact u20600
  · exact u20601
  · exact u20602
  · exact u20603
  · exact u20604

def r24113 : Route 9 := (fun mask => (mask,id))

def c24113 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24113 : Upper (D 8) (R 8) [66,260,24] 13 := by
  apply FastRouting.sound _ _ [66,260,24] 13 (by decide) (choices 2) [33,65,96,129,160,192] r24113 c24113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20605
  · exact u20606
  · exact u20607
  · exact u20608
  · exact u20609
  · exact u20610

def r24114 : Route 9 := (fun mask => (mask,id))

def c24114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24114 : Upper (D 8) (R 8) [66,260,33] 13 := by
  apply FastRouting.sound _ _ [66,260,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24114 c24114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20611
  · exact u20612
  · exact u20613
  · exact u20614
  · exact u20615
  · exact u20616
  · exact u20617
  · exact u20618
  · exact u20619
  · exact u20620

def r24115 : Route 9 := (fun mask => (mask,id))

def c24115 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24115 : Upper (D 8) (R 8) [66,260,40] 13 := by
  apply FastRouting.sound _ _ [66,260,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24115 c24115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20621
  · exact u20622
  · exact u20623
  · exact u20624
  · exact u20625
  · exact u20626
  · exact u20627
  · exact u20628
  · exact u20629
  · exact u20630

def b24116 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 69 185 185 185 249 185 441), lower := (rows 67 262 69 8 16 32 64 128 256), losses := [] }

theorem u24116 : Upper (D 8) (R 8) [66,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24117 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 76 185 177 177 241 177 433), lower := (rows 67 262 76 8 16 32 64 128 256), losses := [] }

theorem u24117 : Upper (D 8) (R 8) [66,260,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24118 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 100 185 185 185 249 185 441), lower := (rows 67 262 100 8 16 32 64 128 256), losses := [] }

theorem u24118 : Upper (D 8) (R 8) [66,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24119 : Route 9 := (fun mask => (mask,id))

def c24119 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24119 : Upper (D 8) (R 8) [66,260,129] 13 := by
  apply FastRouting.sound _ _ [66,260,129] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24119 c24119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20631
  · exact u20632
  · exact u20633
  · exact u20634
  · exact u20635
  · exact u20636
  · exact u20637
  · exact u20638
  · exact u20639
  · exact u20640

#print axioms u24119
end Delivery.IrregularNine14.P08
