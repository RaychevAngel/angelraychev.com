import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0208
import IrregularNine14P08C0209
import IrregularNine14P08C0212
import IrregularNine14P08C0213
import IrregularNine14P08C0216
import IrregularNine14P08C0217
import IrregularNine14P08C0219
import IrregularNine14P08C0220
import IrregularNine14P08C0221
import IrregularNine14P08C0222
import IrregularNine14P08C0223
import IrregularNine14P08C0224

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21000 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 370 370 370 498 370), lower := (rows 97 7 140 137 16 32 64 128 256), losses := [] }

theorem u21000 : Upper (D 8) (R 8) [96,5,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21001 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 369 369 369 497 369), lower := (rows 97 7 140 138 16 32 64 128 256), losses := [] }

theorem u21001 : Upper (D 8) (R 8) [96,5,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21002 : PairBound 9 := { available := 355, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 371 355 355 483 355), lower := (rows 97 7 140 152 16 32 64 128 256), losses := [] }

theorem u21002 : Upper (D 8) (R 8) [96,5,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21003 : PairBound 9 := { available := 371, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 371 371 371 499 371), lower := (rows 97 7 140 168 16 32 64 128 256), losses := [] }

theorem u21003 : Upper (D 8) (R 8) [96,5,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21004 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 200 307 307 371 435 307), lower := (rows 97 7 140 200 16 32 64 128 256), losses := [] }

theorem u21004 : Upper (D 8) (R 8) [96,5,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21005 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 265 242 242 242 242 498), lower := (rows 97 7 140 265 16 32 64 128 256), losses := [] }

theorem u21005 : Upper (D 8) (R 8) [96,5,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21006 : Route 9 := (fun mask => (mask,id))

def c21006 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21006 : Upper (D 8) (R 8) [96,5,136,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21006 c21006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13293
  · exact u13294
  · exact u13295
  · exact u13296
  · exact u13297
  · exact u13298

theorem m21007_3 : Upper (D 8) (R 8) [96,5,136,272,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12539

def r21007 : Route 9 := (fun mask => (mask,id))

def c21007 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21007 : Upper (D 8) (R 8) [96,5,136,272] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21007 c21007
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21007_3
  · exact u13299
  · exact u13300
  · exact u13301
  · exact u13302
  · exact u13303
  · exact u13304
  · exact u13305
  · exact u13306
  · exact u13307

theorem m21008_3 : Upper (D 8) (R 8) [96,5,136,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12540

def r21008 : Route 9 := (fun mask => (mask,id))

def c21008 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21008 : Upper (D 8) (R 8) [96,5,136,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21008 c21008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21008_3
  · exact u13308
  · exact u13309
  · exact u13310
  · exact u13311
  · exact u13312
  · exact u13313
  · exact u13314
  · exact u13315
  · exact u13316

def b21009 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 328 179 179 243 179 435), lower := (rows 97 7 140 328 16 32 64 128 256), losses := [] }

theorem u21009 : Upper (D 8) (R 8) [96,5,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21010 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 392 115 115 115 243 371), lower := (rows 97 7 140 392 16 32 64 128 256), losses := [] }

theorem u21010 : Upper (D 8) (R 8) [96,5,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21011_9 : Upper (D 8) (R 8) [96,5,144,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12802

theorem m21011_33 : Upper (D 8) (R 8) [96,5,144,34,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13207

theorem m21011_40 : Upper (D 8) (R 8) [96,5,144,34,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13226

theorem m21011_65 : Upper (D 8) (R 8) [96,5,144,34,65] 13 :=
  permutation_upper _ _ _ [96,5,136,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13239

theorem m21011_72 : Upper (D 8) (R 8) [96,5,144,34,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13249

theorem m21011_96 : Upper (D 8) (R 8) [96,5,144,34,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13257

theorem m21011_129 : Upper (D 8) (R 8) [96,5,144,34,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13264

theorem m21011_136 : Upper (D 8) (R 8) [96,5,144,34,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13272

theorem m21011_160 : Upper (D 8) (R 8) [96,5,144,34,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13278

theorem m21011_192 : Upper (D 8) (R 8) [96,5,144,34,192] 13 :=
  permutation_upper _ _ _ [96,5,136,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13284

theorem m21011_257 : Upper (D 8) (R 8) [96,5,144,34,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13288

theorem m21011_264 : Upper (D 8) (R 8) [96,5,144,34,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13300

theorem m21011_288 : Upper (D 8) (R 8) [96,5,144,34,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13309

theorem m21011_320 : Upper (D 8) (R 8) [96,5,144,34,320] 13 :=
  permutation_upper _ _ _ [96,5,136,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13317

theorem m21011_384 : Upper (D 8) (R 8) [96,5,144,34,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13321

def r21011 : Route 9 := (fun mask => (mask,id))

def c21011 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u21011 : Upper (D 8) (R 8) [96,5,144,34] 13 := by
  apply FastRouting.sound _ _ [96,5,144,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r21011 c21011
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21011_9
  · exact m21011_33
  · exact m21011_40
  · exact m21011_65
  · exact m21011_72
  · exact m21011_96
  · exact m21011_129
  · exact m21011_136
  · exact m21011_160
  · exact m21011_192
  · exact m21011_257
  · exact m21011_264
  · exact m21011_288
  · exact m21011_320
  · exact m21011_384

theorem m21012_9 : Upper (D 8) (R 8) [96,5,144,66,9] 13 :=
  permutation_upper _ _ _ [96,5,72,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12996

theorem m21012_33 : Upper (D 8) (R 8) [96,5,144,66,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13208

theorem m21012_40 : Upper (D 8) (R 8) [96,5,144,66,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13228

theorem m21012_129 : Upper (D 8) (R 8) [96,5,144,66,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13265

theorem m21012_136 : Upper (D 8) (R 8) [96,5,144,66,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13273

theorem m21012_160 : Upper (D 8) (R 8) [96,5,144,66,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13279

theorem m21012_257 : Upper (D 8) (R 8) [96,5,144,66,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13289

theorem m21012_264 : Upper (D 8) (R 8) [96,5,144,66,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13302

theorem m21012_288 : Upper (D 8) (R 8) [96,5,144,66,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13311

theorem m21012_384 : Upper (D 8) (R 8) [96,5,144,66,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13322

def r21012 : Route 9 := (fun mask => (mask,id))

def c21012 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21012 : Upper (D 8) (R 8) [96,5,144,66] 13 := by
  apply FastRouting.sound _ _ [96,5,144,66] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r21012 c21012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21012_9
  · exact m21012_33
  · exact m21012_40
  · exact m21012_129
  · exact m21012_136
  · exact m21012_160
  · exact m21012_257
  · exact m21012_264
  · exact m21012_288
  · exact m21012_384

theorem m21013_10 : Upper (D 8) (R 8) [96,5,144,129,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13200

theorem m21013_34 : Upper (D 8) (R 8) [96,5,144,129,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13218

theorem m21013_40 : Upper (D 8) (R 8) [96,5,144,129,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13230

theorem m21013_66 : Upper (D 8) (R 8) [96,5,144,129,66] 13 :=
  permutation_upper _ _ _ [96,5,136,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13244

theorem m21013_72 : Upper (D 8) (R 8) [96,5,144,129,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13250

theorem m21013_96 : Upper (D 8) (R 8) [96,5,144,129,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13258

theorem m21013_258 : Upper (D 8) (R 8) [96,5,144,129,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13296

theorem m21013_264 : Upper (D 8) (R 8) [96,5,144,129,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13304

theorem m21013_288 : Upper (D 8) (R 8) [96,5,144,129,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13313

theorem m21013_320 : Upper (D 8) (R 8) [96,5,144,129,320] 13 :=
  permutation_upper _ _ _ [96,5,136,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13318

def r21013 : Route 9 := (fun mask => (mask,id))

def c21013 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u21013 : Upper (D 8) (R 8) [96,5,144,129] 13 := by
  apply FastRouting.sound _ _ [96,5,144,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,258,264,288,320] r21013 c21013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21013_10
  · exact m21013_34
  · exact m21013_40
  · exact m21013_66
  · exact m21013_72
  · exact m21013_96
  · exact m21013_258
  · exact m21013_264
  · exact m21013_288
  · exact m21013_320

def b21014 : PairBound 9 := { available := 361, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 148 138 377 361 361 489 361), lower := (rows 97 7 148 138 16 32 64 128 256), losses := [] }

theorem u21014 : Upper (D 8) (R 8) [96,5,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21015_3 : Upper (D 8) (R 8) [96,5,144,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12532

theorem m21015_9 : Upper (D 8) (R 8) [96,5,144,160,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13191

theorem m21015_10 : Upper (D 8) (R 8) [96,5,144,160,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13201

theorem m21015_33 : Upper (D 8) (R 8) [96,5,144,160,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13209

theorem m21015_34 : Upper (D 8) (R 8) [96,5,144,160,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13219

theorem m21015_40 : Upper (D 8) (R 8) [96,5,144,160,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13232

theorem m21015_65 : Upper (D 8) (R 8) [96,5,144,160,65] 13 :=
  permutation_upper _ _ _ [96,5,136,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13240

theorem m21015_66 : Upper (D 8) (R 8) [96,5,144,160,66] 13 :=
  permutation_upper _ _ _ [96,5,136,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13245

theorem m21015_72 : Upper (D 8) (R 8) [96,5,144,160,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13252

theorem m21015_96 : Upper (D 8) (R 8) [96,5,144,160,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13259

theorem m21015_257 : Upper (D 8) (R 8) [96,5,144,160,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13291

theorem m21015_258 : Upper (D 8) (R 8) [96,5,144,160,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13297

theorem m21015_264 : Upper (D 8) (R 8) [96,5,144,160,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13306

theorem m21015_288 : Upper (D 8) (R 8) [96,5,144,160,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13315

theorem m21015_320 : Upper (D 8) (R 8) [96,5,144,160,320] 13 :=
  permutation_upper _ _ _ [96,5,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13320

def r21015 : Route 9 := (fun mask => (mask,id))

def c21015 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u21015 : Upper (D 8) (R 8) [96,5,144,160] 13 := by
  apply FastRouting.sound _ _ [96,5,144,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r21015 c21015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21015_3
  · exact m21015_9
  · exact m21015_10
  · exact m21015_33
  · exact m21015_34
  · exact m21015_40
  · exact m21015_65
  · exact m21015_66
  · exact m21015_72
  · exact m21015_96
  · exact m21015_257
  · exact m21015_258
  · exact m21015_264
  · exact m21015_288
  · exact m21015_320

theorem m21016_3 : Upper (D 8) (R 8) [96,5,144,192,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12533

theorem m21016_9 : Upper (D 8) (R 8) [96,5,144,192,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13192

theorem m21016_10 : Upper (D 8) (R 8) [96,5,144,192,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13202

theorem m21016_33 : Upper (D 8) (R 8) [96,5,144,192,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13210

theorem m21016_34 : Upper (D 8) (R 8) [96,5,144,192,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13220

theorem m21016_40 : Upper (D 8) (R 8) [96,5,144,192,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13233

theorem m21016_257 : Upper (D 8) (R 8) [96,5,144,192,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13292

theorem m21016_258 : Upper (D 8) (R 8) [96,5,144,192,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13298

theorem m21016_264 : Upper (D 8) (R 8) [96,5,144,192,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13307

theorem m21016_288 : Upper (D 8) (R 8) [96,5,144,192,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13316

def r21016 : Route 9 := (fun mask => (mask,id))

def c21016 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21016 : Upper (D 8) (R 8) [96,5,144,192] 13 := by
  apply FastRouting.sound _ _ [96,5,144,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r21016 c21016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21016_3
  · exact m21016_9
  · exact m21016_10
  · exact m21016_33
  · exact m21016_34
  · exact m21016_40
  · exact m21016_257
  · exact m21016_258
  · exact m21016_264
  · exact m21016_288

theorem m21017_10 : Upper (D 8) (R 8) [96,5,144,257,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13203

theorem m21017_34 : Upper (D 8) (R 8) [96,5,144,257,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13221

theorem m21017_40 : Upper (D 8) (R 8) [96,5,144,257,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13234

theorem m21017_66 : Upper (D 8) (R 8) [96,5,144,257,66] 13 :=
  permutation_upper _ _ _ [96,5,136,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13246

theorem m21017_72 : Upper (D 8) (R 8) [96,5,144,257,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13253

theorem m21017_96 : Upper (D 8) (R 8) [96,5,144,257,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13260

theorem m21017_130 : Upper (D 8) (R 8) [96,5,144,257,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13269

theorem m21017_136 : Upper (D 8) (R 8) [96,5,144,257,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13274

theorem m21017_160 : Upper (D 8) (R 8) [96,5,144,257,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13280

theorem m21017_192 : Upper (D 8) (R 8) [96,5,144,257,192] 13 :=
  permutation_upper _ _ _ [96,5,136,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13285

def r21017 : Route 9 := (fun mask => (mask,id))

def c21017 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21017 : Upper (D 8) (R 8) [96,5,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,144,257] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r21017 c21017
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21017_10
  · exact m21017_34
  · exact m21017_40
  · exact m21017_66
  · exact m21017_72
  · exact m21017_96
  · exact m21017_130
  · exact m21017_136
  · exact m21017_160
  · exact m21017_192

theorem m21018_9 : Upper (D 8) (R 8) [96,5,144,258,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13193

theorem m21018_33 : Upper (D 8) (R 8) [96,5,144,258,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13211

theorem m21018_40 : Upper (D 8) (R 8) [96,5,144,258,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13235

theorem m21018_65 : Upper (D 8) (R 8) [96,5,144,258,65] 13 :=
  permutation_upper _ _ _ [96,5,136,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13241

theorem m21018_72 : Upper (D 8) (R 8) [96,5,144,258,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13254

theorem m21018_96 : Upper (D 8) (R 8) [96,5,144,258,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13261

theorem m21018_129 : Upper (D 8) (R 8) [96,5,144,258,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13266

theorem m21018_136 : Upper (D 8) (R 8) [96,5,144,258,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13275

theorem m21018_160 : Upper (D 8) (R 8) [96,5,144,258,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13281

theorem m21018_192 : Upper (D 8) (R 8) [96,5,144,258,192] 13 :=
  permutation_upper _ _ _ [96,5,136,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13286

def r21018 : Route 9 := (fun mask => (mask,id))

def c21018 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21018 : Upper (D 8) (R 8) [96,5,144,258] 13 := by
  apply FastRouting.sound _ _ [96,5,144,258] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21018 c21018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21018_9
  · exact m21018_33
  · exact m21018_40
  · exact m21018_65
  · exact m21018_72
  · exact m21018_96
  · exact m21018_129
  · exact m21018_136
  · exact m21018_160
  · exact m21018_192

theorem m21019_3 : Upper (D 8) (R 8) [96,5,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12534

theorem m21019_9 : Upper (D 8) (R 8) [96,5,144,288,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13194

theorem m21019_10 : Upper (D 8) (R 8) [96,5,144,288,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13204

theorem m21019_33 : Upper (D 8) (R 8) [96,5,144,288,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13212

theorem m21019_34 : Upper (D 8) (R 8) [96,5,144,288,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13222

theorem m21019_40 : Upper (D 8) (R 8) [96,5,144,288,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13236

theorem m21019_65 : Upper (D 8) (R 8) [96,5,144,288,65] 13 :=
  permutation_upper _ _ _ [96,5,136,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13242

theorem m21019_66 : Upper (D 8) (R 8) [96,5,144,288,66] 13 :=
  permutation_upper _ _ _ [96,5,136,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13247

theorem m21019_72 : Upper (D 8) (R 8) [96,5,144,288,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13255

theorem m21019_96 : Upper (D 8) (R 8) [96,5,144,288,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13262

theorem m21019_129 : Upper (D 8) (R 8) [96,5,144,288,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13267

theorem m21019_130 : Upper (D 8) (R 8) [96,5,144,288,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13270

theorem m21019_136 : Upper (D 8) (R 8) [96,5,144,288,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13276

theorem m21019_160 : Upper (D 8) (R 8) [96,5,144,288,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13282

theorem m21019_192 : Upper (D 8) (R 8) [96,5,144,288,192] 13 :=
  permutation_upper _ _ _ [96,5,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13287

def r21019 : Route 9 := (fun mask => (mask,id))

def c21019 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21019 : Upper (D 8) (R 8) [96,5,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,144,288] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r21019 c21019
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21019_3
  · exact m21019_9
  · exact m21019_10
  · exact m21019_33
  · exact m21019_34
  · exact m21019_40
  · exact m21019_65
  · exact m21019_66
  · exact m21019_72
  · exact m21019_96
  · exact m21019_129
  · exact m21019_130
  · exact m21019_136
  · exact m21019_160
  · exact m21019_192

theorem m21020_3 : Upper (D 8) (R 8) [96,5,144,320,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12535

theorem m21020_9 : Upper (D 8) (R 8) [96,5,144,320,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13195

theorem m21020_10 : Upper (D 8) (R 8) [96,5,144,320,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13205

theorem m21020_33 : Upper (D 8) (R 8) [96,5,144,320,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13213

theorem m21020_34 : Upper (D 8) (R 8) [96,5,144,320,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13223

theorem m21020_40 : Upper (D 8) (R 8) [96,5,144,320,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13237

theorem m21020_129 : Upper (D 8) (R 8) [96,5,144,320,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13268

theorem m21020_130 : Upper (D 8) (R 8) [96,5,144,320,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13271

theorem m21020_136 : Upper (D 8) (R 8) [96,5,144,320,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13277

theorem m21020_160 : Upper (D 8) (R 8) [96,5,144,320,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13283

def r21020 : Route 9 := (fun mask => (mask,id))

def c21020 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21020 : Upper (D 8) (R 8) [96,5,144,320] 13 := by
  apply FastRouting.sound _ _ [96,5,144,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21020 c21020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21020_3
  · exact m21020_9
  · exact m21020_10
  · exact m21020_33
  · exact m21020_34
  · exact m21020_40
  · exact m21020_129
  · exact m21020_130
  · exact m21020_136
  · exact m21020_160

theorem m21021_3 : Upper (D 8) (R 8) [96,5,144,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12536

theorem m21021_9 : Upper (D 8) (R 8) [96,5,144,384,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13196

theorem m21021_10 : Upper (D 8) (R 8) [96,5,144,384,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13206

theorem m21021_33 : Upper (D 8) (R 8) [96,5,144,384,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13214

theorem m21021_34 : Upper (D 8) (R 8) [96,5,144,384,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13224

theorem m21021_40 : Upper (D 8) (R 8) [96,5,144,384,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13238

theorem m21021_65 : Upper (D 8) (R 8) [96,5,144,384,65] 13 :=
  permutation_upper _ _ _ [96,5,136,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13243

theorem m21021_66 : Upper (D 8) (R 8) [96,5,144,384,66] 13 :=
  permutation_upper _ _ _ [96,5,136,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13248

theorem m21021_72 : Upper (D 8) (R 8) [96,5,144,384,72] 13 :=
  permutation_upper _ _ _ [96,5,136,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13256

theorem m21021_96 : Upper (D 8) (R 8) [96,5,144,384,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13263

def r21021 : Route 9 := (fun mask => (mask,id))

def c21021 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21021 : Upper (D 8) (R 8) [96,5,144,384] 13 := by
  apply FastRouting.sound _ _ [96,5,144,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21021 c21021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21021_3
  · exact m21021_9
  · exact m21021_10
  · exact m21021_33
  · exact m21021_34
  · exact m21021_40
  · exact m21021_65
  · exact m21021_66
  · exact m21021_72
  · exact m21021_96

theorem m21022_10 : Upper (D 8) (R 8) [96,5,160,17,10] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12576

theorem m21022_34 : Upper (D 8) (R 8) [96,5,160,17,34] 13 :=
  permutation_upper _ _ _ [96,5,40,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12803

theorem m21022_40 : Upper (D 8) (R 8) [96,5,160,17,40] 13 :=
  permutation_upper _ _ _ [96,5,34,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12765

theorem m21022_66 : Upper (D 8) (R 8) [96,5,160,17,66] 13 :=
  permutation_upper _ _ _ [96,5,72,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12997

theorem m21022_72 : Upper (D 8) (R 8) [96,5,160,17,72] 13 :=
  permutation_upper _ _ _ [96,5,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12976

theorem m21022_96 : Upper (D 8) (R 8) [96,5,160,17,96] 13 :=
  permutation_upper _ _ _ [96,5,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13055

theorem m21022_130 : Upper (D 8) (R 8) [96,5,160,17,130] 13 :=
  permutation_upper _ _ _ [96,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13191

theorem m21022_136 : Upper (D 8) (R 8) [96,5,160,17,136] 13 :=
  permutation_upper _ _ _ [96,5,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13143

def r21022 : Route 9 := (fun mask => (mask,id))

def c21022 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u21022 : Upper (D 8) (R 8) [96,5,160,17] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192,258,264,288,320,384] r21022 c21022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21022_10
  · exact m21022_34
  · exact m21022_40
  · exact m21022_66
  · exact m21022_72
  · exact m21022_96
  · exact m21022_130
  · exact m21022_136
  · exact u13323
  · exact u13324
  · exact u13325
  · exact u13326
  · exact u13327
  · exact u13328
  · exact u13329

theorem m21023_9 : Upper (D 8) (R 8) [96,5,160,18,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12576

def r21023 : Route 9 := (fun mask => (mask,id))

def c21023 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u21023 : Upper (D 8) (R 8) [96,5,160,18] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r21023 c21023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21023_9
  · exact u13330
  · exact u13331
  · exact u13332
  · exact u13333
  · exact u13334
  · exact u13335
  · exact u13336
  · exact u13337
  · exact u13338
  · exact u13339
  · exact u13340
  · exact u13341
  · exact u13342
  · exact u13343

def b21024 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 474 506 474 474 474), lower := (rows 97 7 164 41 16 32 64 128 256), losses := [] }

theorem u21024 : Upper (D 8) (R 8) [96,5,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21025_9 : Upper (D 8) (R 8) [96,5,160,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12803

def r21025 : Route 9 := (fun mask => (mask,id))

def c21025 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u21025 : Upper (D 8) (R 8) [96,5,160,34] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r21025 c21025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21025_9
  · exact u13352
  · exact u13353
  · exact u13354
  · exact u13355
  · exact u13356
  · exact u13357
  · exact u13358
  · exact u13359
  · exact u13360

theorem m21026_3 : Upper (D 8) (R 8) [96,5,160,48,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12542

theorem m21026_9 : Upper (D 8) (R 8) [96,5,160,48,9] 13 :=
  permutation_upper _ _ _ [96,5,34,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12765

theorem m21026_10 : Upper (D 8) (R 8) [96,5,160,48,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13331

def r21026 : Route 9 := (fun mask => (mask,id))

def c21026 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u21026 : Upper (D 8) (R 8) [96,5,160,48] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r21026 c21026
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21026_3
  · exact m21026_9
  · exact m21026_10
  · exact u13361
  · exact u13362
  · exact u13363
  · exact u13364
  · exact u13365
  · exact u13366
  · exact u13367
  · exact u13368
  · exact u13369
  · exact u13370
  · exact u13371
  · exact u13372

def b21027 : PairBound 9 := { available := 442, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 73 442 442 506 442 442), lower := (rows 97 7 164 73 16 32 64 128 256), losses := [] }

theorem u21027 : Upper (D 8) (R 8) [96,5,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21028_9 : Upper (D 8) (R 8) [96,5,160,66,9] 13 :=
  permutation_upper _ _ _ [96,5,72,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12997

theorem m21028_33 : Upper (D 8) (R 8) [96,5,160,66,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13344

theorem m21028_40 : Upper (D 8) (R 8) [96,5,160,66,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13362

def r21028 : Route 9 := (fun mask => (mask,id))

def c21028 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21028 : Upper (D 8) (R 8) [96,5,160,66] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r21028 c21028
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21028_9
  · exact m21028_33
  · exact m21028_40
  · exact u13378
  · exact u13379
  · exact u13380
  · exact u13381
  · exact u13382
  · exact u13383
  · exact u13384

theorem m21029_3 : Upper (D 8) (R 8) [96,5,160,80,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12543

theorem m21029_9 : Upper (D 8) (R 8) [96,5,160,80,9] 13 :=
  permutation_upper _ _ _ [96,5,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12976

theorem m21029_10 : Upper (D 8) (R 8) [96,5,160,80,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13333

theorem m21029_33 : Upper (D 8) (R 8) [96,5,160,80,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13345

theorem m21029_34 : Upper (D 8) (R 8) [96,5,160,80,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13353

theorem m21029_40 : Upper (D 8) (R 8) [96,5,160,80,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13363

def r21029 : Route 9 := (fun mask => (mask,id))

def c21029 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21029 : Upper (D 8) (R 8) [96,5,160,80] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r21029 c21029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21029_3
  · exact m21029_9
  · exact m21029_10
  · exact m21029_33
  · exact m21029_34
  · exact m21029_40
  · exact u13385
  · exact u13386
  · exact u13387
  · exact u13388
  · exact u13389
  · exact u13390
  · exact u13391
  · exact u13392
  · exact u13393

def b21030 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 411 443 475 411 411), lower := (rows 97 7 164 104 16 32 64 128 256), losses := [] }

theorem u21030 : Upper (D 8) (R 8) [96,5,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21031_10 : Upper (D 8) (R 8) [96,5,160,129,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13335

theorem m21031_34 : Upper (D 8) (R 8) [96,5,160,129,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13354

theorem m21031_40 : Upper (D 8) (R 8) [96,5,160,129,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13364

theorem m21031_66 : Upper (D 8) (R 8) [96,5,160,129,66] 13 :=
  permutation_upper _ _ _ [96,5,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13378

theorem m21031_72 : Upper (D 8) (R 8) [96,5,160,129,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13385

theorem m21031_96 : Upper (D 8) (R 8) [96,5,160,129,96] 13 :=
  permutation_upper _ _ _ [96,5,160,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13394

def r21031 : Route 9 := (fun mask => (mask,id))

def c21031 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u21031 : Upper (D 8) (R 8) [96,5,160,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,258,264,288,320] r21031 c21031
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21031_10
  · exact m21031_34
  · exact m21031_40
  · exact m21031_66
  · exact m21031_72
  · exact m21031_96
  · exact u13400
  · exact u13401
  · exact u13402
  · exact u13403

def b21032 : PairBound 9 := { available := 377, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 138 377 377 377 505 377), lower := (rows 97 7 164 138 16 32 64 128 256), losses := [] }

theorem u21032 : Upper (D 8) (R 8) [96,5,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21033_3 : Upper (D 8) (R 8) [96,5,160,144,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12544

theorem m21033_9 : Upper (D 8) (R 8) [96,5,160,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13143

theorem m21033_10 : Upper (D 8) (R 8) [96,5,160,144,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13336

theorem m21033_33 : Upper (D 8) (R 8) [96,5,160,144,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13346

theorem m21033_34 : Upper (D 8) (R 8) [96,5,160,144,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13355

theorem m21033_40 : Upper (D 8) (R 8) [96,5,160,144,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13366

theorem m21033_65 : Upper (D 8) (R 8) [96,5,160,144,65] 13 :=
  permutation_upper _ _ _ [96,5,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13373

theorem m21033_66 : Upper (D 8) (R 8) [96,5,160,144,66] 13 :=
  permutation_upper _ _ _ [96,5,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13379

theorem m21033_72 : Upper (D 8) (R 8) [96,5,160,144,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13387

theorem m21033_96 : Upper (D 8) (R 8) [96,5,160,144,96] 13 :=
  permutation_upper _ _ _ [96,5,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13395

def r21033 : Route 9 := (fun mask => (mask,id))

def c21033 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u21033 : Upper (D 8) (R 8) [96,5,160,144] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r21033 c21033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21033_3
  · exact m21033_9
  · exact m21033_10
  · exact m21033_33
  · exact m21033_34
  · exact m21033_40
  · exact m21033_65
  · exact m21033_66
  · exact m21033_72
  · exact m21033_96
  · exact u13408
  · exact u13409
  · exact u13410
  · exact u13411
  · exact u13412

def b21034 : PairBound 9 := { available := 347, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 168 347 379 347 475 347), lower := (rows 97 7 164 168 16 32 64 128 256), losses := [] }

theorem u21034 : Upper (D 8) (R 8) [96,5,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21035_3 : Upper (D 8) (R 8) [96,5,160,192,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12545

theorem m21035_9 : Upper (D 8) (R 8) [96,5,160,192,9] 13 :=
  permutation_upper _ _ _ [96,5,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13324

theorem m21035_10 : Upper (D 8) (R 8) [96,5,160,192,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13338

theorem m21035_33 : Upper (D 8) (R 8) [96,5,160,192,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13347

theorem m21035_34 : Upper (D 8) (R 8) [96,5,160,192,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13356

theorem m21035_40 : Upper (D 8) (R 8) [96,5,160,192,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13367

def r21035 : Route 9 := (fun mask => (mask,id))

def c21035 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21035 : Upper (D 8) (R 8) [96,5,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r21035 c21035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21035_3
  · exact m21035_9
  · exact m21035_10
  · exact m21035_33
  · exact m21035_34
  · exact m21035_40
  · exact u13417
  · exact u13418
  · exact u13419
  · exact u13420

theorem m21036_10 : Upper (D 8) (R 8) [96,5,160,257,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13339

theorem m21036_34 : Upper (D 8) (R 8) [96,5,160,257,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13357

theorem m21036_40 : Upper (D 8) (R 8) [96,5,160,257,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13368

theorem m21036_66 : Upper (D 8) (R 8) [96,5,160,257,66] 13 :=
  permutation_upper _ _ _ [96,5,160,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13381

theorem m21036_72 : Upper (D 8) (R 8) [96,5,160,257,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13389

theorem m21036_96 : Upper (D 8) (R 8) [96,5,160,257,96] 13 :=
  permutation_upper _ _ _ [96,5,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13396

theorem m21036_130 : Upper (D 8) (R 8) [96,5,160,257,130] 13 :=
  permutation_upper _ _ _ [96,5,160,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13404

theorem m21036_136 : Upper (D 8) (R 8) [96,5,160,257,136] 13 :=
  permutation_upper _ _ _ [96,5,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13408

theorem m21036_160 : Upper (D 8) (R 8) [96,5,160,257,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13413

theorem m21036_192 : Upper (D 8) (R 8) [96,5,160,257,192] 13 :=
  permutation_upper _ _ _ [96,5,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13417

def r21036 : Route 9 := (fun mask => (mask,id))

def c21036 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21036 : Upper (D 8) (R 8) [96,5,160,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r21036 c21036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21036_10
  · exact m21036_34
  · exact m21036_40
  · exact m21036_66
  · exact m21036_72
  · exact m21036_96
  · exact m21036_130
  · exact m21036_136
  · exact m21036_160
  · exact m21036_192

theorem m21037_9 : Upper (D 8) (R 8) [96,5,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,160,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13325

theorem m21037_33 : Upper (D 8) (R 8) [96,5,160,258,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13348

theorem m21037_40 : Upper (D 8) (R 8) [96,5,160,258,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13369

theorem m21037_65 : Upper (D 8) (R 8) [96,5,160,258,65] 13 :=
  permutation_upper _ _ _ [96,5,160,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13374

theorem m21037_72 : Upper (D 8) (R 8) [96,5,160,258,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13390

theorem m21037_96 : Upper (D 8) (R 8) [96,5,160,258,96] 13 :=
  permutation_upper _ _ _ [96,5,160,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13397

theorem m21037_129 : Upper (D 8) (R 8) [96,5,160,258,129] 13 :=
  permutation_upper _ _ _ [96,5,160,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13400

theorem m21037_136 : Upper (D 8) (R 8) [96,5,160,258,136] 13 :=
  permutation_upper _ _ _ [96,5,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13409

theorem m21037_160 : Upper (D 8) (R 8) [96,5,160,258,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13414

theorem m21037_192 : Upper (D 8) (R 8) [96,5,160,258,192] 13 :=
  permutation_upper _ _ _ [96,5,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13418

def r21037 : Route 9 := (fun mask => (mask,id))

def c21037 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21037 : Upper (D 8) (R 8) [96,5,160,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,258] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21037 c21037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21037_9
  · exact m21037_33
  · exact m21037_40
  · exact m21037_65
  · exact m21037_72
  · exact m21037_96
  · exact m21037_129
  · exact m21037_136
  · exact m21037_160
  · exact m21037_192

theorem m21038_3 : Upper (D 8) (R 8) [96,5,160,272,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12546

theorem m21038_9 : Upper (D 8) (R 8) [96,5,160,272,9] 13 :=
  permutation_upper _ _ _ [96,5,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13326

theorem m21038_10 : Upper (D 8) (R 8) [96,5,160,272,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13340

theorem m21038_33 : Upper (D 8) (R 8) [96,5,160,272,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13349

theorem m21038_34 : Upper (D 8) (R 8) [96,5,160,272,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13358

theorem m21038_40 : Upper (D 8) (R 8) [96,5,160,272,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13370

theorem m21038_65 : Upper (D 8) (R 8) [96,5,160,272,65] 13 :=
  permutation_upper _ _ _ [96,5,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13375

theorem m21038_66 : Upper (D 8) (R 8) [96,5,160,272,66] 13 :=
  permutation_upper _ _ _ [96,5,160,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13382

theorem m21038_72 : Upper (D 8) (R 8) [96,5,160,272,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13391

theorem m21038_96 : Upper (D 8) (R 8) [96,5,160,272,96] 13 :=
  permutation_upper _ _ _ [96,5,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13398

theorem m21038_129 : Upper (D 8) (R 8) [96,5,160,272,129] 13 :=
  permutation_upper _ _ _ [96,5,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13401

theorem m21038_130 : Upper (D 8) (R 8) [96,5,160,272,130] 13 :=
  permutation_upper _ _ _ [96,5,160,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13405

theorem m21038_136 : Upper (D 8) (R 8) [96,5,160,272,136] 13 :=
  permutation_upper _ _ _ [96,5,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13410

theorem m21038_160 : Upper (D 8) (R 8) [96,5,160,272,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13415

theorem m21038_192 : Upper (D 8) (R 8) [96,5,160,272,192] 13 :=
  permutation_upper _ _ _ [96,5,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13419

def r21038 : Route 9 := (fun mask => (mask,id))

def c21038 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21038 : Upper (D 8) (R 8) [96,5,160,272] 13 := by
  apply FastRouting.sound _ _ [96,5,160,272] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r21038 c21038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21038_3
  · exact m21038_9
  · exact m21038_10
  · exact m21038_33
  · exact m21038_34
  · exact m21038_40
  · exact m21038_65
  · exact m21038_66
  · exact m21038_72
  · exact m21038_96
  · exact m21038_129
  · exact m21038_130
  · exact m21038_136
  · exact m21038_160
  · exact m21038_192

theorem m21039_3 : Upper (D 8) (R 8) [96,5,160,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12547

theorem m21039_9 : Upper (D 8) (R 8) [96,5,160,288,9] 13 :=
  permutation_upper _ _ _ [96,5,160,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13327

theorem m21039_10 : Upper (D 8) (R 8) [96,5,160,288,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13341

theorem m21039_65 : Upper (D 8) (R 8) [96,5,160,288,65] 13 :=
  permutation_upper _ _ _ [96,5,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13376

theorem m21039_66 : Upper (D 8) (R 8) [96,5,160,288,66] 13 :=
  permutation_upper _ _ _ [96,5,160,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13383

theorem m21039_72 : Upper (D 8) (R 8) [96,5,160,288,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13392

theorem m21039_129 : Upper (D 8) (R 8) [96,5,160,288,129] 13 :=
  permutation_upper _ _ _ [96,5,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13402

theorem m21039_130 : Upper (D 8) (R 8) [96,5,160,288,130] 13 :=
  permutation_upper _ _ _ [96,5,160,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13406

theorem m21039_136 : Upper (D 8) (R 8) [96,5,160,288,136] 13 :=
  permutation_upper _ _ _ [96,5,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13411

theorem m21039_192 : Upper (D 8) (R 8) [96,5,160,288,192] 13 :=
  permutation_upper _ _ _ [96,5,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13420

def r21039 : Route 9 := (fun mask => (mask,id))

def c21039 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21039 : Upper (D 8) (R 8) [96,5,160,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r21039 c21039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21039_3
  · exact m21039_9
  · exact m21039_10
  · exact m21039_65
  · exact m21039_66
  · exact m21039_72
  · exact m21039_129
  · exact m21039_130
  · exact m21039_136
  · exact m21039_192

theorem m21040_3 : Upper (D 8) (R 8) [96,5,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12548

theorem m21040_9 : Upper (D 8) (R 8) [96,5,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13328

theorem m21040_10 : Upper (D 8) (R 8) [96,5,160,320,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13342

theorem m21040_33 : Upper (D 8) (R 8) [96,5,160,320,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13350

theorem m21040_34 : Upper (D 8) (R 8) [96,5,160,320,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13359

theorem m21040_40 : Upper (D 8) (R 8) [96,5,160,320,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13371

theorem m21040_129 : Upper (D 8) (R 8) [96,5,160,320,129] 13 :=
  permutation_upper _ _ _ [96,5,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13403

theorem m21040_130 : Upper (D 8) (R 8) [96,5,160,320,130] 13 :=
  permutation_upper _ _ _ [96,5,160,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13407

theorem m21040_136 : Upper (D 8) (R 8) [96,5,160,320,136] 13 :=
  permutation_upper _ _ _ [96,5,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13412

theorem m21040_160 : Upper (D 8) (R 8) [96,5,160,320,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13416

def r21040 : Route 9 := (fun mask => (mask,id))

def c21040 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21040 : Upper (D 8) (R 8) [96,5,160,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21040 c21040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21040_3
  · exact m21040_9
  · exact m21040_10
  · exact m21040_33
  · exact m21040_34
  · exact m21040_40
  · exact m21040_129
  · exact m21040_130
  · exact m21040_136
  · exact m21040_160

theorem m21041_3 : Upper (D 8) (R 8) [96,5,160,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12549

theorem m21041_9 : Upper (D 8) (R 8) [96,5,160,384,9] 13 :=
  permutation_upper _ _ _ [96,5,160,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13329

theorem m21041_10 : Upper (D 8) (R 8) [96,5,160,384,10] 13 :=
  permutation_upper _ _ _ [96,5,160,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13343

theorem m21041_33 : Upper (D 8) (R 8) [96,5,160,384,33] 13 :=
  permutation_upper _ _ _ [96,5,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13351

theorem m21041_34 : Upper (D 8) (R 8) [96,5,160,384,34] 13 :=
  permutation_upper _ _ _ [96,5,160,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13360

theorem m21041_40 : Upper (D 8) (R 8) [96,5,160,384,40] 13 :=
  permutation_upper _ _ _ [96,5,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13372

theorem m21041_65 : Upper (D 8) (R 8) [96,5,160,384,65] 13 :=
  permutation_upper _ _ _ [96,5,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13377

theorem m21041_66 : Upper (D 8) (R 8) [96,5,160,384,66] 13 :=
  permutation_upper _ _ _ [96,5,160,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13384

theorem m21041_72 : Upper (D 8) (R 8) [96,5,160,384,72] 13 :=
  permutation_upper _ _ _ [96,5,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13393

theorem m21041_96 : Upper (D 8) (R 8) [96,5,160,384,96] 13 :=
  permutation_upper _ _ _ [96,5,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13399

def r21041 : Route 9 := (fun mask => (mask,id))

def c21041 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21041 : Upper (D 8) (R 8) [96,5,160,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21041 c21041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21041_3
  · exact m21041_9
  · exact m21041_10
  · exact m21041_33
  · exact m21041_34
  · exact m21041_40
  · exact m21041_65
  · exact m21041_66
  · exact m21041_72
  · exact m21041_96

def b21042 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 441 425 489 425 425), lower := (rows 97 7 196 26 16 32 64 128 256), losses := [] }

theorem u21042 : Upper (D 8) (R 8) [96,5,192,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21043 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 441 441 505 441 441), lower := (rows 97 7 196 42 16 32 64 128 256), losses := [] }

theorem u21043 : Upper (D 8) (R 8) [96,5,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21044 : PairBound 9 := { available := 314, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 137 314 314 378 442 314), lower := (rows 97 7 196 137 16 32 64 128 256), losses := [] }

theorem u21044 : Upper (D 8) (R 8) [96,5,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21045 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 138 313 313 377 441 313), lower := (rows 97 7 196 138 16 32 64 128 256), losses := [] }

theorem u21045 : Upper (D 8) (R 8) [96,5,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21046 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 168 315 315 379 443 315), lower := (rows 97 7 196 168 16 32 64 128 256), losses := [] }

theorem u21046 : Upper (D 8) (R 8) [96,5,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21047 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 265 186 186 250 186 442), lower := (rows 97 7 196 265 16 32 64 128 256), losses := [] }

theorem u21047 : Upper (D 8) (R 8) [96,5,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21048 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 266 185 185 249 185 441), lower := (rows 97 7 196 266 16 32 64 128 256), losses := [] }

theorem u21048 : Upper (D 8) (R 8) [96,5,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21049 : PairBound 9 := { available := 187, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 296 187 187 251 187 443), lower := (rows 97 7 196 296 16 32 64 128 256), losses := [] }

theorem u21049 : Upper (D 8) (R 8) [96,5,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21050 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 392 59 59 123 187 315), lower := (rows 97 7 196 392 16 32 64 128 256), losses := [] }

theorem u21050 : Upper (D 8) (R 8) [96,5,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21051 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 248 232 232 232 488), lower := (rows 97 7 261 26 16 32 64 128 256), losses := [] }

theorem u21051 : Upper (D 8) (R 8) [96,5,257,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21052 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 248 248 248 248 504), lower := (rows 97 7 261 42 16 32 64 128 256), losses := [] }

theorem u21052 : Upper (D 8) (R 8) [96,5,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21053 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 74 184 184 248 184 440), lower := (rows 97 7 261 74 16 32 64 128 256), losses := [] }

theorem u21053 : Upper (D 8) (R 8) [96,5,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21054 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 138 248 248 248 248 504), lower := (rows 97 7 261 138 16 32 64 128 256), losses := [] }

theorem u21054 : Upper (D 8) (R 8) [96,5,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21055 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 168 250 250 250 250 506), lower := (rows 97 7 261 168 16 32 64 128 256), losses := [] }

theorem u21055 : Upper (D 8) (R 8) [96,5,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21056 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 200 186 186 250 186 442), lower := (rows 97 7 261 200 16 32 64 128 256), losses := [] }

theorem u21056 : Upper (D 8) (R 8) [96,5,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21057 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 262 25 248 232 232 232 488), lower := (rows 97 7 262 25 16 32 64 128 256), losses := [] }

theorem u21057 : Upper (D 8) (R 8) [96,5,258,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21058 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 262 41 248 248 248 248 504), lower := (rows 97 7 262 41 16 32 64 128 256), losses := [] }

theorem u21058 : Upper (D 8) (R 8) [96,5,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21059_9 : Upper (D 8) (R 8) [96,5,258,48,9] 13 :=
  permutation_upper _ _ _ [96,5,34,17,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12766

theorem m21059_33 : Upper (D 8) (R 8) [96,5,258,48,33] 13 :=
  permutation_upper _ _ _ [96,5,258,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13480

def r21059 : Route 9 := (fun mask => (mask,id))

def c21059 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21059 : Upper (D 8) (R 8) [96,5,258,48] 13 := by
  apply FastRouting.sound _ _ [96,5,258,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21059 c21059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21059_9
  · exact m21059_33
  · exact u13485
  · exact u13486
  · exact u13487
  · exact u13488
  · exact u13489
  · exact u13490
  · exact u13491
  · exact u13492

#print axioms u21059
end Delivery.IrregularNine14.P08
