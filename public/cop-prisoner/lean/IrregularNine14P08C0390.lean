import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0296
import IrregularNine14P08C0297
import IrregularNine14P08C0298
import IrregularNine14P08C0299
import IrregularNine14P08C0300
import IrregularNine14P08C0301
import IrregularNine14P08C0302
import IrregularNine14P08C0303
import IrregularNine14P08C0304

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23400 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 134 73 184 184 248 184 440), lower := (rows 321 7 134 73 16 32 64 128 256), losses := [] }

theorem u23400 : Upper (D 8) (R 8) [320,5,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23401_9 : Upper (D 8) (R 8) [320,5,130,80,9] 13 :=
  permutation_upper _ _ _ [320,5,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18030

theorem m23401_33 : Upper (D 8) (R 8) [320,5,130,80,33] 13 :=
  permutation_upper _ _ _ [320,5,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18106

theorem m23401_40 : Upper (D 8) (R 8) [320,5,130,80,40] 13 :=
  permutation_upper _ _ _ [320,5,130,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18113

def r23401 : Route 9 := (fun mask => (mask,id))

def c23401 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23401 : Upper (D 8) (R 8) [320,5,130,80] 13 := by
  apply FastRouting.sound _ _ [320,5,130,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23401 c23401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23401_9
  · exact m23401_33
  · exact m23401_40
  · exact u18119
  · exact u18120
  · exact u18121

theorem m23402_9 : Upper (D 8) (R 8) [320,5,130,96,9] 13 :=
  permutation_upper _ _ _ [320,5,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18063

theorem m23402_33 : Upper (D 8) (R 8) [320,5,130,96,33] 13 :=
  permutation_upper _ _ _ [320,5,130,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18107

theorem m23402_40 : Upper (D 8) (R 8) [320,5,130,96,40] 13 :=
  permutation_upper _ _ _ [320,5,130,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18114

def r23402 : Route 9 := (fun mask => (mask,id))

def c23402 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23402 : Upper (D 8) (R 8) [320,5,130,96] 13 := by
  apply FastRouting.sound _ _ [320,5,130,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23402 c23402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23402_9
  · exact m23402_33
  · exact m23402_40
  · exact u18122
  · exact u18123
  · exact u18124

def b23403 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 134 137 120 120 120 248 376), lower := (rows 321 7 134 137 16 32 64 128 256), losses := [] }

theorem u23403 : Upper (D 8) (R 8) [320,5,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23404 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 152 121 105 105 233 361), lower := (rows 321 7 134 152 16 32 64 128 256), losses := [] }

theorem u23404 : Upper (D 8) (R 8) [320,5,130,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23405 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 168 121 121 121 249 377), lower := (rows 321 7 134 168 16 32 64 128 256), losses := [] }

theorem u23405 : Upper (D 8) (R 8) [320,5,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23406 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 200 57 57 121 185 313), lower := (rows 321 7 134 200 16 32 64 128 256), losses := [] }

theorem u23406 : Upper (D 8) (R 8) [320,5,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23407 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 25 242 226 226 226 482), lower := (rows 321 7 140 25 16 32 64 128 256), losses := [] }

theorem u23407 : Upper (D 8) (R 8) [320,5,136,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23408 : Route 9 := (fun mask => (mask,id))

def c23408 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23408 : Upper (D 8) (R 8) [320,5,136,18] 13 := by
  apply FastRouting.sound _ _ [320,5,136,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23408 c23408
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18127
  · exact u18128
  · exact u18129
  · exact u18130
  · exact u18131
  · exact u18132

def b23409 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 41 242 242 242 242 498), lower := (rows 321 7 140 41 16 32 64 128 256), losses := [] }

theorem u23409 : Upper (D 8) (R 8) [320,5,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23410 : Route 9 := (fun mask => (mask,id))

def c23410 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23410 : Upper (D 8) (R 8) [320,5,136,34] 13 := by
  apply FastRouting.sound _ _ [320,5,136,34] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23410 c23410
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18139
  · exact u18140
  · exact u18141
  · exact u18142
  · exact u18143
  · exact u18144

theorem m23411_3 : Upper (D 8) (R 8) [320,5,136,48,3] 13 :=
  permutation_upper _ _ _ [320,5,9,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17808

def r23411 : Route 9 := (fun mask => (mask,id))

def c23411 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23411 : Upper (D 8) (R 8) [320,5,136,48] 13 := by
  apply FastRouting.sound _ _ [320,5,136,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23411 c23411
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23411_3
  · exact u18145
  · exact u18146
  · exact u18147
  · exact u18148
  · exact u18149
  · exact u18150
  · exact u18151
  · exact u18152
  · exact u18153

def b23412 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 73 178 178 242 178 434), lower := (rows 321 7 140 73 16 32 64 128 256), losses := [] }

theorem u23412 : Upper (D 8) (R 8) [320,5,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23413 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 74 177 177 241 177 433), lower := (rows 321 7 140 74 16 32 64 128 256), losses := [] }

theorem u23413 : Upper (D 8) (R 8) [320,5,136,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23414 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 88 179 163 227 163 419), lower := (rows 321 7 140 88 16 32 64 128 256), losses := [] }

theorem u23414 : Upper (D 8) (R 8) [320,5,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23415 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 104 179 179 243 179 435), lower := (rows 321 7 140 104 16 32 64 128 256), losses := [] }

theorem u23415 : Upper (D 8) (R 8) [320,5,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23416 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 140 137 114 114 114 242 370), lower := (rows 321 7 140 137 16 32 64 128 256), losses := [] }

theorem u23416 : Upper (D 8) (R 8) [320,5,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23417 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 138 113 113 113 241 369), lower := (rows 321 7 140 138 16 32 64 128 256), losses := [] }

theorem u23417 : Upper (D 8) (R 8) [320,5,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23418 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 152 115 99 99 227 355), lower := (rows 321 7 140 152 16 32 64 128 256), losses := [] }

theorem u23418 : Upper (D 8) (R 8) [320,5,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23419 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 168 115 115 115 243 371), lower := (rows 321 7 140 168 16 32 64 128 256), losses := [] }

theorem u23419 : Upper (D 8) (R 8) [320,5,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23420 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 200 51 51 115 179 307), lower := (rows 321 7 140 200 16 32 64 128 256), losses := [] }

theorem u23420 : Upper (D 8) (R 8) [320,5,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23421_10 : Upper (D 8) (R 8) [320,5,144,33,10] 13 :=
  permutation_upper _ _ _ [320,5,136,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18127

theorem m23421_34 : Upper (D 8) (R 8) [320,5,144,33,34] 13 :=
  permutation_upper _ _ _ [320,5,136,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18139

theorem m23421_40 : Upper (D 8) (R 8) [320,5,144,33,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18145

theorem m23421_66 : Upper (D 8) (R 8) [320,5,144,33,66] 13 :=
  permutation_upper _ _ _ [320,5,136,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18156

theorem m23421_72 : Upper (D 8) (R 8) [320,5,144,33,72] 13 :=
  permutation_upper _ _ _ [320,5,136,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18159

theorem m23421_96 : Upper (D 8) (R 8) [320,5,144,33,96] 13 :=
  permutation_upper _ _ _ [320,5,136,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18164

theorem m23421_130 : Upper (D 8) (R 8) [320,5,144,33,130] 13 :=
  permutation_upper _ _ _ [320,5,136,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18172

theorem m23421_136 : Upper (D 8) (R 8) [320,5,144,33,136] 13 :=
  permutation_upper _ _ _ [320,5,136,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18174

theorem m23421_160 : Upper (D 8) (R 8) [320,5,144,33,160] 13 :=
  permutation_upper _ _ _ [320,5,136,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18178

theorem m23421_192 : Upper (D 8) (R 8) [320,5,144,33,192] 13 :=
  permutation_upper _ _ _ [320,5,136,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18182

def r23421 : Route 9 := (fun mask => (mask,id))

def c23421 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23421 : Upper (D 8) (R 8) [320,5,144,33] 13 := by
  apply FastRouting.sound _ _ [320,5,144,33] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r23421 c23421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23421_10
  · exact m23421_34
  · exact m23421_40
  · exact m23421_66
  · exact m23421_72
  · exact m23421_96
  · exact m23421_130
  · exact m23421_136
  · exact m23421_160
  · exact m23421_192

theorem m23422_9 : Upper (D 8) (R 8) [320,5,144,34,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17944

theorem m23422_33 : Upper (D 8) (R 8) [320,5,144,34,33] 13 :=
  permutation_upper _ _ _ [320,5,136,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18133

theorem m23422_40 : Upper (D 8) (R 8) [320,5,144,34,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18146

theorem m23422_65 : Upper (D 8) (R 8) [320,5,144,34,65] 13 :=
  permutation_upper _ _ _ [320,5,136,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18154

theorem m23422_72 : Upper (D 8) (R 8) [320,5,144,34,72] 13 :=
  permutation_upper _ _ _ [320,5,136,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18160

theorem m23422_96 : Upper (D 8) (R 8) [320,5,144,34,96] 13 :=
  permutation_upper _ _ _ [320,5,136,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18165

theorem m23422_129 : Upper (D 8) (R 8) [320,5,144,34,129] 13 :=
  permutation_upper _ _ _ [320,5,136,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18169

theorem m23422_136 : Upper (D 8) (R 8) [320,5,144,34,136] 13 :=
  permutation_upper _ _ _ [320,5,136,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18175

theorem m23422_160 : Upper (D 8) (R 8) [320,5,144,34,160] 13 :=
  permutation_upper _ _ _ [320,5,136,160,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18179

theorem m23422_192 : Upper (D 8) (R 8) [320,5,144,34,192] 13 :=
  permutation_upper _ _ _ [320,5,136,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18183

def r23422 : Route 9 := (fun mask => (mask,id))

def c23422 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23422 : Upper (D 8) (R 8) [320,5,144,34] 13 := by
  apply FastRouting.sound _ _ [320,5,144,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23422 c23422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23422_9
  · exact m23422_33
  · exact m23422_40
  · exact m23422_65
  · exact m23422_72
  · exact m23422_96
  · exact m23422_129
  · exact m23422_136
  · exact m23422_160
  · exact m23422_192

theorem m23423_9 : Upper (D 8) (R 8) [320,5,144,66,9] 13 :=
  permutation_upper _ _ _ [320,5,72,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18037

theorem m23423_33 : Upper (D 8) (R 8) [320,5,144,66,33] 13 :=
  permutation_upper _ _ _ [320,5,136,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18134

theorem m23423_40 : Upper (D 8) (R 8) [320,5,144,66,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18148

theorem m23423_129 : Upper (D 8) (R 8) [320,5,144,66,129] 13 :=
  permutation_upper _ _ _ [320,5,136,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18170

theorem m23423_136 : Upper (D 8) (R 8) [320,5,144,66,136] 13 :=
  permutation_upper _ _ _ [320,5,136,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18176

theorem m23423_160 : Upper (D 8) (R 8) [320,5,144,66,160] 13 :=
  permutation_upper _ _ _ [320,5,136,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18180

def r23423 : Route 9 := (fun mask => (mask,id))

def c23423 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23423 : Upper (D 8) (R 8) [320,5,144,66] 13 := by
  apply FastRouting.sound _ _ [320,5,144,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23423 c23423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23423_9
  · exact m23423_33
  · exact m23423_40
  · exact m23423_129
  · exact m23423_136
  · exact m23423_160

theorem m23424_3 : Upper (D 8) (R 8) [320,5,144,96,3] 13 :=
  permutation_upper _ _ _ [320,5,9,130,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17805

theorem m23424_9 : Upper (D 8) (R 8) [320,5,144,96,9] 13 :=
  permutation_upper _ _ _ [320,5,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18062

theorem m23424_10 : Upper (D 8) (R 8) [320,5,144,96,10] 13 :=
  permutation_upper _ _ _ [320,5,136,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18129

theorem m23424_33 : Upper (D 8) (R 8) [320,5,144,96,33] 13 :=
  permutation_upper _ _ _ [320,5,136,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18135

theorem m23424_34 : Upper (D 8) (R 8) [320,5,144,96,34] 13 :=
  permutation_upper _ _ _ [320,5,136,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18141

theorem m23424_40 : Upper (D 8) (R 8) [320,5,144,96,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18149

theorem m23424_129 : Upper (D 8) (R 8) [320,5,144,96,129] 13 :=
  permutation_upper _ _ _ [320,5,136,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18171

theorem m23424_130 : Upper (D 8) (R 8) [320,5,144,96,130] 13 :=
  permutation_upper _ _ _ [320,5,136,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18173

theorem m23424_136 : Upper (D 8) (R 8) [320,5,144,96,136] 13 :=
  permutation_upper _ _ _ [320,5,136,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18177

theorem m23424_160 : Upper (D 8) (R 8) [320,5,144,96,160] 13 :=
  permutation_upper _ _ _ [320,5,136,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18181

def r23424 : Route 9 := (fun mask => (mask,id))

def c23424 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23424 : Upper (D 8) (R 8) [320,5,144,96] 13 := by
  apply FastRouting.sound _ _ [320,5,144,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23424 c23424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23424_3
  · exact m23424_9
  · exact m23424_10
  · exact m23424_33
  · exact m23424_34
  · exact m23424_40
  · exact m23424_129
  · exact m23424_130
  · exact m23424_136
  · exact m23424_160

theorem m23425_10 : Upper (D 8) (R 8) [320,5,144,129,10] 13 :=
  permutation_upper _ _ _ [320,5,136,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18130

theorem m23425_34 : Upper (D 8) (R 8) [320,5,144,129,34] 13 :=
  permutation_upper _ _ _ [320,5,136,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18142

theorem m23425_40 : Upper (D 8) (R 8) [320,5,144,129,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18150

theorem m23425_66 : Upper (D 8) (R 8) [320,5,144,129,66] 13 :=
  permutation_upper _ _ _ [320,5,136,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18157

theorem m23425_72 : Upper (D 8) (R 8) [320,5,144,129,72] 13 :=
  permutation_upper _ _ _ [320,5,136,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18161

theorem m23425_96 : Upper (D 8) (R 8) [320,5,144,129,96] 13 :=
  permutation_upper _ _ _ [320,5,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18166

def r23425 : Route 9 := (fun mask => (mask,id))

def c23425 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23425 : Upper (D 8) (R 8) [320,5,144,129] 13 := by
  apply FastRouting.sound _ _ [320,5,144,129] 13 (by decide) (choices 2) [10,34,40,66,72,96] r23425 c23425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23425_10
  · exact m23425_34
  · exact m23425_40
  · exact m23425_66
  · exact m23425_72
  · exact m23425_96

def b23426 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 148 138 121 105 105 233 361), lower := (rows 321 7 148 138 16 32 64 128 256), losses := [] }

theorem u23426 : Upper (D 8) (R 8) [320,5,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23427_3 : Upper (D 8) (R 8) [320,5,144,160,3] 13 :=
  permutation_upper _ _ _ [320,5,9,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17806

theorem m23427_9 : Upper (D 8) (R 8) [320,5,144,160,9] 13 :=
  permutation_upper _ _ _ [320,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18125

theorem m23427_10 : Upper (D 8) (R 8) [320,5,144,160,10] 13 :=
  permutation_upper _ _ _ [320,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18131

theorem m23427_33 : Upper (D 8) (R 8) [320,5,144,160,33] 13 :=
  permutation_upper _ _ _ [320,5,136,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18137

theorem m23427_34 : Upper (D 8) (R 8) [320,5,144,160,34] 13 :=
  permutation_upper _ _ _ [320,5,136,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18143

theorem m23427_40 : Upper (D 8) (R 8) [320,5,144,160,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18152

theorem m23427_65 : Upper (D 8) (R 8) [320,5,144,160,65] 13 :=
  permutation_upper _ _ _ [320,5,136,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18155

theorem m23427_66 : Upper (D 8) (R 8) [320,5,144,160,66] 13 :=
  permutation_upper _ _ _ [320,5,136,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18158

theorem m23427_72 : Upper (D 8) (R 8) [320,5,144,160,72] 13 :=
  permutation_upper _ _ _ [320,5,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18163

theorem m23427_96 : Upper (D 8) (R 8) [320,5,144,160,96] 13 :=
  permutation_upper _ _ _ [320,5,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18168

def r23427 : Route 9 := (fun mask => (mask,id))

def c23427 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23427 : Upper (D 8) (R 8) [320,5,144,160] 13 := by
  apply FastRouting.sound _ _ [320,5,144,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23427 c23427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23427_3
  · exact m23427_9
  · exact m23427_10
  · exact m23427_33
  · exact m23427_34
  · exact m23427_40
  · exact m23427_65
  · exact m23427_66
  · exact m23427_72
  · exact m23427_96

theorem m23428_3 : Upper (D 8) (R 8) [320,5,144,192,3] 13 :=
  permutation_upper _ _ _ [320,5,9,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17807

theorem m23428_9 : Upper (D 8) (R 8) [320,5,144,192,9] 13 :=
  permutation_upper _ _ _ [320,5,136,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18126

theorem m23428_10 : Upper (D 8) (R 8) [320,5,144,192,10] 13 :=
  permutation_upper _ _ _ [320,5,136,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18132

theorem m23428_33 : Upper (D 8) (R 8) [320,5,144,192,33] 13 :=
  permutation_upper _ _ _ [320,5,136,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18138

theorem m23428_34 : Upper (D 8) (R 8) [320,5,144,192,34] 13 :=
  permutation_upper _ _ _ [320,5,136,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18144

theorem m23428_40 : Upper (D 8) (R 8) [320,5,144,192,40] 13 :=
  permutation_upper _ _ _ [320,5,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18153

def r23428 : Route 9 := (fun mask => (mask,id))

def c23428 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23428 : Upper (D 8) (R 8) [320,5,144,192] 13 := by
  apply FastRouting.sound _ _ [320,5,144,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23428 c23428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23428_3
  · exact m23428_9
  · exact m23428_10
  · exact m23428_33
  · exact m23428_34
  · exact m23428_40

theorem m23429_10 : Upper (D 8) (R 8) [320,5,160,17,10] 13 :=
  permutation_upper _ _ _ [320,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17820

theorem m23429_34 : Upper (D 8) (R 8) [320,5,160,17,34] 13 :=
  permutation_upper _ _ _ [320,5,40,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17945

theorem m23429_40 : Upper (D 8) (R 8) [320,5,160,17,40] 13 :=
  permutation_upper _ _ _ [320,5,34,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17909

theorem m23429_66 : Upper (D 8) (R 8) [320,5,160,17,66] 13 :=
  permutation_upper _ _ _ [320,5,72,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18038

theorem m23429_72 : Upper (D 8) (R 8) [320,5,160,17,72] 13 :=
  permutation_upper _ _ _ [320,5,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18031

theorem m23429_96 : Upper (D 8) (R 8) [320,5,160,17,96] 13 :=
  permutation_upper _ _ _ [320,5,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18064

theorem m23429_130 : Upper (D 8) (R 8) [320,5,160,17,130] 13 :=
  permutation_upper _ _ _ [320,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18125

theorem m23429_136 : Upper (D 8) (R 8) [320,5,160,17,136] 13 :=
  permutation_upper _ _ _ [320,5,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18104

def r23429 : Route 9 := (fun mask => (mask,id))

def c23429 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23429 : Upper (D 8) (R 8) [320,5,160,17] 13 := by
  apply FastRouting.sound _ _ [320,5,160,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r23429 c23429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23429_10
  · exact m23429_34
  · exact m23429_40
  · exact m23429_66
  · exact m23429_72
  · exact m23429_96
  · exact m23429_130
  · exact m23429_136
  · exact u18184
  · exact u18185

theorem m23430_9 : Upper (D 8) (R 8) [320,5,160,18,9] 13 :=
  permutation_upper _ _ _ [320,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17820

def r23430 : Route 9 := (fun mask => (mask,id))

def c23430 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23430 : Upper (D 8) (R 8) [320,5,160,18] 13 := by
  apply FastRouting.sound _ _ [320,5,160,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23430 c23430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23430_9
  · exact u18186
  · exact u18187
  · exact u18188
  · exact u18189
  · exact u18190
  · exact u18191
  · exact u18192
  · exact u18193
  · exact u18194

theorem m23431_10 : Upper (D 8) (R 8) [320,5,160,33,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18186

def r23431 : Route 9 := (fun mask => (mask,id))

def c23431 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23431 : Upper (D 8) (R 8) [320,5,160,33] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r23431 c23431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23431_10
  · exact u18195
  · exact u18196
  · exact u18197
  · exact u18198
  · exact u18199
  · exact u18200
  · exact u18201
  · exact u18202
  · exact u18203

theorem m23432_9 : Upper (D 8) (R 8) [320,5,160,34,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17945

theorem m23432_33 : Upper (D 8) (R 8) [320,5,160,34,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18195

def r23432 : Route 9 := (fun mask => (mask,id))

def c23432 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23432 : Upper (D 8) (R 8) [320,5,160,34] 13 := by
  apply FastRouting.sound _ _ [320,5,160,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23432 c23432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23432_9
  · exact m23432_33
  · exact u18204
  · exact u18205
  · exact u18206
  · exact u18207
  · exact u18208
  · exact u18209
  · exact u18210
  · exact u18211

theorem m23433_3 : Upper (D 8) (R 8) [320,5,160,48,3] 13 :=
  permutation_upper _ _ _ [320,5,9,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17811

theorem m23433_9 : Upper (D 8) (R 8) [320,5,160,48,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17909

theorem m23433_10 : Upper (D 8) (R 8) [320,5,160,48,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18187

theorem m23433_33 : Upper (D 8) (R 8) [320,5,160,48,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18196

theorem m23433_34 : Upper (D 8) (R 8) [320,5,160,48,34] 13 :=
  permutation_upper _ _ _ [320,5,160,34,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18204

def r23433 : Route 9 := (fun mask => (mask,id))

def c23433 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23433 : Upper (D 8) (R 8) [320,5,160,48] 13 := by
  apply FastRouting.sound _ _ [320,5,160,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r23433 c23433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23433_3
  · exact m23433_9
  · exact m23433_10
  · exact m23433_33
  · exact m23433_34
  · exact u18212
  · exact u18213
  · exact u18214
  · exact u18215
  · exact u18216
  · exact u18217
  · exact u18218
  · exact u18219
  · exact u18220
  · exact u18221

def b23434 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 73 186 186 250 186 442), lower := (rows 321 7 164 73 16 32 64 128 256), losses := [] }

theorem u23434 : Upper (D 8) (R 8) [320,5,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23435_9 : Upper (D 8) (R 8) [320,5,160,66,9] 13 :=
  permutation_upper _ _ _ [320,5,72,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18038

theorem m23435_33 : Upper (D 8) (R 8) [320,5,160,66,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18197

theorem m23435_40 : Upper (D 8) (R 8) [320,5,160,66,40] 13 :=
  permutation_upper _ _ _ [320,5,160,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18214

def r23435 : Route 9 := (fun mask => (mask,id))

def c23435 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23435 : Upper (D 8) (R 8) [320,5,160,66] 13 := by
  apply FastRouting.sound _ _ [320,5,160,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23435 c23435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23435_9
  · exact m23435_33
  · exact m23435_40
  · exact u18223
  · exact u18224
  · exact u18225

theorem m23436_3 : Upper (D 8) (R 8) [320,5,160,80,3] 13 :=
  permutation_upper _ _ _ [320,5,9,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17812

theorem m23436_9 : Upper (D 8) (R 8) [320,5,160,80,9] 13 :=
  permutation_upper _ _ _ [320,5,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18031

theorem m23436_10 : Upper (D 8) (R 8) [320,5,160,80,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18189

theorem m23436_33 : Upper (D 8) (R 8) [320,5,160,80,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18198

theorem m23436_34 : Upper (D 8) (R 8) [320,5,160,80,34] 13 :=
  permutation_upper _ _ _ [320,5,160,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18206

theorem m23436_40 : Upper (D 8) (R 8) [320,5,160,80,40] 13 :=
  permutation_upper _ _ _ [320,5,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18215

def r23436 : Route 9 := (fun mask => (mask,id))

def c23436 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23436 : Upper (D 8) (R 8) [320,5,160,80] 13 := by
  apply FastRouting.sound _ _ [320,5,160,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23436 c23436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23436_3
  · exact m23436_9
  · exact m23436_10
  · exact m23436_33
  · exact m23436_34
  · exact m23436_40
  · exact u18226
  · exact u18227
  · exact u18228
  · exact u18229

theorem m23437_3 : Upper (D 8) (R 8) [320,5,160,96,3] 13 :=
  permutation_upper _ _ _ [320,5,9,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17813

theorem m23437_9 : Upper (D 8) (R 8) [320,5,160,96,9] 13 :=
  permutation_upper _ _ _ [320,5,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18064

theorem m23437_10 : Upper (D 8) (R 8) [320,5,160,96,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18190

theorem m23437_33 : Upper (D 8) (R 8) [320,5,160,96,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18199

theorem m23437_34 : Upper (D 8) (R 8) [320,5,160,96,34] 13 :=
  permutation_upper _ _ _ [320,5,160,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18207

theorem m23437_40 : Upper (D 8) (R 8) [320,5,160,96,40] 13 :=
  permutation_upper _ _ _ [320,5,160,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18216

def r23437 : Route 9 := (fun mask => (mask,id))

def c23437 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23437 : Upper (D 8) (R 8) [320,5,160,96] 13 := by
  apply FastRouting.sound _ _ [320,5,160,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23437 c23437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23437_3
  · exact m23437_9
  · exact m23437_10
  · exact m23437_33
  · exact m23437_34
  · exact m23437_40
  · exact u18230
  · exact u18231
  · exact u18232
  · exact u18233

theorem m23438_10 : Upper (D 8) (R 8) [320,5,160,129,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18191

theorem m23438_34 : Upper (D 8) (R 8) [320,5,160,129,34] 13 :=
  permutation_upper _ _ _ [320,5,160,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18208

theorem m23438_40 : Upper (D 8) (R 8) [320,5,160,129,40] 13 :=
  permutation_upper _ _ _ [320,5,160,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18217

theorem m23438_66 : Upper (D 8) (R 8) [320,5,160,129,66] 13 :=
  permutation_upper _ _ _ [320,5,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18223

theorem m23438_72 : Upper (D 8) (R 8) [320,5,160,129,72] 13 :=
  permutation_upper _ _ _ [320,5,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18226

theorem m23438_96 : Upper (D 8) (R 8) [320,5,160,129,96] 13 :=
  permutation_upper _ _ _ [320,5,160,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18230

def r23438 : Route 9 := (fun mask => (mask,id))

def c23438 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23438 : Upper (D 8) (R 8) [320,5,160,129] 13 := by
  apply FastRouting.sound _ _ [320,5,160,129] 13 (by decide) (choices 2) [10,34,40,66,72,96] r23438 c23438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23438_10
  · exact m23438_34
  · exact m23438_40
  · exact m23438_66
  · exact m23438_72
  · exact m23438_96

def b23439 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 138 121 121 121 249 377), lower := (rows 321 7 164 138 16 32 64 128 256), losses := [] }

theorem u23439 : Upper (D 8) (R 8) [320,5,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23440_3 : Upper (D 8) (R 8) [320,5,160,144,3] 13 :=
  permutation_upper _ _ _ [320,5,9,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17814

theorem m23440_9 : Upper (D 8) (R 8) [320,5,160,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18104

theorem m23440_10 : Upper (D 8) (R 8) [320,5,160,144,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18192

theorem m23440_33 : Upper (D 8) (R 8) [320,5,160,144,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18201

theorem m23440_34 : Upper (D 8) (R 8) [320,5,160,144,34] 13 :=
  permutation_upper _ _ _ [320,5,160,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18209

theorem m23440_40 : Upper (D 8) (R 8) [320,5,160,144,40] 13 :=
  permutation_upper _ _ _ [320,5,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18219

theorem m23440_65 : Upper (D 8) (R 8) [320,5,160,144,65] 13 :=
  permutation_upper _ _ _ [320,5,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18222

theorem m23440_66 : Upper (D 8) (R 8) [320,5,160,144,66] 13 :=
  permutation_upper _ _ _ [320,5,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18224

theorem m23440_72 : Upper (D 8) (R 8) [320,5,160,144,72] 13 :=
  permutation_upper _ _ _ [320,5,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18228

theorem m23440_96 : Upper (D 8) (R 8) [320,5,160,144,96] 13 :=
  permutation_upper _ _ _ [320,5,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18232

def r23440 : Route 9 := (fun mask => (mask,id))

def c23440 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23440 : Upper (D 8) (R 8) [320,5,160,144] 13 := by
  apply FastRouting.sound _ _ [320,5,160,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23440 c23440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23440_3
  · exact m23440_9
  · exact m23440_10
  · exact m23440_33
  · exact m23440_34
  · exact m23440_40
  · exact m23440_65
  · exact m23440_66
  · exact m23440_72
  · exact m23440_96

def b23441 : PairBound 9 := { available := 123, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 164 168 123 123 123 251 379), lower := (rows 321 7 164 168 16 32 64 128 256), losses := [] }

theorem u23441 : Upper (D 8) (R 8) [320,5,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23442_3 : Upper (D 8) (R 8) [320,5,160,192,3] 13 :=
  permutation_upper _ _ _ [320,5,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17815

theorem m23442_9 : Upper (D 8) (R 8) [320,5,160,192,9] 13 :=
  permutation_upper _ _ _ [320,5,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18185

theorem m23442_10 : Upper (D 8) (R 8) [320,5,160,192,10] 13 :=
  permutation_upper _ _ _ [320,5,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18194

theorem m23442_33 : Upper (D 8) (R 8) [320,5,160,192,33] 13 :=
  permutation_upper _ _ _ [320,5,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18203

theorem m23442_34 : Upper (D 8) (R 8) [320,5,160,192,34] 13 :=
  permutation_upper _ _ _ [320,5,160,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18211

theorem m23442_40 : Upper (D 8) (R 8) [320,5,160,192,40] 13 :=
  permutation_upper _ _ _ [320,5,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18221

def r23442 : Route 9 := (fun mask => (mask,id))

def c23442 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23442 : Upper (D 8) (R 8) [320,5,160,192] 13 := by
  apply FastRouting.sound _ _ [320,5,160,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23442 c23442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23442_3
  · exact m23442_9
  · exact m23442_10
  · exact m23442_33
  · exact m23442_34
  · exact m23442_40

def b23443 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 26 185 169 233 169 425), lower := (rows 321 7 196 26 16 32 64 128 256), losses := [] }

theorem u23443 : Upper (D 8) (R 8) [320,5,192,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23444 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 41 186 186 250 186 442), lower := (rows 321 7 196 41 16 32 64 128 256), losses := [] }

theorem u23444 : Upper (D 8) (R 8) [320,5,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23445 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 42 185 185 249 185 441), lower := (rows 321 7 196 42 16 32 64 128 256), losses := [] }

theorem u23445 : Upper (D 8) (R 8) [320,5,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23446 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 137 58 58 122 186 314), lower := (rows 321 7 196 137 16 32 64 128 256), losses := [] }

theorem u23446 : Upper (D 8) (R 8) [320,5,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23447 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 138 57 57 121 185 313), lower := (rows 321 7 196 138 16 32 64 128 256), losses := [] }

theorem u23447 : Upper (D 8) (R 8) [320,5,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23448 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 168 59 59 123 187 315), lower := (rows 321 7 196 168 16 32 64 128 256), losses := [] }

theorem u23448 : Upper (D 8) (R 8) [320,5,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23449 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 21 41 242 226 226 226 482), lower := (rows 321 14 21 41 16 32 64 128 256), losses := [] }

theorem u23449 : Upper (D 8) (R 8) [320,12,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23450_33 : Upper (D 8) (R 8) [320,12,17,34,33] 13 :=
  permutation_upper _ _ _ [320,5,33,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17881

theorem m23450_65 : Upper (D 8) (R 8) [320,12,17,34,65] 13 :=
  permutation_upper _ _ _ [320,5,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18022

theorem m23450_96 : Upper (D 8) (R 8) [320,12,17,34,96] 13 :=
  permutation_upper _ _ _ [320,5,96,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18066

theorem m23450_129 : Upper (D 8) (R 8) [320,12,17,34,129] 13 :=
  permutation_upper _ _ _ [320,5,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18083

theorem m23450_160 : Upper (D 8) (R 8) [320,12,17,34,160] 13 :=
  permutation_upper _ _ _ [320,5,160,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18187

theorem m23450_192 : Upper (D 8) (R 8) [320,12,17,34,192] 13 :=
  permutation_upper _ _ _ [320,5,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18235

def r23450 : Route 9 := (fun mask => (mask,id))

def c23450 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23450 : Upper (D 8) (R 8) [320,12,17,34] 13 := by
  apply FastRouting.sound _ _ [320,12,17,34] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23450 c23450
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23450_33
  · exact m23450_65
  · exact m23450_96
  · exact m23450_129
  · exact m23450_160
  · exact m23450_192

theorem m23451_3 : Upper (D 8) (R 8) [320,12,17,96,3] 13 :=
  permutation_upper _ _ _ [320,5,9,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17789

theorem m23451_33 : Upper (D 8) (R 8) [320,12,17,96,33] 13 :=
  permutation_upper _ _ _ [320,5,33,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17882

theorem m23451_34 : Upper (D 8) (R 8) [320,12,17,96,34] 13 :=
  permutation_upper _ _ _ [320,5,40,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17949

theorem m23451_129 : Upper (D 8) (R 8) [320,12,17,96,129] 13 :=
  permutation_upper _ _ _ [320,5,129,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18084

theorem m23451_130 : Upper (D 8) (R 8) [320,12,17,96,130] 13 :=
  permutation_upper _ _ _ [320,5,136,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18129

theorem m23451_160 : Upper (D 8) (R 8) [320,12,17,96,160] 13 :=
  permutation_upper _ _ _ [320,5,160,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18190

def r23451 : Route 9 := (fun mask => (mask,id))

def c23451 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23451 : Upper (D 8) (R 8) [320,12,17,96] 13 := by
  apply FastRouting.sound _ _ [320,12,17,96] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23451 c23451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23451_3
  · exact m23451_33
  · exact m23451_34
  · exact m23451_129
  · exact m23451_130
  · exact m23451_160

def b23452 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 21 137 242 226 226 226 482), lower := (rows 321 14 21 137 16 32 64 128 256), losses := [] }

theorem u23452 : Upper (D 8) (R 8) [320,12,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23453_33 : Upper (D 8) (R 8) [320,12,17,130,33] 13 :=
  permutation_upper _ _ _ [320,5,33,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17883

theorem m23453_65 : Upper (D 8) (R 8) [320,12,17,130,65] 13 :=
  permutation_upper _ _ _ [320,5,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18023

theorem m23453_96 : Upper (D 8) (R 8) [320,12,17,130,96] 13 :=
  permutation_upper _ _ _ [320,5,96,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18068

theorem m23453_129 : Upper (D 8) (R 8) [320,12,17,130,129] 13 :=
  permutation_upper _ _ _ [320,5,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18085

theorem m23453_160 : Upper (D 8) (R 8) [320,12,17,130,160] 13 :=
  permutation_upper _ _ _ [320,5,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18192

theorem m23453_192 : Upper (D 8) (R 8) [320,12,17,130,192] 13 :=
  permutation_upper _ _ _ [320,5,192,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18237

def r23453 : Route 9 := (fun mask => (mask,id))

def c23453 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23453 : Upper (D 8) (R 8) [320,12,17,130] 13 := by
  apply FastRouting.sound _ _ [320,12,17,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23453 c23453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23453_33
  · exact m23453_65
  · exact m23453_96
  · exact m23453_129
  · exact m23453_160
  · exact m23453_192

theorem m23454_3 : Upper (D 8) (R 8) [320,12,17,160,3] 13 :=
  permutation_upper _ _ _ [320,5,9,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17790

theorem m23454_33 : Upper (D 8) (R 8) [320,12,17,160,33] 13 :=
  permutation_upper _ _ _ [320,5,33,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17884

theorem m23454_34 : Upper (D 8) (R 8) [320,12,17,160,34] 13 :=
  permutation_upper _ _ _ [320,5,40,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17951

theorem m23454_65 : Upper (D 8) (R 8) [320,12,17,160,65] 13 :=
  permutation_upper _ _ _ [320,5,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18024

theorem m23454_66 : Upper (D 8) (R 8) [320,12,17,160,66] 13 :=
  permutation_upper _ _ _ [320,5,72,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18041

theorem m23454_96 : Upper (D 8) (R 8) [320,12,17,160,96] 13 :=
  permutation_upper _ _ _ [320,5,96,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18069

theorem m23454_129 : Upper (D 8) (R 8) [320,12,17,160,129] 13 :=
  permutation_upper _ _ _ [320,5,129,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18086

theorem m23454_130 : Upper (D 8) (R 8) [320,12,17,160,130] 13 :=
  permutation_upper _ _ _ [320,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18131

theorem m23454_160 : Upper (D 8) (R 8) [320,12,17,160,160] 13 :=
  permutation_upper _ _ _ [320,5,160,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18193

theorem m23454_192 : Upper (D 8) (R 8) [320,12,17,160,192] 13 :=
  permutation_upper _ _ _ [320,5,192,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18238

def r23454 : Route 9 := (fun mask => (mask,id))

def c23454 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23454 : Upper (D 8) (R 8) [320,12,17,160] 13 := by
  apply FastRouting.sound _ _ [320,12,17,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23454 c23454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23454_3
  · exact m23454_33
  · exact m23454_34
  · exact m23454_65
  · exact m23454_66
  · exact m23454_96
  · exact m23454_129
  · exact m23454_130
  · exact m23454_160
  · exact m23454_192

theorem m23455_3 : Upper (D 8) (R 8) [320,12,17,192,3] 13 :=
  permutation_upper _ _ _ [320,5,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17791

theorem m23455_33 : Upper (D 8) (R 8) [320,12,17,192,33] 13 :=
  permutation_upper _ _ _ [320,5,33,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17885

theorem m23455_34 : Upper (D 8) (R 8) [320,12,17,192,34] 13 :=
  permutation_upper _ _ _ [320,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17952

theorem m23455_129 : Upper (D 8) (R 8) [320,12,17,192,129] 13 :=
  permutation_upper _ _ _ [320,5,129,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18087

theorem m23455_130 : Upper (D 8) (R 8) [320,12,17,192,130] 13 :=
  permutation_upper _ _ _ [320,5,136,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18132

theorem m23455_160 : Upper (D 8) (R 8) [320,12,17,192,160] 13 :=
  permutation_upper _ _ _ [320,5,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18194

def r23455 : Route 9 := (fun mask => (mask,id))

def c23455 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23455 : Upper (D 8) (R 8) [320,12,17,192] 13 := by
  apply FastRouting.sound _ _ [320,12,17,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23455 c23455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23455_3
  · exact m23455_33
  · exact m23455_34
  · exact m23455_129
  · exact m23455_130
  · exact m23455_160

def r23456 : Route 9 := (fun mask => (mask,id))

def c23456 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23456 : Upper (D 8) (R 8) [320,12,18,33] 13 := by
  apply FastRouting.sound _ _ [320,12,18,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23456 c23456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18249
  · exact u18250
  · exact u18251
  · exact u18252
  · exact u18253
  · exact u18254

def b23457 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 73 177 161 225 161 417), lower := (rows 321 14 22 73 16 32 64 128 256), losses := [] }

theorem u23457 : Upper (D 8) (R 8) [320,12,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23458 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 22 104 177 161 225 161 417), lower := (rows 321 14 22 104 16 32 64 128 256), losses := [] }

theorem u23458 : Upper (D 8) (R 8) [320,12,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23459_33 : Upper (D 8) (R 8) [320,12,18,129,33] 13 :=
  permutation_upper _ _ _ [320,12,18,33,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18252

theorem m23459_65 : Upper (D 8) (R 8) [320,12,18,129,65] 13 :=
  permutation_upper _ _ _ [320,12,18,65,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18255

theorem m23459_96 : Upper (D 8) (R 8) [320,12,18,129,96] 13 :=
  permutation_upper _ _ _ [320,12,18,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18257

def r23459 : Route 9 := (fun mask => (mask,id))

def c23459 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23459 : Upper (D 8) (R 8) [320,12,18,129] 13 := by
  apply FastRouting.sound _ _ [320,12,18,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23459 c23459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23459_33
  · exact m23459_65
  · exact m23459_96
  · exact u18259
  · exact u18260
  · exact u18261

#print axioms u23459
end Delivery.IrregularNine14.P08
