import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0250
import IrregularNine14P08C0251
import IrregularNine14P08C0252
import IrregularNine14P08C0253
import IrregularNine14P08C0254
import IrregularNine14P08C0255
import IrregularNine14P08C0256
import IrregularNine14P08C0257
import IrregularNine14P08C0258
import IrregularNine14P08C0260
import IrregularNine14P08C0261
import IrregularNine14P08C0262

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22140 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 104 433 433 497 433 433), lower := (rows 193 14 38 104 16 32 64 128 256), losses := [] }

theorem u22140 : Upper (D 8) (R 8) [192,12,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22141 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 38 200 305 305 369 433 305), lower := (rows 193 14 38 200 16 32 64 128 256), losses := [] }

theorem u22141 : Upper (D 8) (R 8) [192,12,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22142 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22142 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22142 : Upper (D 8) (R 8) [192,12,34,257] 13 := by
  apply FastRouting.sound _ _ [192,12,34,257] 13 (by decide) (choices 2) [33,65,96,192] r22142 c22142
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15646
  · exact u15647
  · exact u15648
  · exact u15649

def r22143 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22143 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22143 : Upper (D 8) (R 8) [192,12,34,272] 13 := by
  apply FastRouting.sound _ _ [192,12,34,272] 13 (by decide) (choices 2) [33,65,96,192] r22143 c22143
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15650
  · exact u15651
  · exact u15652
  · exact u15653

def b22144 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 296 241 241 241 241 497), lower := (rows 193 14 38 296 16 32 64 128 256), losses := [] }

theorem u22144 : Upper (D 8) (R 8) [192,12,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22145 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 328 177 177 241 177 433), lower := (rows 193 14 38 328 16 32 64 128 256), losses := [] }

theorem u22145 : Upper (D 8) (R 8) [192,12,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22146 : PairBound 9 := { available := 419, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 73 435 419 483 419 419), lower := (rows 193 14 52 73 16 32 64 128 256), losses := [] }

theorem u22146 : Upper (D 8) (R 8) [192,12,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22147 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 52 74 433 417 481 417 417), lower := (rows 193 14 52 74 16 32 64 128 256), losses := [] }

theorem u22147 : Upper (D 8) (R 8) [192,12,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22148_3 : Upper (D 8) (R 8) [192,12,48,96,3] 13 :=
  permutation_upper _ _ _ [192,5,24,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15127

def r22148 : Route 9 := (fun mask => (mask,id))

def c22148 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22148 : Upper (D 8) (R 8) [192,12,48,96] 13 := by
  apply FastRouting.sound _ _ [192,12,48,96] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r22148 c22148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22148_3
  · exact u15663
  · exact u15664
  · exact u15665
  · exact u15666
  · exact u15667
  · exact u15668
  · exact u15669
  · exact u15670
  · exact u15671

def b22149 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 52 200 307 291 355 419 291), lower := (rows 193 14 52 200 16 32 64 128 256), losses := [] }

theorem u22149 : Upper (D 8) (R 8) [192,12,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22150_3 : Upper (D 8) (R 8) [192,12,48,257,3] 13 :=
  permutation_upper _ _ _ [192,5,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15129

def r22150 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22150 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22150 : Upper (D 8) (R 8) [192,12,48,257] 13 := by
  apply FastRouting.sound _ _ [192,12,48,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22150 c22150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22150_3
  · exact u15674
  · exact u15675
  · exact u15676
  · exact u15677
  · exact u15678
  · exact u15679

def r22151 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22151 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22151 : Upper (D 8) (R 8) [192,12,48,258] 13 := by
  apply FastRouting.sound _ _ [192,12,48,258] 13 (by decide) (choices 2) [33,65,96,192] r22151 c22151
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15680
  · exact u15681
  · exact u15682
  · exact u15683

theorem m22152_3 : Upper (D 8) (R 8) [192,12,48,288,3] 13 :=
  permutation_upper _ _ _ [192,5,24,34,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15130

def r22152 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22152 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22152 : Upper (D 8) (R 8) [192,12,48,288] 13 := by
  apply FastRouting.sound _ _ [192,12,48,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22152 c22152
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22152_3
  · exact u15684
  · exact u15685
  · exact u15686
  · exact u15687
  · exact u15688
  · exact u15689

theorem m22153_3 : Upper (D 8) (R 8) [192,12,48,320,3] 13 :=
  permutation_upper _ _ _ [192,5,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15131

def r22153 : Route 9 := (fun mask => (mask,id))

def c22153 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22153 : Upper (D 8) (R 8) [192,12,48,320] 13 := by
  apply FastRouting.sound _ _ [192,12,48,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22153 c22153
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22153_3
  · exact u15690
  · exact u15691
  · exact u15692
  · exact u15693
  · exact u15694

def b22154 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 152 307 291 355 419 291), lower := (rows 193 14 69 152 16 32 64 128 256), losses := [] }

theorem u22154 : Upper (D 8) (R 8) [192,12,65,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22155 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 168 307 307 371 435 307), lower := (rows 193 14 69 168 16 32 64 128 256), losses := [] }

theorem u22155 : Upper (D 8) (R 8) [192,12,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22156 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 265 178 178 242 178 434), lower := (rows 193 14 69 265 16 32 64 128 256), losses := [] }

theorem u22156 : Upper (D 8) (R 8) [192,12,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22157 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 266 177 177 241 177 433), lower := (rows 193 14 69 266 16 32 64 128 256), losses := [] }

theorem u22157 : Upper (D 8) (R 8) [192,12,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22158 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 280 179 163 227 163 419), lower := (rows 193 14 69 280 16 32 64 128 256), losses := [] }

theorem u22158 : Upper (D 8) (R 8) [192,12,65,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22159 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 296 179 179 243 179 435), lower := (rows 193 14 69 296 16 32 64 128 256), losses := [] }

theorem u22159 : Upper (D 8) (R 8) [192,12,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22160 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 392 51 51 115 179 307), lower := (rows 193 14 69 392 16 32 64 128 256), losses := [] }

theorem u22160 : Upper (D 8) (R 8) [192,12,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22161 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 152 305 289 353 417 289), lower := (rows 193 14 70 152 16 32 64 128 256), losses := [] }

theorem u22161 : Upper (D 8) (R 8) [192,12,66,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22162 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 168 305 305 369 433 305), lower := (rows 193 14 70 168 16 32 64 128 256), losses := [] }

theorem u22162 : Upper (D 8) (R 8) [192,12,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22163 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 265 177 177 241 177 433), lower := (rows 193 14 70 265 16 32 64 128 256), losses := [] }

theorem u22163 : Upper (D 8) (R 8) [192,12,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22164 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 280 177 161 225 161 417), lower := (rows 193 14 70 280 16 32 64 128 256), losses := [] }

theorem u22164 : Upper (D 8) (R 8) [192,12,66,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22165 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 296 177 177 241 177 433), lower := (rows 193 14 70 296 16 32 64 128 256), losses := [] }

theorem u22165 : Upper (D 8) (R 8) [192,12,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22166 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 392 49 49 113 177 305), lower := (rows 193 14 70 392 16 32 64 128 256), losses := [] }

theorem u22166 : Upper (D 8) (R 8) [192,12,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22167_3 : Upper (D 8) (R 8) [192,12,80,160,3] 13 :=
  permutation_upper _ _ _ [192,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15134

def r22167 : Route 9 := (fun mask => (mask,id))

def c22167 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22167 : Upper (D 8) (R 8) [192,12,80,160] 13 := by
  apply FastRouting.sound _ _ [192,12,80,160] 13 (by decide) (choices 2) [3,33,34,257,258,288] r22167 c22167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22167_3
  · exact u15730
  · exact u15731
  · exact u15732
  · exact u15733
  · exact u15734

theorem m22168_3 : Upper (D 8) (R 8) [192,12,80,257,3] 13 :=
  permutation_upper _ _ _ [192,5,24,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15135

def r22168 : Route 9 := (fun mask => (mask,id))

def c22168 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22168 : Upper (D 8) (R 8) [192,12,80,257] 13 := by
  apply FastRouting.sound _ _ [192,12,80,257] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22168 c22168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22168_3
  · exact u15735
  · exact u15736
  · exact u15737
  · exact u15738
  · exact u15739

def b22169 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 84 266 177 161 225 161 417), lower := (rows 193 14 84 266 16 32 64 128 256), losses := [] }

theorem u22169 : Upper (D 8) (R 8) [192,12,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22170_3 : Upper (D 8) (R 8) [192,12,80,288,3] 13 :=
  permutation_upper _ _ _ [192,5,24,66,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15136

def r22170 : Route 9 := (fun mask => (mask,id))

def c22170 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22170 : Upper (D 8) (R 8) [192,12,80,288] 13 := by
  apply FastRouting.sound _ _ [192,12,80,288] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22170 c22170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22170_3
  · exact u15742
  · exact u15743
  · exact u15744
  · exact u15745
  · exact u15746

theorem m22171_3 : Upper (D 8) (R 8) [192,12,80,384,3] 13 :=
  permutation_upper _ _ _ [192,5,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15137

def r22171 : Route 9 := (fun mask => (mask,id))

def c22171 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22171 : Upper (D 8) (R 8) [192,12,80,384] 13 := by
  apply FastRouting.sound _ _ [192,12,80,384] 13 (by decide) (choices 2) [3,33,34] r22171 c22171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22171_3
  · exact u15747
  · exact u15748

theorem m22172_3 : Upper (D 8) (R 8) [192,12,96,160,3] 13 :=
  permutation_upper _ _ _ [192,5,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15138

def r22172 : Route 9 := (fun mask => (mask,id))

def c22172 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22172 : Upper (D 8) (R 8) [192,12,96,160] 13 := by
  apply FastRouting.sound _ _ [192,12,96,160] 13 (by decide) (choices 2) [3,33,34,257,258,288] r22172 c22172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22172_3
  · exact u15749
  · exact u15750
  · exact u15751
  · exact u15752
  · exact u15753

theorem m22173_3 : Upper (D 8) (R 8) [192,12,96,257,3] 13 :=
  permutation_upper _ _ _ [192,5,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15139

def r22173 : Route 9 := (fun mask => (mask,id))

def c22173 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22173 : Upper (D 8) (R 8) [192,12,96,257] 13 := by
  apply FastRouting.sound _ _ [192,12,96,257] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22173 c22173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22173_3
  · exact u15754
  · exact u15755
  · exact u15756
  · exact u15757
  · exact u15758

def b22174 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 100 266 177 177 241 177 433), lower := (rows 193 14 100 266 16 32 64 128 256), losses := [] }

theorem u22174 : Upper (D 8) (R 8) [192,12,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22175_3 : Upper (D 8) (R 8) [192,12,96,272,3] 13 :=
  permutation_upper _ _ _ [192,5,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15140

def r22175 : Route 9 := (fun mask => (mask,id))

def c22175 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22175 : Upper (D 8) (R 8) [192,12,96,272] 13 := by
  apply FastRouting.sound _ _ [192,12,96,272] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22175 c22175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22175_3
  · exact u15761
  · exact u15762
  · exact u15763
  · exact u15764
  · exact u15765

theorem m22176_3 : Upper (D 8) (R 8) [192,12,96,288,3] 13 :=
  permutation_upper _ _ _ [192,5,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15141

def r22176 : Route 9 := (fun mask => (mask,id))

def c22176 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22176 : Upper (D 8) (R 8) [192,12,96,288] 13 := by
  apply FastRouting.sound _ _ [192,12,96,288] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22176 c22176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22176_3
  · exact u15766
  · exact u15767
  · exact u15768
  · exact u15769
  · exact u15770

theorem m22177_3 : Upper (D 8) (R 8) [192,12,96,384,3] 13 :=
  permutation_upper _ _ _ [192,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15142

def r22177 : Route 9 := (fun mask => (mask,id))

def c22177 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22177 : Upper (D 8) (R 8) [192,12,96,384] 13 := by
  apply FastRouting.sound _ _ [192,12,96,384] 13 (by decide) (choices 2) [3,33,34] r22177 c22177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22177_3
  · exact u15771
  · exact u15772

def b22178 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 265 51 51 115 179 307), lower := (rows 193 14 196 265 16 32 64 128 256), losses := [] }

theorem u22178 : Upper (D 8) (R 8) [192,12,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22179 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 266 49 49 113 177 305), lower := (rows 193 14 196 266 16 32 64 128 256), losses := [] }

theorem u22179 : Upper (D 8) (R 8) [192,12,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22180 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 280 51 35 99 163 291), lower := (rows 193 14 196 280 16 32 64 128 256), losses := [] }

theorem u22180 : Upper (D 8) (R 8) [192,12,192,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22181 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 296 51 51 115 179 307), lower := (rows 193 14 196 296 16 32 64 128 256), losses := [] }

theorem u22181 : Upper (D 8) (R 8) [192,12,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22182_12 : Upper (D 8) (R 8) [192,17,33,34,12] 13 :=
  permutation_upper _ _ _ [192,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15120

theorem m22182_36 : Upper (D 8) (R 8) [192,17,33,34,36] 13 :=
  permutation_upper _ _ _ [192,5,40,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15225

theorem m22182_40 : Upper (D 8) (R 8) [192,17,33,34,40] 13 :=
  permutation_upper _ _ _ [192,5,40,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15231

theorem m22182_68 : Upper (D 8) (R 8) [192,17,33,34,68] 13 :=
  permutation_upper _ _ _ [192,5,72,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15340

theorem m22182_72 : Upper (D 8) (R 8) [192,17,33,34,72] 13 :=
  permutation_upper _ _ _ [192,5,72,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15346

theorem m22182_96 : Upper (D 8) (R 8) [192,17,33,34,96] 13 :=
  permutation_upper _ _ _ [192,5,96,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15393

theorem m22182_192 : Upper (D 8) (R 8) [192,17,33,34,192] 13 :=
  permutation_upper _ _ _ [192,5,192,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15426

theorem m22182_260 : Upper (D 8) (R 8) [192,17,33,34,260] 13 :=
  permutation_upper _ _ _ [192,5,264,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15462

theorem m22182_264 : Upper (D 8) (R 8) [192,17,33,34,264] 13 :=
  permutation_upper _ _ _ [192,5,264,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15465

theorem m22182_288 : Upper (D 8) (R 8) [192,17,33,34,288] 13 :=
  permutation_upper _ _ _ [192,5,288,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15496

theorem m22182_320 : Upper (D 8) (R 8) [192,17,33,34,320] 13 :=
  permutation_upper _ _ _ [192,5,320,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15524

def r22182 : Route 9 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22182 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u22182 : Upper (D 8) (R 8) [192,17,33,34] 13 := by
  apply FastRouting.sound _ _ [192,17,33,34] 13 (by decide) (choices 2) [12,36,40,68,72,96,192,260,264,288,320] r22182 c22182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22182_12
  · exact m22182_36
  · exact m22182_40
  · exact m22182_68
  · exact m22182_72
  · exact m22182_96
  · exact m22182_192
  · exact m22182_260
  · exact m22182_264
  · exact m22182_288
  · exact m22182_320

theorem m22183_12 : Upper (D 8) (R 8) [192,17,33,66,12] 13 :=
  permutation_upper _ _ _ [192,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15121

theorem m22183_36 : Upper (D 8) (R 8) [192,17,33,66,36] 13 :=
  permutation_upper _ _ _ [192,5,40,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15226

theorem m22183_40 : Upper (D 8) (R 8) [192,17,33,66,40] 13 :=
  permutation_upper _ _ _ [192,5,40,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15250

theorem m22183_132 : Upper (D 8) (R 8) [192,17,33,66,132] 13 :=
  permutation_upper _ _ _ [192,5,72,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15341

theorem m22183_136 : Upper (D 8) (R 8) [192,17,33,66,136] 13 :=
  permutation_upper _ _ _ [192,5,72,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15355

theorem m22183_160 : Upper (D 8) (R 8) [192,17,33,66,160] 13 :=
  permutation_upper _ _ _ [192,5,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15394

theorem m22183_260 : Upper (D 8) (R 8) [192,17,33,66,260] 13 :=
  permutation_upper _ _ _ [192,5,264,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15463

theorem m22183_264 : Upper (D 8) (R 8) [192,17,33,66,264] 13 :=
  permutation_upper _ _ _ [192,5,264,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15478

theorem m22183_288 : Upper (D 8) (R 8) [192,17,33,66,288] 13 :=
  permutation_upper _ _ _ [192,5,288,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15498

theorem m22183_384 : Upper (D 8) (R 8) [192,17,33,66,384] 13 :=
  permutation_upper _ _ _ [192,5,320,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15525

def r22183 : Route 9 := (fun mask => (mask,id))

def c22183 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22183 : Upper (D 8) (R 8) [192,17,33,66] 13 := by
  apply FastRouting.sound _ _ [192,17,33,66] 13 (by decide) (choices 2) [12,36,40,132,136,160,260,264,288,384] r22183 c22183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22183_12
  · exact m22183_36
  · exact m22183_40
  · exact m22183_132
  · exact m22183_136
  · exact m22183_160
  · exact m22183_260
  · exact m22183_264
  · exact m22183_288
  · exact m22183_384

theorem m22184_10 : Upper (D 8) (R 8) [192,17,33,68,10] 13 :=
  permutation_upper _ _ _ [192,5,10,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15098

theorem m22184_34 : Upper (D 8) (R 8) [192,17,33,68,34] 13 :=
  permutation_upper _ _ _ [192,5,34,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15180

theorem m22184_40 : Upper (D 8) (R 8) [192,17,33,68,40] 13 :=
  permutation_upper _ _ _ [192,5,40,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15255

theorem m22184_130 : Upper (D 8) (R 8) [192,17,33,68,130] 13 :=
  permutation_upper _ _ _ [192,5,66,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15320

theorem m22184_136 : Upper (D 8) (R 8) [192,17,33,68,136] 13 :=
  permutation_upper _ _ _ [192,5,72,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15358

theorem m22184_160 : Upper (D 8) (R 8) [192,17,33,68,160] 13 :=
  permutation_upper _ _ _ [192,5,96,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15395

theorem m22184_258 : Upper (D 8) (R 8) [192,17,33,68,258] 13 :=
  permutation_upper _ _ _ [192,5,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15446

theorem m22184_264 : Upper (D 8) (R 8) [192,17,33,68,264] 13 :=
  permutation_upper _ _ _ [192,5,264,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15480

theorem m22184_288 : Upper (D 8) (R 8) [192,17,33,68,288] 13 :=
  permutation_upper _ _ _ [192,5,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15499

theorem m22184_384 : Upper (D 8) (R 8) [192,17,33,68,384] 13 :=
  permutation_upper _ _ _ [192,5,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15526

def r22184 : Route 9 := (fun mask => (mask,id))

def c22184 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22184 : Upper (D 8) (R 8) [192,17,33,68] 13 := by
  apply FastRouting.sound _ _ [192,17,33,68] 13 (by decide) (choices 2) [10,34,40,130,136,160,258,264,288,384] r22184 c22184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22184_10
  · exact m22184_34
  · exact m22184_40
  · exact m22184_130
  · exact m22184_136
  · exact m22184_160
  · exact m22184_258
  · exact m22184_264
  · exact m22184_288
  · exact m22184_384

theorem m22185_6 : Upper (D 8) (R 8) [192,17,33,96,6] 13 :=
  permutation_upper _ _ _ [192,5,10,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15085

theorem m22185_10 : Upper (D 8) (R 8) [192,17,33,96,10] 13 :=
  permutation_upper _ _ _ [192,5,10,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15103

theorem m22185_12 : Upper (D 8) (R 8) [192,17,33,96,12] 13 :=
  permutation_upper _ _ _ [192,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15122

theorem m22185_34 : Upper (D 8) (R 8) [192,17,33,96,34] 13 :=
  permutation_upper _ _ _ [192,5,34,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15181

theorem m22185_36 : Upper (D 8) (R 8) [192,17,33,96,36] 13 :=
  permutation_upper _ _ _ [192,5,40,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15227

theorem m22185_40 : Upper (D 8) (R 8) [192,17,33,96,40] 13 :=
  permutation_upper _ _ _ [192,5,40,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15263

theorem m22185_130 : Upper (D 8) (R 8) [192,17,33,96,130] 13 :=
  permutation_upper _ _ _ [192,5,66,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15321

theorem m22185_132 : Upper (D 8) (R 8) [192,17,33,96,132] 13 :=
  permutation_upper _ _ _ [192,5,72,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15342

theorem m22185_136 : Upper (D 8) (R 8) [192,17,33,96,136] 13 :=
  permutation_upper _ _ _ [192,5,72,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15363

theorem m22185_160 : Upper (D 8) (R 8) [192,17,33,96,160] 13 :=
  permutation_upper _ _ _ [192,5,96,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15396

theorem m22185_258 : Upper (D 8) (R 8) [192,17,33,96,258] 13 :=
  permutation_upper _ _ _ [192,5,258,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15447

theorem m22185_260 : Upper (D 8) (R 8) [192,17,33,96,260] 13 :=
  permutation_upper _ _ _ [192,5,264,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15464

theorem m22185_264 : Upper (D 8) (R 8) [192,17,33,96,264] 13 :=
  permutation_upper _ _ _ [192,5,264,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15484

theorem m22185_288 : Upper (D 8) (R 8) [192,17,33,96,288] 13 :=
  permutation_upper _ _ _ [192,5,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15500

theorem m22185_384 : Upper (D 8) (R 8) [192,17,33,96,384] 13 :=
  permutation_upper _ _ _ [192,5,320,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15527

def r22185 : Route 9 := (fun mask => (mask,id))

def c22185 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22185 : Upper (D 8) (R 8) [192,17,33,96] 13 := by
  apply FastRouting.sound _ _ [192,17,33,96] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,258,260,264,288,384] r22185 c22185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22185_6
  · exact m22185_10
  · exact m22185_12
  · exact m22185_34
  · exact m22185_36
  · exact m22185_40
  · exact m22185_130
  · exact m22185_132
  · exact m22185_136
  · exact m22185_160
  · exact m22185_258
  · exact m22185_260
  · exact m22185_264
  · exact m22185_288
  · exact m22185_384

theorem m22186_12 : Upper (D 8) (R 8) [192,17,33,258,12] 13 :=
  permutation_upper _ _ _ [192,5,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15123

theorem m22186_36 : Upper (D 8) (R 8) [192,17,33,258,36] 13 :=
  permutation_upper _ _ _ [192,5,40,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15228

theorem m22186_40 : Upper (D 8) (R 8) [192,17,33,258,40] 13 :=
  permutation_upper _ _ _ [192,5,40,258,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15279

theorem m22186_68 : Upper (D 8) (R 8) [192,17,33,258,68] 13 :=
  permutation_upper _ _ _ [192,5,72,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15343

theorem m22186_72 : Upper (D 8) (R 8) [192,17,33,258,72] 13 :=
  permutation_upper _ _ _ [192,5,72,258,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15371

theorem m22186_96 : Upper (D 8) (R 8) [192,17,33,258,96] 13 :=
  permutation_upper _ _ _ [192,5,96,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15397

theorem m22186_192 : Upper (D 8) (R 8) [192,17,33,258,192] 13 :=
  permutation_upper _ _ _ [192,5,192,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15427

def r22186 : Route 9 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22186 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22186 : Upper (D 8) (R 8) [192,17,33,258] 13 := by
  apply FastRouting.sound _ _ [192,17,33,258] 13 (by decide) (choices 2) [12,36,40,68,72,96,192] r22186 c22186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22186_12
  · exact m22186_36
  · exact m22186_40
  · exact m22186_68
  · exact m22186_72
  · exact m22186_96
  · exact m22186_192

theorem m22187_10 : Upper (D 8) (R 8) [192,17,33,260,10] 13 :=
  permutation_upper _ _ _ [192,5,10,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15110

theorem m22187_34 : Upper (D 8) (R 8) [192,17,33,260,34] 13 :=
  permutation_upper _ _ _ [192,5,34,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15182

theorem m22187_40 : Upper (D 8) (R 8) [192,17,33,260,40] 13 :=
  permutation_upper _ _ _ [192,5,40,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15283

theorem m22187_66 : Upper (D 8) (R 8) [192,17,33,260,66] 13 :=
  permutation_upper _ _ _ [192,5,66,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15322

theorem m22187_72 : Upper (D 8) (R 8) [192,17,33,260,72] 13 :=
  permutation_upper _ _ _ [192,5,72,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15373

theorem m22187_96 : Upper (D 8) (R 8) [192,17,33,260,96] 13 :=
  permutation_upper _ _ _ [192,5,96,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15398

theorem m22187_192 : Upper (D 8) (R 8) [192,17,33,260,192] 13 :=
  permutation_upper _ _ _ [192,5,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15428

def r22187 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22187 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22187 : Upper (D 8) (R 8) [192,17,33,260] 13 := by
  apply FastRouting.sound _ _ [192,17,33,260] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r22187 c22187
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22187_10
  · exact m22187_34
  · exact m22187_40
  · exact m22187_66
  · exact m22187_72
  · exact m22187_96
  · exact m22187_192

theorem m22188_6 : Upper (D 8) (R 8) [192,17,33,288,6] 13 :=
  permutation_upper _ _ _ [192,5,10,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15086

theorem m22188_10 : Upper (D 8) (R 8) [192,17,33,288,10] 13 :=
  permutation_upper _ _ _ [192,5,10,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15114

theorem m22188_12 : Upper (D 8) (R 8) [192,17,33,288,12] 13 :=
  permutation_upper _ _ _ [192,5,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15124

theorem m22188_34 : Upper (D 8) (R 8) [192,17,33,288,34] 13 :=
  permutation_upper _ _ _ [192,5,34,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15183

theorem m22188_36 : Upper (D 8) (R 8) [192,17,33,288,36] 13 :=
  permutation_upper _ _ _ [192,5,40,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15229

theorem m22188_40 : Upper (D 8) (R 8) [192,17,33,288,40] 13 :=
  permutation_upper _ _ _ [192,5,40,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15289

theorem m22188_66 : Upper (D 8) (R 8) [192,17,33,288,66] 13 :=
  permutation_upper _ _ _ [192,5,66,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15323

theorem m22188_68 : Upper (D 8) (R 8) [192,17,33,288,68] 13 :=
  permutation_upper _ _ _ [192,5,72,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15344

theorem m22188_72 : Upper (D 8) (R 8) [192,17,33,288,72] 13 :=
  permutation_upper _ _ _ [192,5,72,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15377

theorem m22188_96 : Upper (D 8) (R 8) [192,17,33,288,96] 13 :=
  permutation_upper _ _ _ [192,5,96,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15399

theorem m22188_192 : Upper (D 8) (R 8) [192,17,33,288,192] 13 :=
  permutation_upper _ _ _ [192,5,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15429

def r22188 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22188 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22188 : Upper (D 8) (R 8) [192,17,33,288] 13 := by
  apply FastRouting.sound _ _ [192,17,33,288] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,192] r22188 c22188
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22188_6
  · exact m22188_10
  · exact m22188_12
  · exact m22188_34
  · exact m22188_36
  · exact m22188_40
  · exact m22188_66
  · exact m22188_68
  · exact m22188_72
  · exact m22188_96
  · exact m22188_192

theorem m22189_6 : Upper (D 8) (R 8) [192,17,33,320,6] 13 :=
  permutation_upper _ _ _ [192,5,10,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15087

theorem m22189_10 : Upper (D 8) (R 8) [192,17,33,320,10] 13 :=
  permutation_upper _ _ _ [192,5,10,320,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15118

theorem m22189_12 : Upper (D 8) (R 8) [192,17,33,320,12] 13 :=
  permutation_upper _ _ _ [192,5,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15125

theorem m22189_34 : Upper (D 8) (R 8) [192,17,33,320,34] 13 :=
  permutation_upper _ _ _ [192,5,34,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15184

theorem m22189_36 : Upper (D 8) (R 8) [192,17,33,320,36] 13 :=
  permutation_upper _ _ _ [192,5,40,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15230

theorem m22189_40 : Upper (D 8) (R 8) [192,17,33,320,40] 13 :=
  permutation_upper _ _ _ [192,5,40,320,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15293

theorem m22189_130 : Upper (D 8) (R 8) [192,17,33,320,130] 13 :=
  permutation_upper _ _ _ [192,5,66,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15324

theorem m22189_132 : Upper (D 8) (R 8) [192,17,33,320,132] 13 :=
  permutation_upper _ _ _ [192,5,72,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15345

theorem m22189_136 : Upper (D 8) (R 8) [192,17,33,320,136] 13 :=
  permutation_upper _ _ _ [192,5,72,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15381

theorem m22189_160 : Upper (D 8) (R 8) [192,17,33,320,160] 13 :=
  permutation_upper _ _ _ [192,5,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15400

def r22189 : Route 9 := (fun mask => (mask,id))

def c22189 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22189 : Upper (D 8) (R 8) [192,17,33,320] 13 := by
  apply FastRouting.sound _ _ [192,17,33,320] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160] r22189 c22189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22189_6
  · exact m22189_10
  · exact m22189_12
  · exact m22189_34
  · exact m22189_36
  · exact m22189_40
  · exact m22189_130
  · exact m22189_132
  · exact m22189_136
  · exact m22189_160

theorem m22190_9 : Upper (D 8) (R 8) [192,17,34,68,9] 13 :=
  permutation_upper _ _ _ [192,5,9,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15060

theorem m22190_33 : Upper (D 8) (R 8) [192,17,34,68,33] 13 :=
  permutation_upper _ _ _ [192,5,33,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15150

theorem m22190_40 : Upper (D 8) (R 8) [192,17,34,68,40] 13 :=
  permutation_upper _ _ _ [192,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15256

theorem m22190_129 : Upper (D 8) (R 8) [192,17,34,68,129] 13 :=
  permutation_upper _ _ _ [192,5,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15302

theorem m22190_136 : Upper (D 8) (R 8) [192,17,34,68,136] 13 :=
  permutation_upper _ _ _ [192,5,72,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15359

theorem m22190_160 : Upper (D 8) (R 8) [192,17,34,68,160] 13 :=
  permutation_upper _ _ _ [192,5,96,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15401

theorem m22190_257 : Upper (D 8) (R 8) [192,17,34,68,257] 13 :=
  permutation_upper _ _ _ [192,5,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15438

theorem m22190_264 : Upper (D 8) (R 8) [192,17,34,68,264] 13 :=
  permutation_upper _ _ _ [192,5,264,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15481

theorem m22190_288 : Upper (D 8) (R 8) [192,17,34,68,288] 13 :=
  permutation_upper _ _ _ [192,5,288,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15504

theorem m22190_384 : Upper (D 8) (R 8) [192,17,34,68,384] 13 :=
  permutation_upper _ _ _ [192,5,320,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15528

def r22190 : Route 9 := (fun mask => (mask,id))

def c22190 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22190 : Upper (D 8) (R 8) [192,17,34,68] 13 := by
  apply FastRouting.sound _ _ [192,17,34,68] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r22190 c22190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22190_9
  · exact m22190_33
  · exact m22190_40
  · exact m22190_129
  · exact m22190_136
  · exact m22190_160
  · exact m22190_257
  · exact m22190_264
  · exact m22190_288
  · exact m22190_384

theorem m22191_5 : Upper (D 8) (R 8) [192,17,34,96,5] 13 :=
  permutation_upper _ _ _ [192,5,9,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15051

theorem m22191_9 : Upper (D 8) (R 8) [192,17,34,96,9] 13 :=
  permutation_upper _ _ _ [192,5,9,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15066

theorem m22191_12 : Upper (D 8) (R 8) [192,17,34,96,12] 13 :=
  permutation_upper _ _ _ [192,5,24,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15127

theorem m22191_33 : Upper (D 8) (R 8) [192,17,34,96,33] 13 :=
  permutation_upper _ _ _ [192,5,33,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15151

theorem m22191_36 : Upper (D 8) (R 8) [192,17,34,96,36] 13 :=
  permutation_upper _ _ _ [192,5,40,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15232

theorem m22191_40 : Upper (D 8) (R 8) [192,17,34,96,40] 13 :=
  permutation_upper _ _ _ [192,5,40,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15264

theorem m22191_129 : Upper (D 8) (R 8) [192,17,34,96,129] 13 :=
  permutation_upper _ _ _ [192,5,65,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15303

theorem m22191_132 : Upper (D 8) (R 8) [192,17,34,96,132] 13 :=
  permutation_upper _ _ _ [192,5,72,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15347

theorem m22191_136 : Upper (D 8) (R 8) [192,17,34,96,136] 13 :=
  permutation_upper _ _ _ [192,5,72,160,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15364

theorem m22191_160 : Upper (D 8) (R 8) [192,17,34,96,160] 13 :=
  permutation_upper _ _ _ [192,5,96,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15402

theorem m22191_257 : Upper (D 8) (R 8) [192,17,34,96,257] 13 :=
  permutation_upper _ _ _ [192,5,257,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15439

theorem m22191_260 : Upper (D 8) (R 8) [192,17,34,96,260] 13 :=
  permutation_upper _ _ _ [192,5,264,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15467

theorem m22191_264 : Upper (D 8) (R 8) [192,17,34,96,264] 13 :=
  permutation_upper _ _ _ [192,5,264,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15485

theorem m22191_288 : Upper (D 8) (R 8) [192,17,34,96,288] 13 :=
  permutation_upper _ _ _ [192,5,288,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15505

theorem m22191_384 : Upper (D 8) (R 8) [192,17,34,96,384] 13 :=
  permutation_upper _ _ _ [192,5,320,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15529

def r22191 : Route 9 := (fun mask => (mask,id))

def c22191 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22191 : Upper (D 8) (R 8) [192,17,34,96] 13 := by
  apply FastRouting.sound _ _ [192,17,34,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r22191 c22191
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22191_5
  · exact m22191_9
  · exact m22191_12
  · exact m22191_33
  · exact m22191_36
  · exact m22191_40
  · exact m22191_129
  · exact m22191_132
  · exact m22191_136
  · exact m22191_160
  · exact m22191_257
  · exact m22191_260
  · exact m22191_264
  · exact m22191_288
  · exact m22191_384

theorem m22192_12 : Upper (D 8) (R 8) [192,17,34,257,12] 13 :=
  permutation_upper _ _ _ [192,5,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15129

theorem m22192_36 : Upper (D 8) (R 8) [192,17,34,257,36] 13 :=
  permutation_upper _ _ _ [192,5,40,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15233

theorem m22192_40 : Upper (D 8) (R 8) [192,17,34,257,40] 13 :=
  permutation_upper _ _ _ [192,5,40,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15276

theorem m22192_68 : Upper (D 8) (R 8) [192,17,34,257,68] 13 :=
  permutation_upper _ _ _ [192,5,72,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15348

theorem m22192_72 : Upper (D 8) (R 8) [192,17,34,257,72] 13 :=
  permutation_upper _ _ _ [192,5,72,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15368

theorem m22192_96 : Upper (D 8) (R 8) [192,17,34,257,96] 13 :=
  permutation_upper _ _ _ [192,5,96,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15403

theorem m22192_192 : Upper (D 8) (R 8) [192,17,34,257,192] 13 :=
  permutation_upper _ _ _ [192,5,192,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15430

def r22192 : Route 9 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22192 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22192 : Upper (D 8) (R 8) [192,17,34,257] 13 := by
  apply FastRouting.sound _ _ [192,17,34,257] 13 (by decide) (choices 2) [12,36,40,68,72,96,192] r22192 c22192
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22192_12
  · exact m22192_36
  · exact m22192_40
  · exact m22192_68
  · exact m22192_72
  · exact m22192_96
  · exact m22192_192

theorem m22193_9 : Upper (D 8) (R 8) [192,17,34,260,9] 13 :=
  permutation_upper _ _ _ [192,5,9,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15073

theorem m22193_33 : Upper (D 8) (R 8) [192,17,34,260,33] 13 :=
  permutation_upper _ _ _ [192,5,33,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15152

theorem m22193_40 : Upper (D 8) (R 8) [192,17,34,260,40] 13 :=
  permutation_upper _ _ _ [192,5,40,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15284

theorem m22193_65 : Upper (D 8) (R 8) [192,17,34,260,65] 13 :=
  permutation_upper _ _ _ [192,5,65,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15304

theorem m22193_72 : Upper (D 8) (R 8) [192,17,34,260,72] 13 :=
  permutation_upper _ _ _ [192,5,72,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15374

theorem m22193_96 : Upper (D 8) (R 8) [192,17,34,260,96] 13 :=
  permutation_upper _ _ _ [192,5,96,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15404

theorem m22193_192 : Upper (D 8) (R 8) [192,17,34,260,192] 13 :=
  permutation_upper _ _ _ [192,5,192,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15431

def r22193 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22193 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22193 : Upper (D 8) (R 8) [192,17,34,260] 13 := by
  apply FastRouting.sound _ _ [192,17,34,260] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22193 c22193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22193_9
  · exact m22193_33
  · exact m22193_40
  · exact m22193_65
  · exact m22193_72
  · exact m22193_96
  · exact m22193_192

theorem m22194_5 : Upper (D 8) (R 8) [192,17,34,288,5] 13 :=
  permutation_upper _ _ _ [192,5,9,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15052

theorem m22194_9 : Upper (D 8) (R 8) [192,17,34,288,9] 13 :=
  permutation_upper _ _ _ [192,5,9,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15076

theorem m22194_12 : Upper (D 8) (R 8) [192,17,34,288,12] 13 :=
  permutation_upper _ _ _ [192,5,24,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15130

theorem m22194_33 : Upper (D 8) (R 8) [192,17,34,288,33] 13 :=
  permutation_upper _ _ _ [192,5,33,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15153

theorem m22194_36 : Upper (D 8) (R 8) [192,17,34,288,36] 13 :=
  permutation_upper _ _ _ [192,5,40,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15234

theorem m22194_40 : Upper (D 8) (R 8) [192,17,34,288,40] 13 :=
  permutation_upper _ _ _ [192,5,40,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15290

theorem m22194_65 : Upper (D 8) (R 8) [192,17,34,288,65] 13 :=
  permutation_upper _ _ _ [192,5,65,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15305

theorem m22194_68 : Upper (D 8) (R 8) [192,17,34,288,68] 13 :=
  permutation_upper _ _ _ [192,5,72,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15349

theorem m22194_72 : Upper (D 8) (R 8) [192,17,34,288,72] 13 :=
  permutation_upper _ _ _ [192,5,72,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15378

theorem m22194_96 : Upper (D 8) (R 8) [192,17,34,288,96] 13 :=
  permutation_upper _ _ _ [192,5,96,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15405

theorem m22194_192 : Upper (D 8) (R 8) [192,17,34,288,192] 13 :=
  permutation_upper _ _ _ [192,5,192,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15432

def r22194 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22194 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22194 : Upper (D 8) (R 8) [192,17,34,288] 13 := by
  apply FastRouting.sound _ _ [192,17,34,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,192] r22194 c22194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22194_5
  · exact m22194_9
  · exact m22194_12
  · exact m22194_33
  · exact m22194_36
  · exact m22194_40
  · exact m22194_65
  · exact m22194_68
  · exact m22194_72
  · exact m22194_96
  · exact m22194_192

theorem m22195_5 : Upper (D 8) (R 8) [192,17,34,320,5] 13 :=
  permutation_upper _ _ _ [192,5,9,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15053

theorem m22195_9 : Upper (D 8) (R 8) [192,17,34,320,9] 13 :=
  permutation_upper _ _ _ [192,5,9,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15079

theorem m22195_12 : Upper (D 8) (R 8) [192,17,34,320,12] 13 :=
  permutation_upper _ _ _ [192,5,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15131

theorem m22195_33 : Upper (D 8) (R 8) [192,17,34,320,33] 13 :=
  permutation_upper _ _ _ [192,5,33,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15154

theorem m22195_36 : Upper (D 8) (R 8) [192,17,34,320,36] 13 :=
  permutation_upper _ _ _ [192,5,40,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15235

theorem m22195_40 : Upper (D 8) (R 8) [192,17,34,320,40] 13 :=
  permutation_upper _ _ _ [192,5,40,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15294

theorem m22195_129 : Upper (D 8) (R 8) [192,17,34,320,129] 13 :=
  permutation_upper _ _ _ [192,5,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15306

theorem m22195_132 : Upper (D 8) (R 8) [192,17,34,320,132] 13 :=
  permutation_upper _ _ _ [192,5,72,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15350

theorem m22195_136 : Upper (D 8) (R 8) [192,17,34,320,136] 13 :=
  permutation_upper _ _ _ [192,5,72,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15382

theorem m22195_160 : Upper (D 8) (R 8) [192,17,34,320,160] 13 :=
  permutation_upper _ _ _ [192,5,96,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15406

def r22195 : Route 9 := (fun mask => (mask,id))

def c22195 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22195 : Upper (D 8) (R 8) [192,17,34,320] 13 := by
  apply FastRouting.sound _ _ [192,17,34,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22195 c22195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22195_5
  · exact m22195_9
  · exact m22195_12
  · exact m22195_33
  · exact m22195_36
  · exact m22195_40
  · exact m22195_129
  · exact m22195_132
  · exact m22195_136
  · exact m22195_160

theorem m22196_5 : Upper (D 8) (R 8) [192,17,40,66,5] 13 :=
  permutation_upper _ _ _ [192,5,9,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15054

theorem m22196_33 : Upper (D 8) (R 8) [192,17,40,66,33] 13 :=
  permutation_upper _ _ _ [192,5,33,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15155

theorem m22196_36 : Upper (D 8) (R 8) [192,17,40,66,36] 13 :=
  permutation_upper _ _ _ [192,5,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15238

theorem m22196_129 : Upper (D 8) (R 8) [192,17,40,66,129] 13 :=
  permutation_upper _ _ _ [192,5,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15307

theorem m22196_132 : Upper (D 8) (R 8) [192,17,40,66,132] 13 :=
  permutation_upper _ _ _ [192,5,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15351

theorem m22196_160 : Upper (D 8) (R 8) [192,17,40,66,160] 13 :=
  permutation_upper _ _ _ [192,5,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15407

theorem m22196_257 : Upper (D 8) (R 8) [192,17,40,66,257] 13 :=
  permutation_upper _ _ _ [192,5,257,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15440

theorem m22196_260 : Upper (D 8) (R 8) [192,17,40,66,260] 13 :=
  permutation_upper _ _ _ [192,5,264,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15472

theorem m22196_288 : Upper (D 8) (R 8) [192,17,40,66,288] 13 :=
  permutation_upper _ _ _ [192,5,288,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15509

theorem m22196_384 : Upper (D 8) (R 8) [192,17,40,66,384] 13 :=
  permutation_upper _ _ _ [192,5,320,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15530

def r22196 : Route 9 := (fun mask => (mask,id))

def c22196 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22196 : Upper (D 8) (R 8) [192,17,40,66] 13 := by
  apply FastRouting.sound _ _ [192,17,40,66] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r22196 c22196
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22196_5
  · exact m22196_33
  · exact m22196_36
  · exact m22196_129
  · exact m22196_132
  · exact m22196_160
  · exact m22196_257
  · exact m22196_260
  · exact m22196_288
  · exact m22196_384

theorem m22197_6 : Upper (D 8) (R 8) [192,17,40,257,6] 13 :=
  permutation_upper _ _ _ [192,5,10,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15092

theorem m22197_34 : Upper (D 8) (R 8) [192,17,40,257,34] 13 :=
  permutation_upper _ _ _ [192,5,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15190

theorem m22197_36 : Upper (D 8) (R 8) [192,17,40,257,36] 13 :=
  permutation_upper _ _ _ [192,5,40,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15240

theorem m22197_66 : Upper (D 8) (R 8) [192,17,40,257,66] 13 :=
  permutation_upper _ _ _ [192,5,66,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15325

theorem m22197_68 : Upper (D 8) (R 8) [192,17,40,257,68] 13 :=
  permutation_upper _ _ _ [192,5,72,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15352

theorem m22197_96 : Upper (D 8) (R 8) [192,17,40,257,96] 13 :=
  permutation_upper _ _ _ [192,5,96,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15408

theorem m22197_192 : Upper (D 8) (R 8) [192,17,40,257,192] 13 :=
  permutation_upper _ _ _ [192,5,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15433

def r22197 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22197 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22197 : Upper (D 8) (R 8) [192,17,40,257] 13 := by
  apply FastRouting.sound _ _ [192,17,40,257] 13 (by decide) (choices 2) [6,34,36,66,68,96,192] r22197 c22197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22197_6
  · exact m22197_34
  · exact m22197_36
  · exact m22197_66
  · exact m22197_68
  · exact m22197_96
  · exact m22197_192

theorem m22198_5 : Upper (D 8) (R 8) [192,17,40,258,5] 13 :=
  permutation_upper _ _ _ [192,5,9,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15055

theorem m22198_33 : Upper (D 8) (R 8) [192,17,40,258,33] 13 :=
  permutation_upper _ _ _ [192,5,33,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15156

theorem m22198_36 : Upper (D 8) (R 8) [192,17,40,258,36] 13 :=
  permutation_upper _ _ _ [192,5,40,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15241

theorem m22198_65 : Upper (D 8) (R 8) [192,17,40,258,65] 13 :=
  permutation_upper _ _ _ [192,5,65,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15308

theorem m22198_68 : Upper (D 8) (R 8) [192,17,40,258,68] 13 :=
  permutation_upper _ _ _ [192,5,72,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15353

theorem m22198_96 : Upper (D 8) (R 8) [192,17,40,258,96] 13 :=
  permutation_upper _ _ _ [192,5,96,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15409

theorem m22198_192 : Upper (D 8) (R 8) [192,17,40,258,192] 13 :=
  permutation_upper _ _ _ [192,5,192,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15434

def r22198 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22198 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22198 : Upper (D 8) (R 8) [192,17,40,258] 13 := by
  apply FastRouting.sound _ _ [192,17,40,258] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r22198 c22198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22198_5
  · exact m22198_33
  · exact m22198_36
  · exact m22198_65
  · exact m22198_68
  · exact m22198_96
  · exact m22198_192

theorem m22199_3 : Upper (D 8) (R 8) [192,17,40,260,3] 13 :=
  permutation_upper _ _ _ [192,5,3,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15039

theorem m22199_33 : Upper (D 8) (R 8) [192,17,40,260,33] 13 :=
  permutation_upper _ _ _ [192,5,33,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15157

theorem m22199_34 : Upper (D 8) (R 8) [192,17,40,260,34] 13 :=
  permutation_upper _ _ _ [192,5,34,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15191

theorem m22199_65 : Upper (D 8) (R 8) [192,17,40,260,65] 13 :=
  permutation_upper _ _ _ [192,5,65,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15309

theorem m22199_66 : Upper (D 8) (R 8) [192,17,40,260,66] 13 :=
  permutation_upper _ _ _ [192,5,66,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15326

theorem m22199_96 : Upper (D 8) (R 8) [192,17,40,260,96] 13 :=
  permutation_upper _ _ _ [192,5,96,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15410

theorem m22199_192 : Upper (D 8) (R 8) [192,17,40,260,192] 13 :=
  permutation_upper _ _ _ [192,5,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15435

def r22199 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22199 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22199 : Upper (D 8) (R 8) [192,17,40,260] 13 := by
  apply FastRouting.sound _ _ [192,17,40,260] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22199 c22199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22199_3
  · exact m22199_33
  · exact m22199_34
  · exact m22199_65
  · exact m22199_66
  · exact m22199_96
  · exact m22199_192

#print axioms u22199
end Delivery.IrregularNine14.P08
