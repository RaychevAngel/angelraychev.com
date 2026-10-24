import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0088
import IrregularNine14P08C0089

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15180 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 88 432 496 432 432), lower := (rows 193 7 38 41 88 32 64 128 256), losses := [] }

theorem u15180 : Upper (D 8) (R 8) [192,5,34,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15181 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 112 440 472 408 408), lower := (rows 193 7 38 41 112 32 64 128 256), losses := [] }

theorem u15181 : Upper (D 8) (R 8) [192,5,34,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15182 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 280 240 240 240 496), lower := (rows 193 7 38 41 280 32 64 128 256), losses := [] }

theorem u15182 : Upper (D 8) (R 8) [192,5,34,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15183 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 304 248 216 216 472), lower := (rows 193 7 38 41 304 32 64 128 256), losses := [] }

theorem u15183 : Upper (D 8) (R 8) [192,5,34,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15184 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 336 184 248 184 440), lower := (rows 193 7 38 41 336 32 64 128 256), losses := [] }

theorem u15184 : Upper (D 8) (R 8) [192,5,34,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15185 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 56 56 481 449 449 449), lower := (rows 193 7 38 56 56 32 64 128 256), losses := [] }

theorem u15185 : Upper (D 8) (R 8) [192,5,34,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15186 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 56 81 424 488 424 424), lower := (rows 193 7 38 56 81 32 64 128 256), losses := [] }

theorem u15186 : Upper (D 8) (R 8) [192,5,34,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15187 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 294, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 56 88 417 481 417 417), lower := (rows 193 7 38 56 88 32 64 128 256), losses := [] }

theorem u15187 : Upper (D 8) (R 8) [192,5,34,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15188 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 56 112 425 457 393 393), lower := (rows 193 7 38 56 112 32 64 128 256), losses := [] }

theorem u15188 : Upper (D 8) (R 8) [192,5,34,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15189 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 38 56 208 297 361 425 297), lower := (rows 193 7 38 56 208 32 64 128 256), losses := [] }

theorem u15189 : Upper (D 8) (R 8) [192,5,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15190 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 56 273 232 232 232 488), lower := (rows 193 7 38 56 273 32 64 128 256), losses := [] }

theorem u15190 : Upper (D 8) (R 8) [192,5,34,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15191 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15191 : Upper (D 8) (R 8) [192,5,34,48,264] 13 := by
  apply FastRouting.sound _ _ [192,5,34,48,264] 13 (by decide) (choices 1) [1,64] r15191 c15191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5337
  · exact u5338

def b15192 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 56 304 233 201 201 457), lower := (rows 193 7 38 56 304 32 64 128 256), losses := [] }

theorem u15192 : Upper (D 8) (R 8) [192,5,34,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15193 : Route 9 := (fun mask => (mask,id))

def c15193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15193 : Upper (D 8) (R 8) [192,5,34,48,320] 13 := by
  apply FastRouting.sound _ _ [192,5,34,48,320] 13 (by decide) (choices 1) [1,8,128] r15193 c15193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5339
  · exact u5340
  · exact u5341

def b15194 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 73 152 304 368 432 304), lower := (rows 193 7 38 73 152 32 64 128 256), losses := [] }

theorem u15194 : Upper (D 8) (R 8) [192,5,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15195 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 73 176 312 376 440 312), lower := (rows 193 7 38 73 176 32 64 128 256), losses := [] }

theorem u15195 : Upper (D 8) (R 8) [192,5,34,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15196 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 73 280 176 240 176 432), lower := (rows 193 7 38 73 280 32 64 128 256), losses := [] }

theorem u15196 : Upper (D 8) (R 8) [192,5,34,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15197 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 73 304 184 248 184 440), lower := (rows 193 7 38 73 304 32 64 128 256), losses := [] }

theorem u15197 : Upper (D 8) (R 8) [192,5,34,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15198 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 73 400 56 120 184 312), lower := (rows 193 7 38 73 400 32 64 128 256), losses := [] }

theorem u15198 : Upper (D 8) (R 8) [192,5,34,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15199 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 88 152 289 353 417 289), lower := (rows 193 7 38 88 152 32 64 128 256), losses := [] }

theorem u15199 : Upper (D 8) (R 8) [192,5,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15200 : Route 9 := (fun mask => (mask,id))

def c15200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15200 : Upper (D 8) (R 8) [192,5,34,80,160] 13 := by
  apply FastRouting.sound _ _ [192,5,34,80,160] 13 (by decide) (choices 1) [1,8,256] r15200 c15200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5342
  · exact u5343
  · exact u5344

def b15201 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 88 273 168 232 168 424), lower := (rows 193 7 38 88 273 32 64 128 256), losses := [] }

theorem u15201 : Upper (D 8) (R 8) [192,5,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15202 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 88 280 161 225 161 417), lower := (rows 193 7 38 88 280 32 64 128 256), losses := [] }

theorem u15202 : Upper (D 8) (R 8) [192,5,34,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15203 : Route 9 := (fun mask => (mask,id))

def c15203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15203 : Upper (D 8) (R 8) [192,5,34,80,288] 13 := by
  apply FastRouting.sound _ _ [192,5,34,80,288] 13 (by decide) (choices 1) [1,8,128] r15203 c15203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5345
  · exact u5346
  · exact u5347

def r15204 : Route 9 := (fun mask => (mask,id))

def c15204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15204 : Upper (D 8) (R 8) [192,5,34,80,384] 13 := by
  apply FastRouting.sound _ _ [192,5,34,80,384] 13 (by decide) (choices 1) [1,8] r15204 c15204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5348
  · exact u5349

theorem m15205_16 : Upper (D 8) (R 8) [192,5,34,96,160,16] 13 :=
  permutation_upper _ _ _ [192,5,34,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5351

def r15205 : Route 9 := (fun mask => (mask,id))

def c15205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15205 : Upper (D 8) (R 8) [192,5,34,96,160] 13 := by
  apply FastRouting.sound _ _ [192,5,34,96,160] 13 (by decide) (choices 1) [1,8,16,256] r15205 c15205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5350
  · exact u5351
  · exact m15205_16
  · exact u5352

def b15206 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 104 273 184 248 184 440), lower := (rows 193 7 38 104 273 32 64 128 256), losses := [] }

theorem u15206 : Upper (D 8) (R 8) [192,5,34,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15207 : Route 9 := (fun mask => (mask,id))

def c15207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15207 : Upper (D 8) (R 8) [192,5,34,96,264] 13 := by
  apply FastRouting.sound _ _ [192,5,34,96,264] 13 (by decide) (choices 1) [1,16,128] r15207 c15207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5353
  · exact u5354
  · exact u5355

def r15208 : Route 9 := (fun mask => (mask,id))

def c15208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15208 : Upper (D 8) (R 8) [192,5,34,96,288] 13 := by
  apply FastRouting.sound _ _ [192,5,34,96,288] 13 (by decide) (choices 1) [1,8,16,128] r15208 c15208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5356
  · exact u5357
  · exact u5358
  · exact u5359

def r15209 : Route 9 := (fun mask => (mask,id))

def c15209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15209 : Upper (D 8) (R 8) [192,5,34,96,384] 13 := by
  apply FastRouting.sound _ _ [192,5,34,96,384] 13 (by decide) (choices 1) [1,8,16] r15209 c15209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5360
  · exact u5361
  · exact u5362

def b15210 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 200 280 49 113 177 305), lower := (rows 193 7 38 200 280 32 64 128 256), losses := [] }

theorem u15210 : Upper (D 8) (R 8) [192,5,34,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15211 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 200 304 57 121 185 313), lower := (rows 193 7 38 200 304 32 64 128 256), losses := [] }

theorem u15211 : Upper (D 8) (R 8) [192,5,34,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15212 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 25 50 480 480 480 480), lower := (rows 193 7 44 25 50 32 64 128 256), losses := [] }

theorem u15212 : Upper (D 8) (R 8) [192,5,40,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15213 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 25 82 416 480 416 416), lower := (rows 193 7 44 25 82 32 64 128 256), losses := [] }

theorem u15213 : Upper (D 8) (R 8) [192,5,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15214 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 25 112 418 482 418 418), lower := (rows 193 7 44 25 112 32 64 128 256), losses := [] }

theorem u15214 : Upper (D 8) (R 8) [192,5,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15215 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 25 274 224 224 224 480), lower := (rows 193 7 44 25 274 32 64 128 256), losses := [] }

theorem u15215 : Upper (D 8) (R 8) [192,5,40,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15216 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 25 304 226 226 226 482), lower := (rows 193 7 44 25 304 32 64 128 256), losses := [] }

theorem u15216 : Upper (D 8) (R 8) [192,5,40,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15217 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 25 336 162 226 162 418), lower := (rows 193 7 44 25 336 32 64 128 256), losses := [] }

theorem u15217 : Upper (D 8) (R 8) [192,5,40,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15218 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 26 49 480 480 480 480), lower := (rows 193 7 44 26 49 32 64 128 256), losses := [] }

theorem u15218 : Upper (D 8) (R 8) [192,5,40,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15219 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 26 81 416 480 416 416), lower := (rows 193 7 44 26 81 32 64 128 256), losses := [] }

theorem u15219 : Upper (D 8) (R 8) [192,5,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15220 : PairBound 9 := { available := 417, camps := [], pairs := [(2,6)], upper := (rows 193 7 44 26 112 417 481 417 417), lower := (rows 193 7 44 26 112 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 44 446 48 32 0 128 256) }] }

theorem u15220 : Upper (D 8) (R 8) [192,5,40,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15221 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 26 208 289 353 417 289), lower := (rows 193 7 44 26 208 32 64 128 256), losses := [] }

theorem u15221 : Upper (D 8) (R 8) [192,5,40,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15222 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 26 273 224 224 224 480), lower := (rows 193 7 44 26 273 32 64 128 256), losses := [] }

theorem u15222 : Upper (D 8) (R 8) [192,5,40,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15223 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15223 : Upper (D 8) (R 8) [192,5,40,18,288] 13 := by
  apply FastRouting.sound _ _ [192,5,40,18,288] 13 (by decide) (choices 1) [1,64] r15223 c15223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5363
  · exact u5364

def b15224 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 193 7 44 26 336 161 225 161 417), lower := (rows 193 7 44 26 336 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 44 446 272 32 0 128 256) }] }

theorem u15224 : Upper (D 8) (R 8) [192,5,40,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15225 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 50 496 464 464 464), lower := (rows 193 7 44 41 50 32 64 128 256), losses := [] }

theorem u15225 : Upper (D 8) (R 8) [192,5,40,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15226 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 82 432 496 432 432), lower := (rows 193 7 44 41 82 32 64 128 256), losses := [] }

theorem u15226 : Upper (D 8) (R 8) [192,5,40,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15227 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 112 434 466 402 402), lower := (rows 193 7 44 41 112 32 64 128 256), losses := [] }

theorem u15227 : Upper (D 8) (R 8) [192,5,40,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15228 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 274 240 240 240 496), lower := (rows 193 7 44 41 274 32 64 128 256), losses := [] }

theorem u15228 : Upper (D 8) (R 8) [192,5,40,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15229 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 304 242 210 210 466), lower := (rows 193 7 44 41 304 32 64 128 256), losses := [] }

theorem u15229 : Upper (D 8) (R 8) [192,5,40,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15230 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 336 178 242 178 434), lower := (rows 193 7 44 41 336 32 64 128 256), losses := [] }

theorem u15230 : Upper (D 8) (R 8) [192,5,40,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15231 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 42 49 496 464 464 464), lower := (rows 193 7 44 42 49 32 64 128 256), losses := [] }

theorem u15231 : Upper (D 8) (R 8) [192,5,40,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15232 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 42 112 433 465 401 401), lower := (rows 193 7 44 42 112 32 64 128 256), losses := [] }

theorem u15232 : Upper (D 8) (R 8) [192,5,40,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15233 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 42 273 240 240 240 496), lower := (rows 193 7 44 42 273 32 64 128 256), losses := [] }

theorem u15233 : Upper (D 8) (R 8) [192,5,40,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15234 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 42 304 241 209 209 465), lower := (rows 193 7 44 42 304 32 64 128 256), losses := [] }

theorem u15234 : Upper (D 8) (R 8) [192,5,40,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15235 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 42 336 177 241 177 433), lower := (rows 193 7 44 42 336 32 64 128 256), losses := [] }

theorem u15235 : Upper (D 8) (R 8) [192,5,40,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15236 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 56 49 482 450 450 450), lower := (rows 193 7 44 56 49 32 64 128 256), losses := [] }

theorem u15236 : Upper (D 8) (R 8) [192,5,40,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15237 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 50 481 449 449 449), lower := (rows 193 7 44 56 50 32 64 128 256), losses := [] }

theorem u15237 : Upper (D 8) (R 8) [192,5,40,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15238 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 82 417 481 417 417), lower := (rows 193 7 44 56 82 32 64 128 256), losses := [] }

theorem u15238 : Upper (D 8) (R 8) [192,5,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15239 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 112 419 451 387 387), lower := (rows 193 7 44 56 112 32 64 128 256), losses := [] }

theorem u15239 : Upper (D 8) (R 8) [192,5,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15239
end Delivery.IrregularNine14.P08
