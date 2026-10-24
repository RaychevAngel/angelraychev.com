import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0012
import IrregularNine14P01C0013

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3180 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 140 328 48 178 210 146 402), lower := (rows 53 67 140 328 48 32 64 128 256), losses := [] }

theorem u3180 : Upper (D 1) (R 1) [52,65,136,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 140 328 144 50 114 178 306), lower := (rows 53 67 140 328 144 32 64 128 256), losses := [] }

theorem u3181 : Upper (D 1) (R 1) [52,65,136,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 67 262 88 18 168 232 168 424), lower := (rows 53 67 262 88 18 32 64 128 256), losses := [] }

theorem u3182 : Upper (D 1) (R 1) [52,65,258,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 67 262 88 24 162 226 162 418), lower := (rows 53 67 262 88 24 32 64 128 256), losses := [] }

theorem u3183 : Upper (D 1) (R 1) [52,65,258,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 88 48 170 202 138 394), lower := (rows 53 67 262 88 48 32 64 128 256), losses := [] }

theorem u3184 : Upper (D 1) (R 1) [52,65,258,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3185 : Route 9 := (fun mask => (mask,id))

def c3185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3185 : Upper (D 1) (R 1) [52,65,258,80,128] 13 := by
  apply FastRouting.sound _ _ [52,65,258,80,128] 13 (by decide) (choices 1) [2,8,128] r3185 c3185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u736
  · exact u737
  · exact u738

def b3186 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 67 262 138 24 240 240 240 496), lower := (rows 53 67 262 138 24 32 64 128 256), losses := [] }

theorem u3186 : Upper (D 1) (R 1) [52,65,258,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3187 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 138 48 248 216 216 472), lower := (rows 53 67 262 138 48 32 64 128 256), losses := [] }

theorem u3187 : Upper (D 1) (R 1) [52,65,258,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3187
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3188_8 : Upper (D 1) (R 1) [52,65,258,130,64,8] 13 :=
  permutation_upper _ _ _ [52,65,258,130,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u739

theorem m3188_16 : Upper (D 1) (R 1) [52,65,258,130,64,16] 13 :=
  permutation_upper _ _ _ [52,65,258,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u741

def r3188 : Route 9 := (fun mask => (mask,id))

def c3188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3188 : Upper (D 1) (R 1) [52,65,258,130,64] 13 := by
  apply FastRouting.sound _ _ [52,65,258,130,64] 13 (by decide) (choices 1) [8,16,128] r3188 c3188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3188_8
  · exact m3188_16
  · exact u743

theorem m3189_8 : Upper (D 1) (R 1) [52,65,258,130,128,8] 13 :=
  permutation_upper _ _ _ [52,65,258,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u740

theorem m3189_16 : Upper (D 1) (R 1) [52,65,258,130,128,16] 13 :=
  permutation_upper _ _ _ [52,65,258,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u742

theorem m3189_64 : Upper (D 1) (R 1) [52,65,258,130,128,64] 13 :=
  permutation_upper _ _ _ [52,65,258,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u743

def r3189 : Route 9 := (fun mask => (mask,id))

def c3189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3189 : Upper (D 1) (R 1) [52,65,258,130,128] 13 := by
  apply FastRouting.sound _ _ [52,65,258,130,128] 13 (by decide) (choices 1) [8,16,64] r3189 c3189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3189_8
  · exact m3189_16
  · exact m3189_64

def b3190 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 152 18 232 232 232 488), lower := (rows 53 67 262 152 18 32 64 128 256), losses := [] }

theorem u3190 : Upper (D 1) (R 1) [52,65,258,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3191 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 67 262 152 24 226 226 226 482), lower := (rows 53 67 262 152 24 32 64 128 256), losses := [] }

theorem u3191 : Upper (D 1) (R 1) [52,65,258,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3192 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 152 48 234 202 202 458), lower := (rows 53 67 262 152 48 32 64 128 256), losses := [] }

theorem u3192 : Upper (D 1) (R 1) [52,65,258,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3193 : Route 9 := (fun mask => (mask,id))

def c3193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3193 : Upper (D 1) (R 1) [52,65,258,144,64] 13 := by
  apply FastRouting.sound _ _ [52,65,258,144,64] 13 (by decide) (choices 1) [2,8,128] r3193 c3193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u744
  · exact u745
  · exact u746

def b3194 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 53 67 262 152 144 106 106 234 362), lower := (rows 53 67 262 152 144 32 64 128 256), losses := [] }

theorem u3194 : Upper (D 1) (R 1) [52,65,258,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3194
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3195 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 200 18 184 248 184 440), lower := (rows 53 67 262 200 18 32 64 128 256), losses := [] }

theorem u3195 : Upper (D 1) (R 1) [52,65,258,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3196 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 67 262 200 24 178 242 178 434), lower := (rows 53 67 262 200 24 32 64 128 256), losses := [] }

theorem u3196 : Upper (D 1) (R 1) [52,65,258,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3197 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 200 48 186 218 154 410), lower := (rows 53 67 262 200 48 32 64 128 256), losses := [] }

theorem u3197 : Upper (D 1) (R 1) [52,65,258,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3197
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3198_2 : Upper (D 1) (R 1) [52,65,258,192,128,2] 13 :=
  permutation_upper _ _ _ [52,65,258,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u747

theorem m3198_8 : Upper (D 1) (R 1) [52,65,258,192,128,8] 13 :=
  permutation_upper _ _ _ [52,65,258,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u748

theorem m3198_16 : Upper (D 1) (R 1) [52,65,258,192,128,16] 13 :=
  permutation_upper _ _ _ [52,65,258,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u749

def r3198 : Route 9 := (fun mask => (mask,id))

def c3198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3198 : Upper (D 1) (R 1) [52,65,258,192,128] 13 := by
  apply FastRouting.sound _ _ [52,65,258,192,128] 13 (by decide) (choices 1) [2,8,16] r3198 c3198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3198_2
  · exact m3198_8
  · exact m3198_16

def r3199 : Route 9 := (fun mask => (mask,id))

def c3199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3199 : Upper (D 1) (R 1) [52,65,264,130,2] 13 := by
  apply FastRouting.sound _ _ [52,65,264,130,2] 13 (by decide) (choices 1) [16,64,128] r3199 c3199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u750
  · exact u751
  · exact u752

def b3200 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 268 138 48 242 210 210 466), lower := (rows 53 67 268 138 48 32 64 128 256), losses := [] }

theorem u3200 : Upper (D 1) (R 1) [52,65,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3200
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3201_2 : Upper (D 1) (R 1) [52,65,264,130,64,2] 13 :=
  permutation_upper _ _ _ [52,65,264,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u751

theorem m3201_16 : Upper (D 1) (R 1) [52,65,264,130,64,16] 13 :=
  permutation_upper _ _ _ [52,65,264,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u753

def r3201 : Route 9 := (fun mask => (mask,id))

def c3201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3201 : Upper (D 1) (R 1) [52,65,264,130,64] 13 := by
  apply FastRouting.sound _ _ [52,65,264,130,64] 13 (by decide) (choices 1) [2,16,128] r3201 c3201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3201_2
  · exact m3201_16
  · exact u754

def b3202 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 268 138 144 114 114 242 370), lower := (rows 53 67 268 138 144 32 64 128 256), losses := [] }

theorem u3202 : Upper (D 1) (R 1) [52,65,264,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3203 : Route 9 := (fun mask => (mask,id))

def c3203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3203 : Upper (D 1) (R 1) [52,65,264,192,2] 13 := by
  apply FastRouting.sound _ _ [52,65,264,192,2] 13 (by decide) (choices 1) [2,16,128] r3203 c3203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u755
  · exact u756
  · exact u757

def b3204 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 268 200 48 178 210 146 402), lower := (rows 53 67 268 200 48 32 64 128 256), losses := [] }

theorem u3204 : Upper (D 1) (R 1) [52,65,264,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 268 200 144 50 114 178 306), lower := (rows 53 67 268 200 144 32 64 128 256), losses := [] }

theorem u3205 : Upper (D 1) (R 1) [52,65,264,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 67 388 88 18 170 234 170 426), lower := (rows 53 67 388 88 18 32 64 128 256), losses := [] }

theorem u3206 : Upper (D 1) (R 1) [52,65,384,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 67 388 88 24 162 226 162 418), lower := (rows 53 67 388 88 24 32 64 128 256), losses := [] }

theorem u3207 : Upper (D 1) (R 1) [52,65,384,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3208 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 388 88 48 170 202 138 394), lower := (rows 53 67 388 88 48 32 64 128 256), losses := [] }

theorem u3208 : Upper (D 1) (R 1) [52,65,384,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3209 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 388 88 144 42 106 170 298), lower := (rows 53 67 388 88 144 32 64 128 256), losses := [] }

theorem u3209 : Upper (D 1) (R 1) [52,65,384,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3209
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3210 : Route 9 := (fun mask => (mask,id))

def c3210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3210 : Upper (D 1) (R 1) [52,65,384,130,2] 13 := by
  apply FastRouting.sound _ _ [52,65,384,130,2] 13 (by decide) (choices 1) [8,16,64] r3210 c3210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u758
  · exact u759
  · exact u760

def b3211 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 53 67 388 138 24 114 114 242 370), lower := (rows 53 67 388 138 24 32 64 128 256), losses := [] }

theorem u3211 : Upper (D 1) (R 1) [52,65,384,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3212 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 388 138 48 122 90 218 346), lower := (rows 53 67 388 138 48 32 64 128 256), losses := [] }

theorem u3212 : Upper (D 1) (R 1) [52,65,384,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3212
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3213_2 : Upper (D 1) (R 1) [52,65,384,130,64,2] 13 :=
  permutation_upper _ _ _ [52,65,384,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u760

theorem m3213_8 : Upper (D 1) (R 1) [52,65,384,130,64,8] 13 :=
  permutation_upper _ _ _ [52,65,384,130,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u761

theorem m3213_16 : Upper (D 1) (R 1) [52,65,384,130,64,16] 13 :=
  permutation_upper _ _ _ [52,65,384,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u762

def r3213 : Route 9 := (fun mask => (mask,id))

def c3213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3213 : Upper (D 1) (R 1) [52,65,384,130,64] 13 := by
  apply FastRouting.sound _ _ [52,65,384,130,64] 13 (by decide) (choices 1) [2,8,16] r3213 c3213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3213_2
  · exact m3213_8
  · exact m3213_16

def r3214 : Route 9 := (fun mask => (mask,id))

def c3214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3214 : Upper (D 1) (R 1) [52,65,384,144,2] 13 := by
  apply FastRouting.sound _ _ [52,65,384,144,2] 13 (by decide) (choices 1) [2,8,64] r3214 c3214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u763
  · exact u764
  · exact u765

def b3215 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 53 67 388 152 24 98 98 226 354), lower := (rows 53 67 388 152 24 32 64 128 256), losses := [] }

theorem u3215 : Upper (D 1) (R 1) [52,65,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3216 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 388 152 48 106 74 202 330), lower := (rows 53 67 388 152 48 32 64 128 256), losses := [] }

theorem u3216 : Upper (D 1) (R 1) [52,65,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3217 : Route 9 := (fun mask => (mask,id))

def c3217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3217 : Upper (D 1) (R 1) [52,65,384,144,64] 13 := by
  apply FastRouting.sound _ _ [52,65,384,144,64] 13 (by decide) (choices 1) [2,8] r3217 c3217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u766
  · exact u767

def r3218 : Route 9 := (fun mask => (mask,id))

def c3218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3218 : Upper (D 1) (R 1) [52,65,384,192,2] 13 := by
  apply FastRouting.sound _ _ [52,65,384,192,2] 13 (by decide) (choices 1) [2,8,16] r3218 c3218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u768
  · exact u769
  · exact u770

def b3219 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 67 388 200 24 50 114 178 306), lower := (rows 53 67 388 200 24 32 64 128 256), losses := [] }

theorem u3219 : Upper (D 1) (R 1) [52,65,384,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3219
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3220 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 388 200 48 58 90 154 282), lower := (rows 53 67 388 200 48 32 64 128 256), losses := [] }

theorem u3220 : Upper (D 1) (R 1) [52,65,384,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3221 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 7 392 18 240 240 240 496), lower := (rows 53 74 7 392 18 32 64 128 256), losses := [] }

theorem u3221 : Upper (D 1) (R 1) [52,72,3,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3222 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 7 392 48 242 210 210 466), lower := (rows 53 74 7 392 48 32 64 128 256), losses := [] }

theorem u3222 : Upper (D 1) (R 1) [52,72,3,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3222
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3223_2 : Upper (D 1) (R 1) [52,72,3,384,64,2] 13 :=
  permutation_upper _ _ _ [52,72,3,384,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u771

theorem m3223_16 : Upper (D 1) (R 1) [52,72,3,384,64,16] 13 :=
  permutation_upper _ _ _ [52,72,3,384,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u773

def r3223 : Route 9 := (fun mask => (mask,id))

def c3223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3223 : Upper (D 1) (R 1) [52,72,3,384,64] 13 := by
  apply FastRouting.sound _ _ [52,72,3,384,64] 13 (by decide) (choices 1) [2,16,128] r3223 c3223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3223_2
  · exact m3223_16
  · exact u775

theorem m3224_2 : Upper (D 1) (R 1) [52,72,3,384,128,2] 13 :=
  permutation_upper _ _ _ [52,72,3,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u772

theorem m3224_16 : Upper (D 1) (R 1) [52,72,3,384,128,16] 13 :=
  permutation_upper _ _ _ [52,72,3,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u774

theorem m3224_64 : Upper (D 1) (R 1) [52,72,3,384,128,64] 13 :=
  permutation_upper _ _ _ [52,72,3,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u775

def r3224 : Route 9 := (fun mask => (mask,id))

def c3224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3224 : Upper (D 1) (R 1) [52,72,3,384,128] 13 := by
  apply FastRouting.sound _ _ [52,72,3,384,128] 13 (by decide) (choices 1) [2,16,64] r3224 c3224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3224_2
  · exact m3224_16
  · exact m3224_64

def b3225 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 133 266 18 240 240 240 496), lower := (rows 53 74 133 266 18 32 64 128 256), losses := [] }

theorem u3225 : Upper (D 1) (R 1) [52,72,129,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3225
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3226 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 133 266 48 242 210 210 466), lower := (rows 53 74 133 266 48 32 64 128 256), losses := [] }

theorem u3226 : Upper (D 1) (R 1) [52,72,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3226
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3227_2 : Upper (D 1) (R 1) [52,72,129,258,64,2] 13 :=
  permutation_upper _ _ _ [52,72,129,258,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u776

theorem m3227_16 : Upper (D 1) (R 1) [52,72,129,258,64,16] 13 :=
  permutation_upper _ _ _ [52,72,129,258,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u777

def r3227 : Route 9 := (fun mask => (mask,id))

def c3227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3227 : Upper (D 1) (R 1) [52,72,129,258,64] 13 := by
  apply FastRouting.sound _ _ [52,72,129,258,64] 13 (by decide) (choices 1) [2,16,128] r3227 c3227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3227_2
  · exact m3227_16
  · exact u778

def b3228 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 133 266 144 114 114 242 370), lower := (rows 53 74 133 266 144 32 64 128 256), losses := [] }

theorem u3228 : Upper (D 1) (R 1) [52,72,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3228
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 134 265 18 240 240 240 496), lower := (rows 53 74 134 265 18 32 64 128 256), losses := [] }

theorem u3229 : Upper (D 1) (R 1) [52,72,130,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 134 265 48 242 210 210 466), lower := (rows 53 74 134 265 48 32 64 128 256), losses := [] }

theorem u3230 : Upper (D 1) (R 1) [52,72,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3230
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3231_2 : Upper (D 1) (R 1) [52,72,130,257,64,2] 13 :=
  permutation_upper _ _ _ [52,72,130,257,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u779

theorem m3231_16 : Upper (D 1) (R 1) [52,72,130,257,64,16] 13 :=
  permutation_upper _ _ _ [52,72,130,257,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u780

def r3231 : Route 9 := (fun mask => (mask,id))

def c3231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3231 : Upper (D 1) (R 1) [52,72,130,257,64] 13 := by
  apply FastRouting.sound _ _ [52,72,130,257,64] 13 (by decide) (choices 1) [2,16,128] r3231 c3231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3231_2
  · exact m3231_16
  · exact u781

def b3232 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 134 265 144 114 114 242 370), lower := (rows 53 74 134 265 144 32 64 128 256), losses := [] }

theorem u3232 : Upper (D 1) (R 1) [52,72,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 74 134 280 17 226 226 226 482), lower := (rows 53 74 134 280 17 32 64 128 256), losses := [] }

theorem u3233 : Upper (D 1) (R 1) [52,72,130,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 134 280 18 225 225 225 481), lower := (rows 53 74 134 280 18 32 64 128 256), losses := [] }

theorem u3234 : Upper (D 1) (R 1) [52,72,130,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3235 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 134 280 48 227 195 195 451), lower := (rows 53 74 134 280 48 32 64 128 256), losses := [] }

theorem u3235 : Upper (D 1) (R 1) [52,72,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3236 : Route 9 := (fun mask => (mask,id))

def c3236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3236 : Upper (D 1) (R 1) [52,72,130,272,64] 13 := by
  apply FastRouting.sound _ _ [52,72,130,272,64] 13 (by decide) (choices 1) [1,2,128] r3236 c3236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u782
  · exact u783
  · exact u784

def b3237 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 134 280 144 99 99 227 355), lower := (rows 53 74 134 280 144 32 64 128 256), losses := [] }

theorem u3237 : Upper (D 1) (R 1) [52,72,130,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3238 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 196 11 18 432 496 432 432), lower := (rows 53 74 196 11 18 32 64 128 256), losses := [] }

theorem u3238 : Upper (D 1) (R 1) [52,72,192,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3239 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 11 48 434 466 402 402), lower := (rows 53 74 196 11 48 32 64 128 256), losses := [] }

theorem u3239 : Upper (D 1) (R 1) [52,72,192,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3239
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3239
end Delivery.IrregularNine14.P01
