import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0029
import IrregularNine14P01C0030

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5220 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 200 18 184 248 184 440), lower := (rows 305 7 70 200 18 32 64 128 256), losses := [] }

theorem u5220 : Upper (D 1) (R 1) [304,5,66,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5221 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 7 70 200 24 178 242 178 434), lower := (rows 305 7 70 200 24 32 64 128 256), losses := [] }

theorem u5221 : Upper (D 1) (R 1) [304,5,66,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5222 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 200 48 186 218 154 410), lower := (rows 305 7 70 200 48 32 64 128 256), losses := [] }

theorem u5222 : Upper (D 1) (R 1) [304,5,66,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5222
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5223_2 : Upper (D 1) (R 1) [304,5,66,192,128,2] 13 :=
  permutation_upper _ _ _ [304,5,66,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1766

theorem m5223_8 : Upper (D 1) (R 1) [304,5,66,192,128,8] 13 :=
  permutation_upper _ _ _ [304,5,66,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1767

theorem m5223_16 : Upper (D 1) (R 1) [304,5,66,192,128,16] 13 :=
  permutation_upper _ _ _ [304,5,66,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1768

def r5223 : Route 9 := (fun mask => (mask,id))

def c5223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5223 : Upper (D 1) (R 1) [304,5,66,192,128] 13 := by
  apply FastRouting.sound _ _ [304,5,66,192,128] 13 (by decide) (choices 1) [2,8,16] r5223 c5223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5223_2
  · exact m5223_8
  · exact m5223_16

def b5224 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 76 138 18 240 240 240 496), lower := (rows 305 7 76 138 18 32 64 128 256), losses := [] }

theorem u5224 : Upper (D 1) (R 1) [304,5,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5224
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5225 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 138 48 242 210 210 466), lower := (rows 305 7 76 138 48 32 64 128 256), losses := [] }

theorem u5225 : Upper (D 1) (R 1) [304,5,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5225
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5226_2 : Upper (D 1) (R 1) [304,5,72,130,64,2] 13 :=
  permutation_upper _ _ _ [304,5,72,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1769

theorem m5226_16 : Upper (D 1) (R 1) [304,5,72,130,64,16] 13 :=
  permutation_upper _ _ _ [304,5,72,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1771

def r5226 : Route 9 := (fun mask => (mask,id))

def c5226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5226 : Upper (D 1) (R 1) [304,5,72,130,64] 13 := by
  apply FastRouting.sound _ _ [304,5,72,130,64] 13 (by decide) (choices 1) [2,16,128] r5226 c5226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5226_2
  · exact m5226_16
  · exact u1773

theorem m5227_2 : Upper (D 1) (R 1) [304,5,72,130,128,2] 13 :=
  permutation_upper _ _ _ [304,5,72,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1770

theorem m5227_16 : Upper (D 1) (R 1) [304,5,72,130,128,16] 13 :=
  permutation_upper _ _ _ [304,5,72,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1772

theorem m5227_64 : Upper (D 1) (R 1) [304,5,72,130,128,64] 13 :=
  permutation_upper _ _ _ [304,5,72,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1773

def r5227 : Route 9 := (fun mask => (mask,id))

def c5227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5227 : Upper (D 1) (R 1) [304,5,72,130,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,130,128] 13 (by decide) (choices 1) [2,16,64] r5227 c5227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5227_2
  · exact m5227_16
  · exact m5227_64

def b5228 : PairBound 9 := { available := 226, camps := [], pairs := [(2,4)], upper := (rows 305 7 76 152 18 226 226 226 482), lower := (rows 305 7 76 152 18 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 50 82 146 274), good := (rows 481 487 76 492 482 32 64 128 256) }] }

theorem u5228 : Upper (D 1) (R 1) [304,5,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5228
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5229 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 152 48 226 194 194 450), lower := (rows 305 7 76 152 48 32 64 128 256), losses := [] }

theorem u5229 : Upper (D 1) (R 1) [304,5,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5230 : Route 9 := (fun mask => (mask,id))

def c5230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5230 : Upper (D 1) (R 1) [304,5,72,144,64] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,64] 13 (by decide) (choices 1) [2,128] r5230 c5230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1774
  · exact u1775

def b5231 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 76 152 144 98 98 226 354), lower := (rows 305 7 76 152 144 32 64 128 256), losses := [] }

theorem u5231 : Upper (D 1) (R 1) [304,5,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5232 : Route 9 := (fun mask => (mask,id))

def c5232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5232 : Upper (D 1) (R 1) [304,5,192,80,2] 13 := by
  apply FastRouting.sound _ _ [304,5,192,80,2] 13 (by decide) (choices 1) [2,8,128] r5232 c5232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1776
  · exact u1777
  · exact u1778

def b5233 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 7 196 88 24 162 226 162 418), lower := (rows 305 7 196 88 24 32 64 128 256), losses := [] }

theorem u5233 : Upper (D 1) (R 1) [304,5,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 196 88 48 170 202 138 394), lower := (rows 305 7 196 88 48 32 64 128 256), losses := [] }

theorem u5234 : Upper (D 1) (R 1) [304,5,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5235 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 196 88 144 42 106 170 298), lower := (rows 305 7 196 88 144 32 64 128 256), losses := [] }

theorem u5235 : Upper (D 1) (R 1) [304,5,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5236 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 7 88 18 224 224 224 480), lower := (rows 305 14 7 88 18 32 64 128 256), losses := [] }

theorem u5236 : Upper (D 1) (R 1) [304,12,3,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5237 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 7 88 48 226 194 194 450), lower := (rows 305 14 7 88 48 32 64 128 256), losses := [] }

theorem u5237 : Upper (D 1) (R 1) [304,12,3,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 7 88 80 162 226 162 418), lower := (rows 305 14 7 88 80 32 64 128 256), losses := [] }

theorem u5238 : Upper (D 1) (R 1) [304,12,3,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5239 : Route 9 := (fun mask => (mask,id))

def c5239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5239 : Upper (D 1) (R 1) [304,12,3,80,128] 13 := by
  apply FastRouting.sound _ _ [304,12,3,80,128] 13 (by decide) (choices 1) [2,64,128] r5239 c5239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1779
  · exact u1780
  · exact u1781

def b5240 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 7 200 18 240 240 240 496), lower := (rows 305 14 7 200 18 32 64 128 256), losses := [] }

theorem u5240 : Upper (D 1) (R 1) [304,12,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 7 200 48 242 210 210 466), lower := (rows 305 14 7 200 48 32 64 128 256), losses := [] }

theorem u5241 : Upper (D 1) (R 1) [304,12,3,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5241
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5242_2 : Upper (D 1) (R 1) [304,12,3,192,64,2] 13 :=
  permutation_upper _ _ _ [304,12,3,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1782

theorem m5242_16 : Upper (D 1) (R 1) [304,12,3,192,64,16] 13 :=
  permutation_upper _ _ _ [304,12,3,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1783

def r5242 : Route 9 := (fun mask => (mask,id))

def c5242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5242 : Upper (D 1) (R 1) [304,12,3,192,64] 13 := by
  apply FastRouting.sound _ _ [304,12,3,192,64] 13 (by decide) (choices 1) [2,16,128] r5242 c5242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5242_2
  · exact m5242_16
  · exact u1784

def b5243 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 73 18 224 224 224 480), lower := (rows 305 14 22 73 18 32 64 128 256), losses := [] }

theorem u5243 : Upper (D 1) (R 1) [304,12,18,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 73 48 226 194 194 450), lower := (rows 305 14 22 73 48 32 64 128 256), losses := [] }

theorem u5244 : Upper (D 1) (R 1) [304,12,18,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 73 80 162 226 162 418), lower := (rows 305 14 22 73 80 32 64 128 256), losses := [] }

theorem u5245 : Upper (D 1) (R 1) [304,12,18,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5246 : Route 9 := (fun mask => (mask,id))

def c5246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5246 : Upper (D 1) (R 1) [304,12,18,65,128] 13 := by
  apply FastRouting.sound _ _ [304,12,18,65,128] 13 (by decide) (choices 1) [2,64,128] r5246 c5246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1785
  · exact u1786
  · exact u1787

def b5247 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 14 22 104 17 226 194 194 450), lower := (rows 305 14 22 104 17 32 64 128 256), losses := [] }

theorem u5247 : Upper (D 1) (R 1) [304,12,18,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5248 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 104 18 225 193 193 449), lower := (rows 305 14 22 104 18 32 64 128 256), losses := [] }

theorem u5248 : Upper (D 1) (R 1) [304,12,18,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5248
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5249 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 104 80 163 195 131 387), lower := (rows 305 14 22 104 80 32 64 128 256), losses := [] }

theorem u5249 : Upper (D 1) (R 1) [304,12,18,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5250 : Route 9 := (fun mask => (mask,id))

def c5250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5250 : Upper (D 1) (R 1) [304,12,18,96,128] 13 := by
  apply FastRouting.sound _ _ [304,12,18,96,128] 13 (by decide) (choices 1) [1,2,64,128] r5250 c5250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1788
  · exact u1789
  · exact u1790
  · exact u1791

def b5251 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 14 22 200 17 226 226 226 482), lower := (rows 305 14 22 200 17 32 64 128 256), losses := [] }

theorem u5251 : Upper (D 1) (R 1) [304,12,18,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5252 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 200 18 225 225 225 481), lower := (rows 305 14 22 200 18 32 64 128 256), losses := [] }

theorem u5252 : Upper (D 1) (R 1) [304,12,18,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5253 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 200 48 227 195 195 451), lower := (rows 305 14 22 200 48 32 64 128 256), losses := [] }

theorem u5253 : Upper (D 1) (R 1) [304,12,18,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5254 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 200 80 163 227 163 419), lower := (rows 305 14 22 200 80 32 64 128 256), losses := [] }

theorem u5254 : Upper (D 1) (R 1) [304,12,18,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5255 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 69 138 18 240 240 240 496), lower := (rows 305 14 69 138 18 32 64 128 256), losses := [] }

theorem u5255 : Upper (D 1) (R 1) [304,12,65,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5256 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 138 48 242 210 210 466), lower := (rows 305 14 69 138 48 32 64 128 256), losses := [] }

theorem u5256 : Upper (D 1) (R 1) [304,12,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5256
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5257_2 : Upper (D 1) (R 1) [304,12,65,130,64,2] 13 :=
  permutation_upper _ _ _ [304,12,65,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1792

theorem m5257_16 : Upper (D 1) (R 1) [304,12,65,130,64,16] 13 :=
  permutation_upper _ _ _ [304,12,65,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1794

def r5257 : Route 9 := (fun mask => (mask,id))

def c5257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5257 : Upper (D 1) (R 1) [304,12,65,130,64] 13 := by
  apply FastRouting.sound _ _ [304,12,65,130,64] 13 (by decide) (choices 1) [2,16,128] r5257 c5257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5257_2
  · exact m5257_16
  · exact u1796

theorem m5258_2 : Upper (D 1) (R 1) [304,12,65,130,128,2] 13 :=
  permutation_upper _ _ _ [304,12,65,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1793

theorem m5258_16 : Upper (D 1) (R 1) [304,12,65,130,128,16] 13 :=
  permutation_upper _ _ _ [304,12,65,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1795

theorem m5258_64 : Upper (D 1) (R 1) [304,12,65,130,128,64] 13 :=
  permutation_upper _ _ _ [304,12,65,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1796

def r5258 : Route 9 := (fun mask => (mask,id))

def c5258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5258 : Upper (D 1) (R 1) [304,12,65,130,128] 13 := by
  apply FastRouting.sound _ _ [304,12,65,130,128] 13 (by decide) (choices 1) [2,16,64] r5258 c5258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5258_2
  · exact m5258_16
  · exact m5258_64

def b5259 : PairBound 9 := { available := 226, camps := [], pairs := [(2,4)], upper := (rows 305 14 69 152 18 226 226 226 482), lower := (rows 305 14 69 152 18 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 8 0 50 82 146 274), good := (rows 485 494 69 488 482 32 64 128 256) }] }

theorem u5259 : Upper (D 1) (R 1) [304,12,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5259
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 152 48 226 194 194 450), lower := (rows 305 14 69 152 48 32 64 128 256), losses := [] }

theorem u5260 : Upper (D 1) (R 1) [304,12,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5261 : Route 9 := (fun mask => (mask,id))

def c5261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5261 : Upper (D 1) (R 1) [304,12,65,144,64] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,64] 13 (by decide) (choices 1) [2,128] r5261 c5261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1797
  · exact u1798

def b5262 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 69 152 144 98 98 226 354), lower := (rows 305 14 69 152 144 32 64 128 256), losses := [] }

theorem u5262 : Upper (D 1) (R 1) [304,12,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5263 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 14 70 152 17 226 226 226 482), lower := (rows 305 14 70 152 17 32 64 128 256), losses := [] }

theorem u5263 : Upper (D 1) (R 1) [304,12,66,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5264 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 70 152 18 225 225 225 481), lower := (rows 305 14 70 152 18 32 64 128 256), losses := [] }

theorem u5264 : Upper (D 1) (R 1) [304,12,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5265 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 70 152 48 227 195 195 451), lower := (rows 305 14 70 152 48 32 64 128 256), losses := [] }

theorem u5265 : Upper (D 1) (R 1) [304,12,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5266 : Route 9 := (fun mask => (mask,id))

def c5266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5266 : Upper (D 1) (R 1) [304,12,66,144,64] 13 := by
  apply FastRouting.sound _ _ [304,12,66,144,64] 13 (by decide) (choices 1) [1,2,128] r5266 c5266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1799
  · exact u1800
  · exact u1801

def b5267 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 70 152 144 99 99 227 355), lower := (rows 305 14 70 152 144 32 64 128 256), losses := [] }

theorem u5267 : Upper (D 1) (R 1) [304,12,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 14 84 168 17 226 194 194 450), lower := (rows 305 14 84 168 17 32 64 128 256), losses := [] }

theorem u5268 : Upper (D 1) (R 1) [304,12,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5268
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5269_1 : Upper (D 1) (R 1) [304,12,80,160,2,1] 13 :=
  permutation_upper _ _ _ [304,12,80,160,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1802

def r5269 : Route 9 := (fun mask => (mask,id))

def c5269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5269 : Upper (D 1) (R 1) [304,12,80,160,2] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,2] 13 (by decide) (choices 1) [1,2,64,128] r5269 c5269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5269_1
  · exact u1804
  · exact u1805
  · exact u1806

def b5270 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 84 168 80 163 195 131 387), lower := (rows 305 14 84 168 80 32 64 128 256), losses := [] }

theorem u5270 : Upper (D 1) (R 1) [304,12,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5270
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5271_1 : Upper (D 1) (R 1) [304,12,80,160,128,1] 13 :=
  permutation_upper _ _ _ [304,12,80,160,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1803

theorem m5271_2 : Upper (D 1) (R 1) [304,12,80,160,128,2] 13 :=
  permutation_upper _ _ _ [304,12,80,160,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1805

def r5271 : Route 9 := (fun mask => (mask,id))

def c5271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5271 : Upper (D 1) (R 1) [304,12,80,160,128] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,128] 13 (by decide) (choices 1) [1,2,64] r5271 c5271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5271_1
  · exact m5271_2
  · exact u1807

def b5272 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 73 18 224 224 224 480), lower := (rows 305 22 14 73 18 32 64 128 256), losses := [] }

theorem u5272 : Upper (D 1) (R 1) [304,20,10,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 73 48 226 194 194 450), lower := (rows 305 22 14 73 48 32 64 128 256), losses := [] }

theorem u5273 : Upper (D 1) (R 1) [304,20,10,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 73 80 162 226 162 418), lower := (rows 305 22 14 73 80 32 64 128 256), losses := [] }

theorem u5274 : Upper (D 1) (R 1) [304,20,10,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5275 : Route 9 := (fun mask => (mask,id))

def c5275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5275 : Upper (D 1) (R 1) [304,20,10,65,128] 13 := by
  apply FastRouting.sound _ _ [304,20,10,65,128] 13 (by decide) (choices 1) [2,64,128] r5275 c5275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1808
  · exact u1809
  · exact u1810

def b5276 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 14 104 17 226 194 194 450), lower := (rows 305 22 14 104 17 32 64 128 256), losses := [] }

theorem u5276 : Upper (D 1) (R 1) [304,20,10,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5277 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 104 18 225 193 193 449), lower := (rows 305 22 14 104 18 32 64 128 256), losses := [] }

theorem u5277 : Upper (D 1) (R 1) [304,20,10,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5278 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 104 80 163 195 131 387), lower := (rows 305 22 14 104 80 32 64 128 256), losses := [] }

theorem u5278 : Upper (D 1) (R 1) [304,20,10,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5279 : Route 9 := (fun mask => (mask,id))

def c5279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5279 : Upper (D 1) (R 1) [304,20,10,96,128] 13 := by
  apply FastRouting.sound _ _ [304,20,10,96,128] 13 (by decide) (choices 1) [1,2,64,128] r5279 c5279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1811
  · exact u1812
  · exact u1813
  · exact u1814

#print axioms u5279
end Delivery.IrregularNine14.P01
