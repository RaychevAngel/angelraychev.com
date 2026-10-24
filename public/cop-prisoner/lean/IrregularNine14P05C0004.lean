import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 140 304 40 66 137 265), lower := (rows 7 19 100 140 304 40 66 128 256), losses := [] }

theorem u240 : Upper (D 5) (R 5) [6,17,96,132,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 140 304 40 72 131 259), lower := (rows 7 19 100 140 304 40 72 128 256), losses := [] }

theorem u241 : Upper (D 5) (R 5) [6,17,96,132,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 100 168 280 33 66 140 268), lower := (rows 7 19 100 168 280 33 66 128 256), losses := [] }

theorem u242 : Upper (D 5) (R 5) [6,17,96,160,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 100 168 280 33 68 138 266), lower := (rows 7 19 100 168 280 33 68 128 256), losses := [] }

theorem u243 : Upper (D 5) (R 5) [6,17,96,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 168 280 33 72 134 262), lower := (rows 7 19 100 168 280 33 72 128 256), losses := [] }

theorem u244 : Upper (D 5) (R 5) [6,17,96,160,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 100 168 280 34 65 140 268), lower := (rows 7 19 100 168 280 34 65 128 256), losses := [] }

theorem u245 : Upper (D 5) (R 5) [6,17,96,160,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 100 168 280 34 68 137 265), lower := (rows 7 19 100 168 280 34 68 128 256), losses := [] }

theorem u246 : Upper (D 5) (R 5) [6,17,96,160,264,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b246
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 168 280 34 72 133 261), lower := (rows 7 19 100 168 280 34 72 128 256), losses := [] }

theorem u247 : Upper (D 5) (R 5) [6,17,96,160,264,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 42 280 36 65 168 296), lower := (rows 7 19 196 42 280 36 65 128 256), losses := [] }

theorem u248 : Upper (D 5) (R 5) [6,17,192,34,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 7 19 196 42 280 36 72 161 289), lower := (rows 7 19 196 42 280 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 14 8 24 127 88 131 259), good := (rows 421 501 228 508 380 36 124 128 256) }] }

theorem u249 : Upper (D 5) (R 5) [6,17,192,34,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 42 280 36 96 137 265), lower := (rows 7 19 196 42 280 36 96 128 256), losses := [] }

theorem u250 : Upper (D 5) (R 5) [6,17,192,34,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 280 33 66 168 296), lower := (rows 7 19 196 44 280 33 66 128 256), losses := [] }

theorem u251 : Upper (D 5) (R 5) [6,17,192,36,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b251
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m252_2 : Upper (D 5) (R 5) [6,17,192,36,264,1,8,2] 13 :=
  permutation_upper _ _ _ [6,17,192,36,264,1,2,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22

def r252 : Route 9 := (fun mask => (mask,id))

def c252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u252 : Upper (D 5) (R 5) [6,17,192,36,264,1,8] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,264,1,8] 13 (by decide) (choices 1) [2,32] r252 c252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m252_2
  · exact u23

def b253 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 44 280 33 96 138 266), lower := (rows 7 19 196 44 280 33 96 128 256), losses := [] }

theorem u253 : Upper (D 5) (R 5) [6,17,192,36,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 280 34 65 168 296), lower := (rows 7 19 196 44 280 34 65 128 256), losses := [] }

theorem u254 : Upper (D 5) (R 5) [6,17,192,36,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b254
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m255_1 : Upper (D 5) (R 5) [6,17,192,36,264,2,8,1] 13 :=
  permutation_upper _ _ _ [6,17,192,36,264,2,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u24

def r255 : Route 9 := (fun mask => (mask,id))

def c255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u255 : Upper (D 5) (R 5) [6,17,192,36,264,2,8] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,264,2,8] 13 (by decide) (choices 1) [1,32] r255 c255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m255_1
  · exact u25

def b256 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 44 280 34 96 137 265), lower := (rows 7 19 196 44 280 34 96 128 256), losses := [] }

theorem u256 : Upper (D 5) (R 5) [6,17,192,36,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 304 33 66 136 264), lower := (rows 7 19 196 44 304 33 66 128 256), losses := [] }

theorem u257 : Upper (D 5) (R 5) [6,17,192,36,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b257
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m258_2 : Upper (D 5) (R 5) [6,17,192,36,288,1,8,2] 13 :=
  permutation_upper _ _ _ [6,17,192,36,288,1,2,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26

def r258 : Route 9 := (fun mask => (mask,id))

def c258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u258 : Upper (D 5) (R 5) [6,17,192,36,288,1,8] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,288,1,8] 13 (by decide) (choices 1) [2,8] r258 c258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m258_2
  · exact u27

def b259 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 196 266 56 36 65 168 296), lower := (rows 7 19 196 266 56 36 65 128 256), losses := [] }

theorem u259 : Upper (D 5) (R 5) [6,17,192,258,40,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b259
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 19 196 266 56 36 72 161 289), lower := (rows 7 19 196 266 56 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 14 8 88 127 88 131 259), good := (rows 421 501 244 508 124 36 124 128 256) }] }

theorem u260 : Upper (D 5) (R 5) [6,17,192,258,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b260
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 266 56 36 96 137 265), lower := (rows 7 19 196 266 56 36 96 128 256), losses := [] }

theorem u261 : Upper (D 5) (R 5) [6,17,192,258,40,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 196 268 56 33 66 168 296), lower := (rows 7 19 196 268 56 33 66 128 256), losses := [] }

theorem u262 : Upper (D 5) (R 5) [6,17,192,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b262
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m263_2 : Upper (D 5) (R 5) [6,17,192,260,40,1,8,2] 13 :=
  permutation_upper _ _ _ [6,17,192,260,40,1,2,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28

def r263 : Route 9 := (fun mask => (mask,id))

def c263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u263 : Upper (D 5) (R 5) [6,17,192,260,40,1,8] 13 := by
  apply FastRouting.sound _ _ [6,17,192,260,40,1,8] 13 (by decide) (choices 1) [2,32] r263 c263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m263_2
  · exact u29

def b264 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 264, targets := 1 },{ cop := 0, region := 264, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 196 268 56 33 96 138 266), lower := (rows 7 19 196 268 56 33 96 128 256), losses := [] }

theorem u264 : Upper (D 5) (R 5) [6,17,192,260,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 196 268 56 34 65 168 296), lower := (rows 7 19 196 268 56 34 65 128 256), losses := [] }

theorem u265 : Upper (D 5) (R 5) [6,17,192,260,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b265
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m266_1 : Upper (D 5) (R 5) [6,17,192,260,40,2,8,1] 13 :=
  permutation_upper _ _ _ [6,17,192,260,40,2,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30

def r266 : Route 9 := (fun mask => (mask,id))

def c266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u266 : Upper (D 5) (R 5) [6,17,192,260,40,2,8] 13 := by
  apply FastRouting.sound _ _ [6,17,192,260,40,2,8] 13 (by decide) (choices 1) [1,32] r266 c266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m266_1
  · exact u31

def b267 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 196 268 56 34 96 137 265), lower := (rows 7 19 196 268 56 34 96 128 256), losses := [] }

theorem u267 : Upper (D 5) (R 5) [6,17,192,260,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 400 33 68 168 296), lower := (rows 7 26 69 42 400 33 68 128 256), losses := [] }

theorem u268 : Upper (D 5) (R 5) [6,24,65,34,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 69 42 400 33 72 164 292), lower := (rows 7 26 69 42 400 33 72 128 256), losses := [] }

theorem u269 : Upper (D 5) (R 5) [6,24,65,34,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 100, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 69 42 400 33 96 140 268), lower := (rows 7 26 69 42 400 33 96 128 256), losses := [] }

theorem u270 : Upper (D 5) (R 5) [6,24,65,34,384,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 400 36 65 168 296), lower := (rows 7 26 69 42 400 36 65 128 256), losses := [] }

theorem u271 : Upper (D 5) (R 5) [6,24,65,34,384,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 69 42 400 36 72 161 289), lower := (rows 7 26 69 42 400 36 72 128 256), losses := [] }

theorem u272 : Upper (D 5) (R 5) [6,24,65,34,384,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 100, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 69 42 400 36 96 137 265), lower := (rows 7 26 69 42 400 36 96 128 256), losses := [] }

theorem u273 : Upper (D 5) (R 5) [6,24,65,34,384,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 44 400 34 65 168 296), lower := (rows 7 26 69 44 400 34 65 128 256), losses := [] }

theorem u274 : Upper (D 5) (R 5) [6,24,65,36,384,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 69 44 400 34 72 161 289), lower := (rows 7 26 69 44 400 34 72 128 256), losses := [] }

theorem u275 : Upper (D 5) (R 5) [6,24,65,36,384,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 69 44 400 34 96 137 265), lower := (rows 7 26 69 44 400 34 96 128 256), losses := [] }

theorem u276 : Upper (D 5) (R 5) [6,24,65,36,384,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 306, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 137 304 34 68 168 296), lower := (rows 7 26 69 137 304 34 68 128 256), losses := [] }

theorem u277 : Upper (D 5) (R 5) [6,24,65,129,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 137 304 34 72 164 292), lower := (rows 7 26 69 137 304 34 72 128 256), losses := [] }

theorem u278 : Upper (D 5) (R 5) [6,24,65,129,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 69 137 304 34 96 140 268), lower := (rows 7 26 69 137 304 34 96 128 256), losses := [] }

theorem u279 : Upper (D 5) (R 5) [6,24,65,129,288,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b279
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 138 304 33 68 168 296), lower := (rows 7 26 69 138 304 33 68 128 256), losses := [] }

theorem u280 : Upper (D 5) (R 5) [6,24,65,130,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 69 138 304 33 72 164 292), lower := (rows 7 26 69 138 304 33 72 128 256), losses := [] }

theorem u281 : Upper (D 5) (R 5) [6,24,65,130,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 100, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 69 138 304 33 96 140 268), lower := (rows 7 26 69 138 304 33 96 128 256), losses := [] }

theorem u282 : Upper (D 5) (R 5) [6,24,65,130,288,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 138 304 36 65 168 296), lower := (rows 7 26 69 138 304 36 65 128 256), losses := [] }

theorem u283 : Upper (D 5) (R 5) [6,24,65,130,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 69 138 304 36 72 161 289), lower := (rows 7 26 69 138 304 36 72 128 256), losses := [] }

theorem u284 : Upper (D 5) (R 5) [6,24,65,130,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 100, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 69 138 304 36 96 137 265), lower := (rows 7 26 69 138 304 36 96 128 256), losses := [] }

theorem u285 : Upper (D 5) (R 5) [6,24,65,130,288,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b285
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 306, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 140 304 34 65 168 296), lower := (rows 7 26 69 140 304 34 65 128 256), losses := [] }

theorem u286 : Upper (D 5) (R 5) [6,24,65,132,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 69 140 304 34 72 161 289), lower := (rows 7 26 69 140 304 34 72 128 256), losses := [] }

theorem u287 : Upper (D 5) (R 5) [6,24,65,132,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 69 140 304 34 96 137 265), lower := (rows 7 26 69 140 304 34 96 128 256), losses := [] }

theorem u288 : Upper (D 5) (R 5) [6,24,65,132,288,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 69, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 26 69 140 304 40 65 162 290), lower := (rows 7 26 69 140 304 40 65 128 256), losses := [] }

theorem u289 : Upper (D 5) (R 5) [6,24,65,132,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 69, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 26 69 140 304 40 66 161 289), lower := (rows 7 26 69 140 304 40 66 128 256), losses := [] }

theorem u290 : Upper (D 5) (R 5) [6,24,65,132,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(2,1),(3,5)], upper := (rows 7 26 69 140 304 40 96 131 259), lower := (rows 7 26 69 140 304 40 96 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 42 123 128 256), good := (rows 101 120 69 236 368 104 96 128 256) }] }

theorem u291 : Upper (D 5) (R 5) [6,24,65,132,288,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 76 137 304 33 66 164 292), lower := (rows 7 26 76 137 304 33 66 128 256), losses := [] }

theorem u292 : Upper (D 5) (R 5) [6,24,72,129,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b292
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 76 137 304 33 68 162 290), lower := (rows 7 26 76 137 304 33 68 128 256), losses := [] }

theorem u293 : Upper (D 5) (R 5) [6,24,72,129,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5),(4,3)], upper := (rows 7 26 76 137 304 33 96 134 262), lower := (rows 7 26 76 137 304 33 96 128 256), losses := [] }

theorem u294 : Upper (D 5) (R 5) [6,24,72,129,288,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 137 304 34 65 164 292), lower := (rows 7 26 76 137 304 34 65 128 256), losses := [] }

theorem u295 : Upper (D 5) (R 5) [6,24,72,129,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b295
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 76 137 304 34 68 161 289), lower := (rows 7 26 76 137 304 34 68 128 256), losses := [] }

theorem u296 : Upper (D 5) (R 5) [6,24,72,129,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b296
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 76 137 304 34 96 133 261), lower := (rows 7 26 76 137 304 34 96 128 256), losses := [] }

theorem u297 : Upper (D 5) (R 5) [6,24,72,129,288,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 137 304 36 65 162 290), lower := (rows 7 26 76 137 304 36 65 128 256), losses := [] }

theorem u298 : Upper (D 5) (R 5) [6,24,72,129,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b298
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 76 137 304 36 66 161 289), lower := (rows 7 26 76 137 304 36 66 128 256), losses := [] }

theorem u299 : Upper (D 5) (R 5) [6,24,72,129,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b299
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P05
