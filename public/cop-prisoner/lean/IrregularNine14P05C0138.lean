import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0079
import IrregularNine14P05C0080
import IrregularNine14P05C0081

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8280 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 296 28 51 83 147 275), lower := (rows 35 70 140 296 28 32 64 128 256), losses := [] }

theorem u8280 : Upper (D 5) (R 5) [34,68,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8281 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 148 44 19 297 329 393 265), lower := (rows 35 70 148 44 19 32 64 128 256), losses := [] }

theorem u8281 : Upper (D 5) (R 5) [34,68,144,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8282 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 148 44 25 299 331 395 267), lower := (rows 35 70 148 44 25 32 64 128 256), losses := [] }

theorem u8282 : Upper (D 5) (R 5) [34,68,144,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8283 : Route 9 := (fun mask => (mask,id))

def c8283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8283 : Upper (D 5) (R 5) [34,68,144,36,10] 13 := by
  apply FastRouting.sound _ _ [34,68,144,36,10] 13 (by decide) (choices 1) [1,8,256] r8283 c8283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4798
  · exact u4799
  · exact u4800

def r8284 : Route 9 := (fun mask => (mask,id))

def c8284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8284 : Upper (D 5) (R 5) [34,68,144,36,257] 13 := by
  apply FastRouting.sound _ _ [34,68,144,36,257] 13 (by decide) (choices 1) [1,2,8] r8284 c8284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4801
  · exact u4802
  · exact u4803

def r8285 : Route 9 := (fun mask => (mask,id))

def c8285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8285 : Upper (D 5) (R 5) [34,68,144,36,258] 13 := by
  apply FastRouting.sound _ _ [34,68,144,36,258] 13 (by decide) (choices 1) [1,8] r8285 c8285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4804
  · exact u4805

def r8286 : Route 9 := (fun mask => (mask,id))

def c8286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8286 : Upper (D 5) (R 5) [34,68,144,36,264] 13 := by
  apply FastRouting.sound _ _ [34,68,144,36,264] 13 (by decide) (choices 1) [1,2,8] r8286 c8286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4806
  · exact u4807
  · exact u4808

def b8287 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 148 265 19 44 108 172 300), lower := (rows 35 70 148 265 19 32 64 128 256), losses := [] }

theorem u8287 : Upper (D 5) (R 5) [34,68,144,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8288 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 265 21 42 106 170 298), lower := (rows 35 70 148 265 21 32 64 128 256), losses := [] }

theorem u8288 : Upper (D 5) (R 5) [34,68,144,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8289 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 148 265 22 41 105 169 297), lower := (rows 35 70 148 265 22 32 64 128 256), losses := [] }

theorem u8289 : Upper (D 5) (R 5) [34,68,144,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8290 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 148 265 25 46 110 174 302), lower := (rows 35 70 148 265 25 32 64 128 256), losses := [] }

theorem u8290 : Upper (D 5) (R 5) [34,68,144,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8291 : Route 9 := (fun mask => (mask,id))

def c8291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8291 : Upper (D 5) (R 5) [34,68,144,257,10] 13 := by
  apply FastRouting.sound _ _ [34,68,144,257,10] 13 (by decide) (choices 1) [1,4,8] r8291 c8291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4809
  · exact u4810
  · exact u4811

def b8292 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 265 28 43 107 171 299), lower := (rows 35 70 148 265 28 32 64 128 256), losses := [] }

theorem u8292 : Upper (D 5) (R 5) [34,68,144,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8292
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8293 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 148 265 49 46 78 142 270), lower := (rows 35 70 148 265 49 32 64 128 256), losses := [] }

theorem u8293 : Upper (D 5) (R 5) [34,68,144,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8294 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 148 265 50 45 77 141 269), lower := (rows 35 70 148 265 50 32 64 128 256), losses := [] }

theorem u8294 : Upper (D 5) (R 5) [34,68,144,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8295 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 265 52 43 75 139 267), lower := (rows 35 70 148 265 52 32 64 128 256), losses := [] }

theorem u8295 : Upper (D 5) (R 5) [34,68,144,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8295
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8296 : Route 9 := (fun mask => (mask,id))

def c8296 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8296 : Upper (D 5) (R 5) [34,68,144,257,40] 13 := by
  apply FastRouting.sound _ _ [34,68,144,257,40] 13 (by decide) (choices 1) [1,2,4,8] r8296 c8296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4812
  · exact u4813
  · exact u4814
  · exact u4815

def b8297 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 266 21 41 105 169 297), lower := (rows 35 70 148 266 21 32 64 128 256), losses := [] }

theorem u8297 : Upper (D 5) (R 5) [34,68,144,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8298 : Route 9 := (fun mask => (mask,id))

def c8298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8298 : Upper (D 5) (R 5) [34,68,144,258,9] 13 := by
  apply FastRouting.sound _ _ [34,68,144,258,9] 13 (by decide) (choices 1) [1,4,8] r8298 c8298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4816
  · exact u4817
  · exact u4818

def b8299 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 266 28 41 105 169 297), lower := (rows 35 70 148 266 28 32 64 128 256), losses := [] }

theorem u8299 : Upper (D 5) (R 5) [34,68,144,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8299
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8300 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 148 266 49 45 77 141 269), lower := (rows 35 70 148 266 49 32 64 128 256), losses := [] }

theorem u8300 : Upper (D 5) (R 5) [34,68,144,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8301 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 266 52 41 73 137 265), lower := (rows 35 70 148 266 52 32 64 128 256), losses := [] }

theorem u8301 : Upper (D 5) (R 5) [34,68,144,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8302 : Route 9 := (fun mask => (mask,id))

def c8302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8302 : Upper (D 5) (R 5) [34,68,144,258,40] 13 := by
  apply FastRouting.sound _ _ [34,68,144,258,40] 13 (by decide) (choices 1) [1,4,8] r8302 c8302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4819
  · exact u4820
  · exact u4821

def b8303 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 148 268 19 41 105 169 297), lower := (rows 35 70 148 268 19 32 64 128 256), losses := [] }

theorem u8303 : Upper (D 5) (R 5) [34,68,144,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8304 : Route 9 := (fun mask => (mask,id))

def c8304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8304 : Upper (D 5) (R 5) [34,68,144,260,9] 13 := by
  apply FastRouting.sound _ _ [34,68,144,260,9] 13 (by decide) (choices 1) [1,2,8] r8304 c8304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4822
  · exact u4823
  · exact u4824

def r8305 : Route 9 := (fun mask => (mask,id))

def c8305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8305 : Upper (D 5) (R 5) [34,68,144,260,10] 13 := by
  apply FastRouting.sound _ _ [34,68,144,260,10] 13 (by decide) (choices 1) [1,8] r8305 c8305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4825
  · exact u4826

def b8306 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 148 268 49 43 75 139 267), lower := (rows 35 70 148 268 49 32 64 128 256), losses := [] }

theorem u8306 : Upper (D 5) (R 5) [34,68,144,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8307 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 148 268 50 41 73 137 265), lower := (rows 35 70 148 268 50 32 64 128 256), losses := [] }

theorem u8307 : Upper (D 5) (R 5) [34,68,144,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8308 : Route 9 := (fun mask => (mask,id))

def c8308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8308 : Upper (D 5) (R 5) [34,68,144,260,40] 13 := by
  apply FastRouting.sound _ _ [34,68,144,260,40] 13 (by decide) (choices 1) [1,2,8] r8308 c8308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4827
  · exact u4828
  · exact u4829

def b8309 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 148 296 19 45 77 141 269), lower := (rows 35 70 148 296 19 32 64 128 256), losses := [] }

theorem u8309 : Upper (D 5) (R 5) [34,68,144,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8310 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 296 21 43 75 139 267), lower := (rows 35 70 148 296 21 32 64 128 256), losses := [] }

theorem u8310 : Upper (D 5) (R 5) [34,68,144,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8311 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 148 296 22 41 73 137 265), lower := (rows 35 70 148 296 22 32 64 128 256), losses := [] }

theorem u8311 : Upper (D 5) (R 5) [34,68,144,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8312 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 148 296 25 47 79 143 271), lower := (rows 35 70 148 296 25 32 64 128 256), losses := [] }

theorem u8312 : Upper (D 5) (R 5) [34,68,144,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8313 : Route 9 := (fun mask => (mask,id))

def c8313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8313 : Upper (D 5) (R 5) [34,68,144,288,10] 13 := by
  apply FastRouting.sound _ _ [34,68,144,288,10] 13 (by decide) (choices 1) [1,4,8] r8313 c8313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4830
  · exact u4831
  · exact u4832

def b8314 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 296 28 43 75 139 267), lower := (rows 35 70 148 296 28 32 64 128 256), losses := [] }

theorem u8314 : Upper (D 5) (R 5) [34,68,144,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8315 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 164 265 19 60 92 156 284), lower := (rows 35 70 164 265 19 32 64 128 256), losses := [] }

theorem u8315 : Upper (D 5) (R 5) [34,68,160,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8316 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 164 265 21 58 90 154 282), lower := (rows 35 70 164 265 21 32 64 128 256), losses := [] }

theorem u8316 : Upper (D 5) (R 5) [34,68,160,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8317 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 164 265 22 57 89 153 281), lower := (rows 35 70 164 265 22 32 64 128 256), losses := [] }

theorem u8317 : Upper (D 5) (R 5) [34,68,160,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8318 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 164 265 25 62 94 158 286), lower := (rows 35 70 164 265 25 32 64 128 256), losses := [] }

theorem u8318 : Upper (D 5) (R 5) [34,68,160,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8319 : Route 9 := (fun mask => (mask,id))

def c8319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8319 : Upper (D 5) (R 5) [34,68,160,257,10] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,10] 13 (by decide) (choices 1) [1,4,8,16] r8319 c8319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4833
  · exact u4834
  · exact u4835
  · exact u4836

def r8320 : Route 9 := (fun mask => (mask,id))

def c8320 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8320 : Upper (D 5) (R 5) [34,68,160,257,12] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,12] 13 (by decide) (choices 1) [1,2,8,16] r8320 c8320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4837
  · exact u4838
  · exact u4839
  · exact u4840

def b8321 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 164 266 21 57 89 153 281), lower := (rows 35 70 164 266 21 32 64 128 256), losses := [] }

theorem u8321 : Upper (D 5) (R 5) [34,68,160,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8322 : Route 9 := (fun mask => (mask,id))

def c8322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8322 : Upper (D 5) (R 5) [34,68,160,258,9] 13 := by
  apply FastRouting.sound _ _ [34,68,160,258,9] 13 (by decide) (choices 1) [1,4,8,16] r8322 c8322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4841
  · exact u4842
  · exact u4843
  · exact u4844

def r8323 : Route 9 := (fun mask => (mask,id))

def c8323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8323 : Upper (D 5) (R 5) [34,68,160,258,12] 13 := by
  apply FastRouting.sound _ _ [34,68,160,258,12] 13 (by decide) (choices 1) [1,8,16] r8323 c8323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4845
  · exact u4846
  · exact u4847

def b8324 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 164 268 19 57 89 153 281), lower := (rows 35 70 164 268 19 32 64 128 256), losses := [] }

theorem u8324 : Upper (D 5) (R 5) [34,68,160,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8324
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8325 : Route 9 := (fun mask => (mask,id))

def c8325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8325 : Upper (D 5) (R 5) [34,68,160,260,9] 13 := by
  apply FastRouting.sound _ _ [34,68,160,260,9] 13 (by decide) (choices 1) [1,2,8,16] r8325 c8325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4848
  · exact u4849
  · exact u4850
  · exact u4851

def r8326 : Route 9 := (fun mask => (mask,id))

def c8326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8326 : Upper (D 5) (R 5) [34,68,160,260,10] 13 := by
  apply FastRouting.sound _ _ [34,68,160,260,10] 13 (by decide) (choices 1) [1,8,16] r8326 c8326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4852
  · exact u4853
  · exact u4854

def b8327 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 164 280 19 45 77 141 269), lower := (rows 35 70 164 280 19 32 64 128 256), losses := [] }

theorem u8327 : Upper (D 5) (R 5) [34,68,160,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8328 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 164 280 21 43 75 139 267), lower := (rows 35 70 164 280 21 32 64 128 256), losses := [] }

theorem u8328 : Upper (D 5) (R 5) [34,68,160,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8329 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 164 280 22 41 73 137 265), lower := (rows 35 70 164 280 22 32 64 128 256), losses := [] }

theorem u8329 : Upper (D 5) (R 5) [34,68,160,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8330 : Route 9 := (fun mask => (mask,id))

def c8330 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8330 : Upper (D 5) (R 5) [34,68,160,272,9] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272,9] 13 (by decide) (choices 1) [1,2,4,8] r8330 c8330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4855
  · exact u4856
  · exact u4857
  · exact u4858

def r8331 : Route 9 := (fun mask => (mask,id))

def c8331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8331 : Upper (D 5) (R 5) [34,68,160,272,10] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272,10] 13 (by decide) (choices 1) [1,4,8] r8331 c8331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4859
  · exact u4860
  · exact u4861

def r8332 : Route 9 := (fun mask => (mask,id))

def c8332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8332 : Upper (D 5) (R 5) [34,68,160,272,12] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272,12] 13 (by decide) (choices 1) [1,2,8] r8332 c8332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4862
  · exact u4863
  · exact u4864

def b8333 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 388 44 19 57 89 153 281), lower := (rows 35 70 388 44 19 32 64 128 256), losses := [] }

theorem u8333 : Upper (D 5) (R 5) [34,68,384,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8334 : PairBound 9 := { available := 27, camps := [{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 388 44 25 59 91 155 283), lower := (rows 35 70 388 44 25 32 64 128 256), losses := [] }

theorem u8334 : Upper (D 5) (R 5) [34,68,384,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8335 : Route 9 := (fun mask => (mask,id))

def c8335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8335 : Upper (D 5) (R 5) [34,68,384,36,10] 13 := by
  apply FastRouting.sound _ _ [34,68,384,36,10] 13 (by decide) (choices 1) [1,8,16] r8335 c8335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4865
  · exact u4866
  · exact u4867

def b8336 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 24, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 388 56 19 45 77 141 269), lower := (rows 35 70 388 56 19 32 64 128 256), losses := [] }

theorem u8336 : Upper (D 5) (R 5) [34,68,384,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8337 : Route 9 := (fun mask => (mask,id))

def c8337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8337 : Upper (D 5) (R 5) [34,68,384,48,5] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,5] 13 (by decide) (choices 1) [1,2,8] r8337 c8337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4868
  · exact u4869
  · exact u4870

def b8338 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 388 56 22 41 73 137 265), lower := (rows 35 70 388 56 22 32 64 128 256), losses := [] }

theorem u8338 : Upper (D 5) (R 5) [34,68,384,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8339 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 388 56 25 47 79 143 271), lower := (rows 35 70 388 56 25 32 64 128 256), losses := [] }

theorem u8339 : Upper (D 5) (R 5) [34,68,384,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8339
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8339
end Delivery.IrregularNine14.P05
