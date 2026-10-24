import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0030

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 22 14 200 17 226 226 226 482), lower := (rows 305 22 14 200 17 32 64 128 256), losses := [] }

theorem u5280 : Upper (D 1) (R 1) [304,20,10,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5281 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 200 18 225 225 225 481), lower := (rows 305 22 14 200 18 32 64 128 256), losses := [] }

theorem u5281 : Upper (D 1) (R 1) [304,20,10,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5282 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 200 48 227 195 195 451), lower := (rows 305 22 14 200 48 32 64 128 256), losses := [] }

theorem u5282 : Upper (D 1) (R 1) [304,20,10,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5283 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 200 80 163 227 163 419), lower := (rows 305 22 14 200 80 32 64 128 256), losses := [] }

theorem u5283 : Upper (D 1) (R 1) [304,20,10,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5284 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 44 74 17 226 194 194 450), lower := (rows 305 22 44 74 17 32 64 128 256), losses := [] }

theorem u5284 : Upper (D 1) (R 1) [304,20,40,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5285 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 44 74 18 225 193 193 449), lower := (rows 305 22 44 74 18 32 64 128 256), losses := [] }

theorem u5285 : Upper (D 1) (R 1) [304,20,40,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5286 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 44 74 80 163 195 131 387), lower := (rows 305 22 44 74 80 32 64 128 256), losses := [] }

theorem u5286 : Upper (D 1) (R 1) [304,20,40,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5286
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5287 : Route 9 := (fun mask => (mask,id))

def c5287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5287 : Upper (D 1) (R 1) [304,20,40,66,128] 13 := by
  apply FastRouting.sound _ _ [304,20,40,66,128] 13 (by decide) (choices 1) [1,2,64,128] r5287 c5287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1815
  · exact u1816
  · exact u1817
  · exact u1818

def b5288 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 44 200 17 226 194 194 450), lower := (rows 305 22 44 200 17 32 64 128 256), losses := [] }

theorem u5288 : Upper (D 1) (R 1) [304,20,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5289 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 44 200 18 227 195 195 451), lower := (rows 305 22 44 200 18 32 64 128 256), losses := [] }

theorem u5289 : Upper (D 1) (R 1) [304,20,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5289
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 44 200 80 163 195 131 387), lower := (rows 305 22 44 200 80 32 64 128 256), losses := [] }

theorem u5290 : Upper (D 1) (R 1) [304,20,40,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5291 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 73 18 168 232 168 424), lower := (rows 305 22 70 73 18 32 64 128 256), losses := [] }

theorem u5291 : Upper (D 1) (R 1) [304,20,66,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5292 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 22 70 73 24 162 226 162 418), lower := (rows 305 22 70 73 24 32 64 128 256), losses := [] }

theorem u5292 : Upper (D 1) (R 1) [304,20,66,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5293 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 73 48 170 202 138 394), lower := (rows 305 22 70 73 48 32 64 128 256), losses := [] }

theorem u5293 : Upper (D 1) (R 1) [304,20,66,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5294 : Route 9 := (fun mask => (mask,id))

def c5294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5294 : Upper (D 1) (R 1) [304,20,66,65,128] 13 := by
  apply FastRouting.sound _ _ [304,20,66,65,128] 13 (by decide) (choices 1) [2,8,128] r5294 c5294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1819
  · exact u1820
  · exact u1821

def b5295 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 22 70 104 17 170 202 138 394), lower := (rows 305 22 70 104 17 32 64 128 256), losses := [] }

theorem u5295 : Upper (D 1) (R 1) [304,20,66,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5296 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 104 18 169 201 137 393), lower := (rows 305 22 70 104 18 32 64 128 256), losses := [] }

theorem u5296 : Upper (D 1) (R 1) [304,20,66,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5296
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5297 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 70 104 24 163 195 131 387), lower := (rows 305 22 70 104 24 32 64 128 256), losses := [] }

theorem u5297 : Upper (D 1) (R 1) [304,20,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5298 : Route 9 := (fun mask => (mask,id))

def c5298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5298 : Upper (D 1) (R 1) [304,20,66,96,128] 13 := by
  apply FastRouting.sound _ _ [304,20,66,96,128] 13 (by decide) (choices 1) [1,2,8,128] r5298 c5298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1822
  · exact u1823
  · exact u1824
  · exact u1825

def b5299 : PairBound 9 := { available := 232, camps := [{ cop := 6, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 137 18 232 232 232 488), lower := (rows 305 22 70 137 18 32 64 128 256), losses := [] }

theorem u5299 : Upper (D 1) (R 1) [304,20,66,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5299
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5300 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 22 70 137 24 226 226 226 482), lower := (rows 305 22 70 137 24 32 64 128 256), losses := [] }

theorem u5300 : Upper (D 1) (R 1) [304,20,66,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5301 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 137 48 234 202 202 458), lower := (rows 305 22 70 137 48 32 64 128 256), losses := [] }

theorem u5301 : Upper (D 1) (R 1) [304,20,66,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5302 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 137 80 170 234 170 426), lower := (rows 305 22 70 137 80 32 64 128 256), losses := [] }

theorem u5302 : Upper (D 1) (R 1) [304,20,66,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5303 : Route 9 := (fun mask => (mask,id))

def c5303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5303 : Upper (D 1) (R 1) [304,20,66,129,128] 13 := by
  apply FastRouting.sound _ _ [304,20,66,129,128] 13 (by decide) (choices 1) [2,8,64] r5303 c5303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1826
  · exact u1827
  · exact u1828

def b5304 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 22 70 168 17 234 202 202 458), lower := (rows 305 22 70 168 17 32 64 128 256), losses := [] }

theorem u5304 : Upper (D 1) (R 1) [304,20,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5305 : PairBound 9 := { available := 201, camps := [{ cop := 6, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 168 18 233 201 201 457), lower := (rows 305 22 70 168 18 32 64 128 256), losses := [] }

theorem u5305 : Upper (D 1) (R 1) [304,20,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 22 70 168 24 227 195 195 451), lower := (rows 305 22 70 168 24 32 64 128 256), losses := [] }

theorem u5306 : Upper (D 1) (R 1) [304,20,66,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5307 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 168 80 171 203 139 395), lower := (rows 305 22 70 168 80 32 64 128 256), losses := [] }

theorem u5307 : Upper (D 1) (R 1) [304,20,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5308 : Route 9 := (fun mask => (mask,id))

def c5308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5308 : Upper (D 1) (R 1) [304,20,66,160,128] 13 := by
  apply FastRouting.sound _ _ [304,20,66,160,128] 13 (by decide) (choices 1) [1,2,8,64] r5308 c5308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1829
  · exact u1830
  · exact u1831
  · exact u1832

def b5309 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 22 70 200 17 170 234 170 426), lower := (rows 305 22 70 200 17 32 64 128 256), losses := [] }

theorem u5309 : Upper (D 1) (R 1) [304,20,66,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5310 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 200 18 169 233 169 425), lower := (rows 305 22 70 200 18 32 64 128 256), losses := [] }

theorem u5310 : Upper (D 1) (R 1) [304,20,66,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5311 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 22 70 200 24 163 227 163 419), lower := (rows 305 22 70 200 24 32 64 128 256), losses := [] }

theorem u5311 : Upper (D 1) (R 1) [304,20,66,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5312 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 200 48 171 203 139 395), lower := (rows 305 22 70 200 48 32 64 128 256), losses := [] }

theorem u5312 : Upper (D 1) (R 1) [304,20,66,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5312
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 70 200 144 43 107 171 299), lower := (rows 305 22 70 200 144 32 64 128 256), losses := [] }

theorem u5313 : Upper (D 1) (R 1) [304,20,66,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5314 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 76 42 17 226 194 194 450), lower := (rows 305 22 76 42 17 32 64 128 256), losses := [] }

theorem u5314 : Upper (D 1) (R 1) [304,20,72,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5315 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 42 18 225 193 193 449), lower := (rows 305 22 76 42 18 32 64 128 256), losses := [] }

theorem u5315 : Upper (D 1) (R 1) [304,20,72,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 76 42 80 163 195 131 387), lower := (rows 305 22 76 42 80 32 64 128 256), losses := [] }

theorem u5316 : Upper (D 1) (R 1) [304,20,72,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5317 : Route 9 := (fun mask => (mask,id))

def c5317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5317 : Upper (D 1) (R 1) [304,20,72,34,128] 13 := by
  apply FastRouting.sound _ _ [304,20,72,34,128] 13 (by decide) (choices 1) [1,2,64,128] r5317 c5317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1833
  · exact u1834
  · exact u1835
  · exact u1836

def b5318 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 137 18 226 226 226 482), lower := (rows 305 22 76 137 18 32 64 128 256), losses := [] }

theorem u5318 : Upper (D 1) (R 1) [304,20,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 137 48 226 194 194 450), lower := (rows 305 22 76 137 48 32 64 128 256), losses := [] }

theorem u5319 : Upper (D 1) (R 1) [304,20,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5319
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 76 137 80 162 226 162 418), lower := (rows 305 22 76 137 80 32 64 128 256), losses := [] }

theorem u5320 : Upper (D 1) (R 1) [304,20,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 137 144 98 98 226 354), lower := (rows 305 22 76 137 144 32 64 128 256), losses := [] }

theorem u5321 : Upper (D 1) (R 1) [304,20,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 22 76 138 17 226 226 226 482), lower := (rows 305 22 76 138 17 32 64 128 256), losses := [] }

theorem u5322 : Upper (D 1) (R 1) [304,20,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 138 18 225 225 225 481), lower := (rows 305 22 76 138 18 32 64 128 256), losses := [] }

theorem u5323 : Upper (D 1) (R 1) [304,20,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5324 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 138 48 227 195 195 451), lower := (rows 305 22 76 138 48 32 64 128 256), losses := [] }

theorem u5324 : Upper (D 1) (R 1) [304,20,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5325 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 76 138 80 163 227 163 419), lower := (rows 305 22 76 138 80 32 64 128 256), losses := [] }

theorem u5325 : Upper (D 1) (R 1) [304,20,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5326 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 138 144 99 99 227 355), lower := (rows 305 22 76 138 144 32 64 128 256), losses := [] }

theorem u5326 : Upper (D 1) (R 1) [304,20,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 76 168 17 226 194 194 450), lower := (rows 305 22 76 168 17 32 64 128 256), losses := [] }

theorem u5327 : Upper (D 1) (R 1) [304,20,72,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5328 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 168 18 227 195 195 451), lower := (rows 305 22 76 168 18 32 64 128 256), losses := [] }

theorem u5328 : Upper (D 1) (R 1) [304,20,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5329 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 76 168 80 163 195 131 387), lower := (rows 305 22 76 168 80 32 64 128 256), losses := [] }

theorem u5329 : Upper (D 1) (R 1) [304,20,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5330 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 168 144 99 67 195 323), lower := (rows 305 22 76 168 144 32 64 128 256), losses := [] }

theorem u5330 : Upper (D 1) (R 1) [304,20,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5331 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 100 73 18 170 202 138 394), lower := (rows 305 22 100 73 18 32 64 128 256), losses := [] }

theorem u5331 : Upper (D 1) (R 1) [304,20,96,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 22 100 73 24 162 194 130 386), lower := (rows 305 22 100 73 24 32 64 128 256), losses := [] }

theorem u5332 : Upper (D 1) (R 1) [304,20,96,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5333 : Route 9 := (fun mask => (mask,id))

def c5333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5333 : Upper (D 1) (R 1) [304,20,96,65,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65,128] 13 (by decide) (choices 1) [2,8,128] r5333 c5333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1837
  · exact u1838
  · exact u1839

def b5334 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 100 137 18 234 202 202 458), lower := (rows 305 22 100 137 18 32 64 128 256), losses := [] }

theorem u5334 : Upper (D 1) (R 1) [304,20,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5335 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 100 137 24 226 194 194 450), lower := (rows 305 22 100 137 24 32 64 128 256), losses := [] }

theorem u5335 : Upper (D 1) (R 1) [304,20,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5336 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 137 80 170 202 138 394), lower := (rows 305 22 100 137 80 32 64 128 256), losses := [] }

theorem u5336 : Upper (D 1) (R 1) [304,20,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5337 : Route 9 := (fun mask => (mask,id))

def c5337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5337 : Upper (D 1) (R 1) [304,20,96,129,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129,128] 13 (by decide) (choices 1) [2,8,64] r5337 c5337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1840
  · exact u1841
  · exact u1842

def b5338 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 22 100 138 17 234 202 202 458), lower := (rows 305 22 100 138 17 32 64 128 256), losses := [] }

theorem u5338 : Upper (D 1) (R 1) [304,20,96,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5338
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5339 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 100 138 18 233 201 201 457), lower := (rows 305 22 100 138 18 32 64 128 256), losses := [] }

theorem u5339 : Upper (D 1) (R 1) [304,20,96,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5339
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5339
end Delivery.IrregularNine14.P01
