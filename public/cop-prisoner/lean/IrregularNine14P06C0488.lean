import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0177
import IrregularNine14P06C0178
import IrregularNine14P06C0179

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29280 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 388 88 22 97 97 225 353), lower := (rows 7 42 388 88 22 32 64 128 256), losses := [] }

theorem u29280 : Upper (D 6) (R 6) [6,40,384,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29280
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29281 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 388 88 49 103 71 199 327), lower := (rows 7 42 388 88 49 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 23 24 16 0 67 131 259), good := (rows 455 463 388 92 477 0 64 128 256) }] }

theorem u29281 : Upper (D 6) (R 6) [6,40,384,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29281
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29282 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 388 88 50 101 69 197 325), lower := (rows 7 42 388 88 50 32 64 128 256), losses := [] }

theorem u29282 : Upper (D 6) (R 6) [6,40,384,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29282
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29283 : Route 9 := (fun mask => (mask,id))

def c29283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29283 : Upper (D 6) (R 6) [6,40,384,80,36] 13 := by
  apply FastRouting.sound _ _ [6,40,384,80,36] 13 (by decide) (choices 1) [1,2,64] r29283 c29283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10679
  · exact u10680
  · exact u10681

def b29284 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 388 88 81 39 103 167 295), lower := (rows 7 42 388 88 81 32 64 128 256), losses := [] }

theorem u29284 : Upper (D 6) (R 6) [6,40,384,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29284
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29285 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 388 88 82 37 101 165 293), lower := (rows 7 42 388 88 82 32 64 128 256), losses := [] }

theorem u29285 : Upper (D 6) (R 6) [6,40,384,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29285
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29286 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 388 88 84 35 99 163 291), lower := (rows 7 42 388 88 84 32 64 128 256), losses := [] }

theorem u29286 : Upper (D 6) (R 6) [6,40,384,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29286
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29287 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 88 112 39 71 135 263), lower := (rows 7 42 388 88 112 32 64 128 256), losses := [] }

theorem u29287 : Upper (D 6) (R 6) [6,40,384,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29287
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29288 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 133 11 28 368 368 496 368), lower := (rows 7 98 133 11 28 32 64 128 256), losses := [] }

theorem u29288 : Upper (D 6) (R 6) [6,96,129,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29288
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29289 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 11 52 376 344 472 344), lower := (rows 7 98 133 11 52 32 64 128 256), losses := [] }

theorem u29289 : Upper (D 6) (R 6) [6,96,129,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29289
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29290 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 11 56 372 340 468 340), lower := (rows 7 98 133 11 56 32 64 128 256), losses := [] }

theorem u29290 : Upper (D 6) (R 6) [6,96,129,3,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29290
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29291 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 11 276 120 120 248 376), lower := (rows 7 98 133 11 276 32 64 128 256), losses := [] }

theorem u29291 : Upper (D 6) (R 6) [6,96,129,3,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29291
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29292 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 11 280 116 116 244 372), lower := (rows 7 98 133 11 280 32 64 128 256), losses := [] }

theorem u29292 : Upper (D 6) (R 6) [6,96,129,3,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29292
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29293 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 11 304 124 92 220 348), lower := (rows 7 98 133 11 304 32 64 128 256), losses := [] }

theorem u29293 : Upper (D 6) (R 6) [6,96,129,3,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29293
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29294 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 133 13 26 368 368 496 368), lower := (rows 7 98 133 13 26 32 64 128 256), losses := [] }

theorem u29294 : Upper (D 6) (R 6) [6,96,129,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29294
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29295 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 13 56 370 338 466 338), lower := (rows 7 98 133 13 56 32 64 128 256), losses := [] }

theorem u29295 : Upper (D 6) (R 6) [6,96,129,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29295
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29296 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 13 274 120 120 248 376), lower := (rows 7 98 133 13 274 32 64 128 256), losses := [] }

theorem u29296 : Upper (D 6) (R 6) [6,96,129,5,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29296
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29297 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 13 280 114 114 242 370), lower := (rows 7 98 133 13 280 32 64 128 256), losses := [] }

theorem u29297 : Upper (D 6) (R 6) [6,96,129,5,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29297
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29298 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 13 304 122 90 218 346), lower := (rows 7 98 133 13 304 32 64 128 256), losses := [] }

theorem u29298 : Upper (D 6) (R 6) [6,96,129,5,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29298
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29299 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 133 14 25 368 368 496 368), lower := (rows 7 98 133 14 25 32 64 128 256), losses := [] }

theorem u29299 : Upper (D 6) (R 6) [6,96,129,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29299
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29300 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 133 14 49 376 344 472 344), lower := (rows 7 98 133 14 49 32 64 128 256), losses := [] }

theorem u29300 : Upper (D 6) (R 6) [6,96,129,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29300
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29301 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 133 14 56 369 337 465 337), lower := (rows 7 98 133 14 56 32 64 128 256), losses := [] }

theorem u29301 : Upper (D 6) (R 6) [6,96,129,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29301
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29302 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 133 14 273 120 120 248 376), lower := (rows 7 98 133 14 273 32 64 128 256), losses := [] }

theorem u29302 : Upper (D 6) (R 6) [6,96,129,6,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29302
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29303 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 133 14 280 113 113 241 369), lower := (rows 7 98 133 14 280 32 64 128 256), losses := [] }

theorem u29303 : Upper (D 6) (R 6) [6,96,129,6,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29303
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29304 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 133 14 304 121 89 217 345), lower := (rows 7 98 133 14 304 32 64 128 256), losses := [] }

theorem u29304 : Upper (D 6) (R 6) [6,96,129,6,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29304
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29305 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 25 26 356 356 484 356), lower := (rows 7 98 133 25 26 32 64 128 256), losses := [] }

theorem u29305 : Upper (D 6) (R 6) [6,96,129,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29305
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29306 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 133 25 28 354 354 482 354), lower := (rows 7 98 133 25 28 32 64 128 256), losses := [] }

theorem u29306 : Upper (D 6) (R 6) [6,96,129,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29306
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29307 : PairBound 9 := { available := 332, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 133 25 50 364 332 460 332), lower := (rows 7 98 133 25 50 32 64 128 256), losses := [] }

theorem u29307 : Upper (D 6) (R 6) [6,96,129,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29307
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29308 : Route 9 := (fun mask => (mask,id))

def c29308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29308 : Upper (D 6) (R 6) [6,96,129,17,36] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,36] 13 (by decide) (choices 1) [2,8,64,256] r29308 c29308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10682
  · exact u10683
  · exact u10684
  · exact u10685

def b29309 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 0, region := 354, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 25 56 358 326 454 326), lower := (rows 7 98 133 25 56 32 64 128 256), losses := [] }

theorem u29309 : Upper (D 6) (R 6) [6,96,129,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29309
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29310 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 133 25 112 302 334 398 270), lower := (rows 7 98 133 25 112 32 64 128 256), losses := [] }

theorem u29310 : Upper (D 6) (R 6) [6,96,129,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29310
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29311 : Route 9 := (fun mask => (mask,id))

def c29311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29311 : Upper (D 6) (R 6) [6,96,129,17,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,258] 13 (by decide) (choices 1) [4,8,64] r29311 c29311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10686
  · exact u10687
  · exact u10688

def r29312 : Route 9 := (fun mask => (mask,id))

def c29312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29312 : Upper (D 6) (R 6) [6,96,129,17,260] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,260] 13 (by decide) (choices 1) [2,8,64] r29312 c29312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10689
  · exact u10690
  · exact u10691

def r29313 : Route 9 := (fun mask => (mask,id))

def c29313 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29313 : Upper (D 6) (R 6) [6,96,129,17,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,264] 13 (by decide) (choices 1) [2,4,64] r29313 c29313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10692
  · exact u10693
  · exact u10694

def r29314 : Route 9 := (fun mask => (mask,id))

def c29314 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29314 : Upper (D 6) (R 6) [6,96,129,17,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,288] 13 (by decide) (choices 1) [2,4,8,64] r29314 c29314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10695
  · exact u10696
  · exact u10697
  · exact u10698

def b29315 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 133 26 28 353 353 481 353), lower := (rows 7 98 133 26 28 32 64 128 256), losses := [] }

theorem u29315 : Upper (D 6) (R 6) [6,96,129,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29315
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29316 : Route 9 := (fun mask => (mask,id))

def c29316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29316 : Upper (D 6) (R 6) [6,96,129,18,33] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,33] 13 (by decide) (choices 1) [4,8,64,256] r29316 c29316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10699
  · exact u10700
  · exact u10701
  · exact u10702

def r29317 : Route 9 := (fun mask => (mask,id))

def c29317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29317 : Upper (D 6) (R 6) [6,96,129,18,36] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,36] 13 (by decide) (choices 1) [1,8,64,256] r29317 c29317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10703
  · exact u10704
  · exact u10705
  · exact u10706

def b29318 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 26 56 357 325 453 325), lower := (rows 7 98 133 26 56 32 64 128 256), losses := [] }

theorem u29318 : Upper (D 6) (R 6) [6,96,129,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29318
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29319 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 26 112 301 333 397 269), lower := (rows 7 98 133 26 112 32 64 128 256), losses := [] }

theorem u29319 : Upper (D 6) (R 6) [6,96,129,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29319
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29320 : Route 9 := (fun mask => (mask,id))

def c29320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29320 : Upper (D 6) (R 6) [6,96,129,18,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,257] 13 (by decide) (choices 1) [4,8,64] r29320 c29320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10707
  · exact u10708
  · exact u10709

def r29321 : Route 9 := (fun mask => (mask,id))

def c29321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29321 : Upper (D 6) (R 6) [6,96,129,18,260] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,260] 13 (by decide) (choices 1) [1,8,64] r29321 c29321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10710
  · exact u10711
  · exact u10712

def r29322 : Route 9 := (fun mask => (mask,id))

def c29322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29322 : Upper (D 6) (R 6) [6,96,129,18,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,264] 13 (by decide) (choices 1) [1,4,64] r29322 c29322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10713
  · exact u10714
  · exact u10715

def r29323 : Route 9 := (fun mask => (mask,id))

def c29323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29323 : Upper (D 6) (R 6) [6,96,129,18,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,288] 13 (by decide) (choices 1) [1,4,8,64] r29323 c29323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10716
  · exact u10717
  · exact u10718
  · exact u10719

def r29324 : Route 9 := (fun mask => (mask,id))

def c29324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29324 : Upper (D 6) (R 6) [6,96,129,20,33] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,33] 13 (by decide) (choices 1) [2,8,64,256] r29324 c29324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10720
  · exact u10721
  · exact u10722
  · exact u10723

def b29325 : PairBound 9 := { available := 329, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 133 28 50 361 329 457 329), lower := (rows 7 98 133 28 50 32 64 128 256), losses := [] }

theorem u29325 : Upper (D 6) (R 6) [6,96,129,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29325
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29326 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 98 133 28 56 355 323 451 323), lower := (rows 7 98 133 28 56 32 64 128 256), losses := [] }

theorem u29326 : Upper (D 6) (R 6) [6,96,129,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29326
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29327 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 133 28 112 299 331 395 267), lower := (rows 7 98 133 28 112 32 64 128 256), losses := [] }

theorem u29327 : Upper (D 6) (R 6) [6,96,129,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29327
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29328 : Route 9 := (fun mask => (mask,id))

def c29328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29328 : Upper (D 6) (R 6) [6,96,129,20,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,257] 13 (by decide) (choices 1) [2,8,64] r29328 c29328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10724
  · exact u10725
  · exact u10726

def r29329 : Route 9 := (fun mask => (mask,id))

def c29329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29329 : Upper (D 6) (R 6) [6,96,129,20,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,258] 13 (by decide) (choices 1) [1,8,64] r29329 c29329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10727
  · exact u10728
  · exact u10729

def r29330 : Route 9 := (fun mask => (mask,id))

def c29330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29330 : Upper (D 6) (R 6) [6,96,129,20,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,264] 13 (by decide) (choices 1) [1,2,64] r29330 c29330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10730
  · exact u10731
  · exact u10732

def r29331 : Route 9 := (fun mask => (mask,id))

def c29331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29331 : Upper (D 6) (R 6) [6,96,129,20,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,288] 13 (by decide) (choices 1) [1,2,8,64] r29331 c29331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10733
  · exact u10734
  · exact u10735
  · exact u10736

def b29332 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 7 98 133 41 82 316 348 412 284), lower := (rows 7 98 133 41 82 32 64 128 256), losses := [] }

theorem u29332 : Upper (D 6) (R 6) [6,96,129,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29332
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29333 : Route 9 := (fun mask => (mask,id))

def c29333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29333 : Upper (D 6) (R 6) [6,96,129,33,68] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,68] 13 (by decide) (choices 1) [2,8,16,256] r29333 c29333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10737
  · exact u10738
  · exact u10739
  · exact u10740

def r29334 : Route 9 := (fun mask => (mask,id))

def c29334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29334 : Upper (D 6) (R 6) [6,96,129,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,72] 13 (by decide) (choices 1) [2,4,16,256] r29334 c29334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10741
  · exact u10742
  · exact u10743
  · exact u10744

def r29335 : Route 9 := (fun mask => (mask,id))

def c29335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29335 : Upper (D 6) (R 6) [6,96,129,33,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,258] 13 (by decide) (choices 1) [4,8,16,64] r29335 c29335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10745
  · exact u10746
  · exact u10747
  · exact u10748

def r29336 : Route 9 := (fun mask => (mask,id))

def c29336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29336 : Upper (D 6) (R 6) [6,96,129,33,260] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,260] 13 (by decide) (choices 1) [2,8,16,64] r29336 c29336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10749
  · exact u10750
  · exact u10751
  · exact u10752

def r29337 : Route 9 := (fun mask => (mask,id))

def c29337 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29337 : Upper (D 6) (R 6) [6,96,129,33,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,264] 13 (by decide) (choices 1) [2,4,16,64] r29337 c29337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10753
  · exact u10754
  · exact u10755
  · exact u10756

def r29338 : Route 9 := (fun mask => (mask,id))

def c29338 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29338 : Upper (D 6) (R 6) [6,96,129,33,320] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,320] 13 (by decide) (choices 1) [2,4,8,16] r29338 c29338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10757
  · exact u10758
  · exact u10759
  · exact u10760

def b29339 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 42 84 313 345 409 281), lower := (rows 7 98 133 42 84 32 64 128 256), losses := [] }

theorem u29339 : Upper (D 6) (R 6) [6,96,129,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29339
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29339
end Delivery.IrregularNine14.P06
