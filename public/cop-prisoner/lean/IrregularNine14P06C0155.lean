import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0016

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9300 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 26 164 41 336 36 67 195 323), lower := (rows 7 26 164 41 336 36 64 128 256), losses := [] }

theorem u9300 : Upper (D 6) (R 6) [6,24,160,33,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9300
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9301 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 7 26 164 41 336 96 71 135 263), lower := (rows 7 26 164 41 336 96 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 65 129 257), good := (rows 471 26 132 475 336 64 64 128 256) },{ target := 6, region := (rows 3 2 12 8 16 32 0 131 259), good := (rows 391 415 164 429 272 32 0 128 256) }] }

theorem u9301 : Upper (D 6) (R 6) [6,24,160,33,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9301
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9302 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 26 164 73 273 34 100 228 356), lower := (rows 7 26 164 73 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 17 32 100 164 292), good := (rows 477 24 484 89 281 484 64 128 256) }] }

theorem u9302 : Upper (D 6) (R 6) [6,24,160,65,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9302
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9303 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 73 273 36 98 226 354), lower := (rows 7 26 164 73 273 36 64 128 256), losses := [] }

theorem u9303 : Upper (D 6) (R 6) [6,24,160,65,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9303
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9304 : Route 9 := (fun mask => (mask,id))

def c9304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9304 : Upper (D 6) (R 6) [6,24,160,65,257,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,257,64] 13 (by decide) (choices 1) [2,4,32] r9304 c9304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u964
  · exact u965
  · exact u966

def b9305 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 26 164 73 274 33 100 228 356), lower := (rows 7 26 164 73 274 33 64 128 256), losses := [] }

theorem u9305 : Upper (D 6) (R 6) [6,24,160,65,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9305
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9306 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 73 274 36 97 225 353), lower := (rows 7 26 164 73 274 36 64 128 256), losses := [] }

theorem u9306 : Upper (D 6) (R 6) [6,24,160,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9306
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9307 : Route 9 := (fun mask => (mask,id))

def c9307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9307 : Upper (D 6) (R 6) [6,24,160,65,258,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,258,64] 13 (by decide) (choices 1) [1,4,32] r9307 c9307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u967
  · exact u968
  · exact u969

def r9308 : Route 9 := (fun mask => (mask,id))

def c9308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9308 : Upper (D 6) (R 6) [6,24,160,65,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,260,1] 13 (by decide) (choices 1) [2,32] r9308 c9308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u970
  · exact u971

def r9309 : Route 9 := (fun mask => (mask,id))

def c9309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9309 : Upper (D 6) (R 6) [6,24,160,65,260,2] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,260,2] 13 (by decide) (choices 1) [1,32] r9309 c9309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u972
  · exact u973

def r9310 : Route 9 := (fun mask => (mask,id))

def c9310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9310 : Upper (D 6) (R 6) [6,24,160,65,260,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,260,64] 13 (by decide) (choices 1) [1,2,32] r9310 c9310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u974
  · exact u975
  · exact u976

def b9311 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(2,0),(3,5),(4,0)], upper := (rows 7 26 164 73 304 33 70 198 326), lower := (rows 7 26 164 73 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 48 32 65 129 257), good := (rows 454 26 180 456 308 500 64 128 256) }] }

theorem u9311 : Upper (D 6) (R 6) [6,24,160,65,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9311
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9312 : Route 9 := (fun mask => (mask,id))

def c9312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9312 : Upper (D 6) (R 6) [6,24,160,65,288,2] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,288,2] 13 (by decide) (choices 1) [1,4] r9312 c9312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u977
  · exact u978

def b9313 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 73 304 36 67 195 323), lower := (rows 7 26 164 73 304 36 64 128 256), losses := [] }

theorem u9313 : Upper (D 6) (R 6) [6,24,160,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9313
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9314 : Route 9 := (fun mask => (mask,id))

def c9314 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9314 : Upper (D 6) (R 6) [6,24,160,65,288,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,288,64] 13 (by decide) (choices 1) [1,2,4] r9314 c9314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u979
  · exact u980
  · exact u981

def r9315 : Route 9 := (fun mask => (mask,id))

def c9315 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9315 : Upper (D 6) (R 6) [6,24,160,65,320,1] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,320,1] 13 (by decide) (choices 1) [2,4,32] r9315 c9315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u982
  · exact u983
  · exact u984

def r9316 : Route 9 := (fun mask => (mask,id))

def c9316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9316 : Upper (D 6) (R 6) [6,24,160,65,320,2] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,320,2] 13 (by decide) (choices 1) [1,4,32] r9316 c9316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u985
  · exact u986
  · exact u987

def b9317 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 73 336 36 99 163 291), lower := (rows 7 26 164 73 336 36 64 128 256), losses := [] }

theorem u9317 : Upper (D 6) (R 6) [6,24,160,65,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9317
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9318 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 26 164 74 273 33 100 228 356), lower := (rows 7 26 164 74 273 33 64 128 256), losses := [] }

theorem u9318 : Upper (D 6) (R 6) [6,24,160,66,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9318
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9319 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 74 273 36 97 225 353), lower := (rows 7 26 164 74 273 36 64 128 256), losses := [] }

theorem u9319 : Upper (D 6) (R 6) [6,24,160,66,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9319
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9320 : Route 9 := (fun mask => (mask,id))

def c9320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9320 : Upper (D 6) (R 6) [6,24,160,66,257,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,66,257,64] 13 (by decide) (choices 1) [1,4,32] r9320 c9320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u988
  · exact u989
  · exact u990

def r9321 : Route 9 := (fun mask => (mask,id))

def c9321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9321 : Upper (D 6) (R 6) [6,24,160,68,257,1] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,257,1] 13 (by decide) (choices 1) [2,32] r9321 c9321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u991
  · exact u992

def r9322 : Route 9 := (fun mask => (mask,id))

def c9322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9322 : Upper (D 6) (R 6) [6,24,160,68,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,257,2] 13 (by decide) (choices 1) [1,32] r9322 c9322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u993
  · exact u994

def r9323 : Route 9 := (fun mask => (mask,id))

def c9323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9323 : Upper (D 6) (R 6) [6,24,160,68,257,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,257,64] 13 (by decide) (choices 1) [1,2,32] r9323 c9323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u995
  · exact u996
  · exact u997

def r9324 : Route 9 := (fun mask => (mask,id))

def c9324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9324 : Upper (D 6) (R 6) [6,24,160,68,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,288,1] 13 (by decide) (choices 1) [1,2] r9324 c9324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u998
  · exact u999

def b9325 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 26 164 76 304 34 65 193 321), lower := (rows 7 26 164 76 304 34 64 128 256), losses := [] }

theorem u9325 : Upper (D 6) (R 6) [6,24,160,68,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9325
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9326 : Route 9 := (fun mask => (mask,id))

def c9326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9326 : Upper (D 6) (R 6) [6,24,160,68,288,64] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,288,64] 13 (by decide) (choices 1) [1,2] r9326 c9326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1000
  · exact u1001

def b9327 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 26 164 104 273 33 70 198 326), lower := (rows 7 26 164 104 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 16 32 65 129 257), good := (rows 454 26 172 108 464 492 64 128 256) }] }

theorem u9327 : Upper (D 6) (R 6) [6,24,160,96,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9327
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9328 : Route 9 := (fun mask => (mask,id))

def c9328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9328 : Upper (D 6) (R 6) [6,24,160,96,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,160,96,257,2] 13 (by decide) (choices 1) [1,4] r9328 c9328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1002
  · exact u1003

def b9329 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 104 273 36 67 195 323), lower := (rows 7 26 164 104 273 36 64 128 256), losses := [] }

theorem u9329 : Upper (D 6) (R 6) [6,24,160,96,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9329
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9330 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 164 104 273 96 71 135 263), lower := (rows 7 26 164 104 273 96 64 128 256), losses := [] }

theorem u9330 : Upper (D 6) (R 6) [6,24,160,96,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9330
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9331 : Route 9 := (fun mask => (mask,id))

def c9331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9331 : Upper (D 6) (R 6) [6,24,160,96,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,160,96,260,1] 13 (by decide) (choices 1) [1,2] r9331 c9331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1004
  · exact u1005

def b9332 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 0, region := 104, targets := 4 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 26 164 104 276 34 65 193 321), lower := (rows 7 26 164 104 276 34 64 128 256), losses := [] }

theorem u9332 : Upper (D 6) (R 6) [6,24,160,96,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9332
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9333 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 164 104 276 96 67 131 259), lower := (rows 7 26 164 104 276 96 64 128 256), losses := [] }

theorem u9333 : Upper (D 6) (R 6) [6,24,160,96,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9333
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9334 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 26 388 41 81 34 100 228 356), lower := (rows 7 26 388 41 81 34 64 128 256), losses := [] }

theorem u9334 : Upper (D 6) (R 6) [6,24,384,33,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9334
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9335 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 26 388 41 81 36 98 226 354), lower := (rows 7 26 388 41 81 36 64 128 256), losses := [] }

theorem u9335 : Upper (D 6) (R 6) [6,24,384,33,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9335
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9336 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 42, targets := 4 },{ cop := 0, region := 484, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 26 388 41 81 96 102 166 294), lower := (rows 7 26 388 41 81 96 64 128 256), losses := [] }

theorem u9336 : Upper (D 6) (R 6) [6,24,384,33,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9336
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9337 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 388 41 82 33 100 228 356), lower := (rows 7 26 388 41 82 33 64 128 256), losses := [] }

theorem u9337 : Upper (D 6) (R 6) [6,24,384,33,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9337
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9338 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 7 26 388 41 82 36 97 225 353), lower := (rows 7 26 388 41 82 36 64 128 256), losses := [] }

theorem u9338 : Upper (D 6) (R 6) [6,24,384,33,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9338
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9339 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 388, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 7 26 388 41 82 96 101 165 293), lower := (rows 7 26 388 41 82 96 64 128 256), losses := [] }

theorem u9339 : Upper (D 6) (R 6) [6,24,384,33,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9339
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9340 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 388 41 84 33 98 226 354), lower := (rows 7 26 388 41 84 33 64 128 256), losses := [] }

theorem u9340 : Upper (D 6) (R 6) [6,24,384,33,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9340
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9341 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 388 41 84 34 97 225 353), lower := (rows 7 26 388 41 84 34 64 128 256), losses := [] }

theorem u9341 : Upper (D 6) (R 6) [6,24,384,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9341
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9342 : Route 9 := (fun mask => (mask,id))

def c9342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9342 : Upper (D 6) (R 6) [6,24,384,33,68,64] 13 := by
  apply FastRouting.sound _ _ [6,24,384,33,68,64] 13 (by decide) (choices 1) [1,2,32] r9342 c9342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1006
  · exact u1007
  · exact u1008

def b9343 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 26 388 41 112 33 70 198 326), lower := (rows 7 26 388 41 112 33 64 128 256), losses := [] }

theorem u9343 : Upper (D 6) (R 6) [6,24,384,33,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9343
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9344 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 40, targets := 4 }], pairs := [(2,1),(2,5),(3,2)], upper := (rows 7 26 388 41 112 34 69 197 325), lower := (rows 7 26 388 41 112 34 64 128 256), losses := [] }

theorem u9344 : Upper (D 6) (R 6) [6,24,384,33,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9344
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9345 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,1),(3,6)], upper := (rows 7 26 388 41 112 36 67 195 323), lower := (rows 7 26 388 41 112 36 64 128 256), losses := [] }

theorem u9345 : Upper (D 6) (R 6) [6,24,384,33,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9345
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9346 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 388 41 112 96 71 135 263), lower := (rows 7 26 388 41 112 96 64 128 256), losses := [] }

theorem u9346 : Upper (D 6) (R 6) [6,24,384,33,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9346
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9347 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 69 26 148 40 352 480 352), lower := (rows 7 35 69 26 148 40 64 128 256), losses := [] }

theorem u9347 : Upper (D 6) (R 6) [6,33,65,18,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9347
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9348 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 26 148 96 360 424 296), lower := (rows 7 35 69 26 148 96 64 128 256), losses := [] }

theorem u9348 : Upper (D 6) (R 6) [6,33,65,18,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9348
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9349 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 26 148 288 104 232 360), lower := (rows 7 35 69 26 148 288 64 128 256), losses := [] }

theorem u9349 : Upper (D 6) (R 6) [6,33,65,18,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9349
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9350 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 26 208 36 360 424 296), lower := (rows 7 35 69 26 208 36 64 128 256), losses := [] }

theorem u9350 : Upper (D 6) (R 6) [6,33,65,18,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9350
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9351 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 26 208 40 356 420 292), lower := (rows 7 35 69 26 208 40 64 128 256), losses := [] }

theorem u9351 : Upper (D 6) (R 6) [6,33,65,18,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9351
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9352 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 26 208 288 108 172 300), lower := (rows 7 35 69 26 208 288 64 128 256), losses := [] }

theorem u9352 : Upper (D 6) (R 6) [6,33,65,18,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9352
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9353 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 26 400 36 104 232 360), lower := (rows 7 35 69 26 400 36 64 128 256), losses := [] }

theorem u9353 : Upper (D 6) (R 6) [6,33,65,18,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9353
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9354 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 26 400 40 100 228 356), lower := (rows 7 35 69 26 400 40 64 128 256), losses := [] }

theorem u9354 : Upper (D 6) (R 6) [6,33,65,18,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9354
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9355 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 26 400 96 108 172 300), lower := (rows 7 35 69 26 400 96 64 128 256), losses := [] }

theorem u9355 : Upper (D 6) (R 6) [6,33,65,18,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9355
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9356 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 56 146 36 328 456 328), lower := (rows 7 35 69 56 146 36 64 128 256), losses := [] }

theorem u9356 : Upper (D 6) (R 6) [6,33,65,48,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9356
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9357 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 69 56 146 40 324 452 324), lower := (rows 7 35 69 56 146 40 64 128 256), losses := [] }

theorem u9357 : Upper (D 6) (R 6) [6,33,65,48,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9357
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9358 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 56 146 96 332 396 268), lower := (rows 7 35 69 56 146 96 64 128 256), losses := [] }

theorem u9358 : Upper (D 6) (R 6) [6,33,65,48,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9358
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9359 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 56 146 288 76 204 332), lower := (rows 7 35 69 56 146 288 64 128 256), losses := [] }

theorem u9359 : Upper (D 6) (R 6) [6,33,65,48,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9359
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9359
end Delivery.IrregularNine14.P06
