import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0028
import IrregularNine14P06C0029

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11280 : Route 9 := (fun mask => (mask,id))

def c11280 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11280 : Upper (D 6) (R 6) [6,136,288,65,96,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,96,1] 13 (by decide) (choices 1) [2,4,16] r11280 c11280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1736
  · exact u1737
  · exact u1738

def r11281 : Route 9 := (fun mask => (mask,id))

def c11281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11281 : Upper (D 6) (R 6) [6,136,288,65,96,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,96,2] 13 (by decide) (choices 1) [1,4,16] r11281 c11281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1739
  · exact u1740
  · exact u1741

def b11282 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 73 112 36 83 147 275), lower := (rows 7 138 292 73 112 36 64 128 256), losses := [] }

theorem u11282 : Upper (D 6) (R 6) [6,136,288,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11282
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11283 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 73 112 48 71 135 263), lower := (rows 7 138 292 73 112 48 64 128 256), losses := [] }

theorem u11283 : Upper (D 6) (R 6) [6,136,288,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11283
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11284 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 74 49 33 84 212 340), lower := (rows 7 138 292 74 49 33 64 128 256), losses := [] }

theorem u11284 : Upper (D 6) (R 6) [6,136,288,66,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11284
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11285 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 138 292 74 49 36 81 209 337), lower := (rows 7 138 292 74 49 36 64 128 256), losses := [] }

theorem u11285 : Upper (D 6) (R 6) [6,136,288,66,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11285
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11286 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 74 49 48 69 197 325), lower := (rows 7 138 292 74 49 48 64 128 256), losses := [] }

theorem u11286 : Upper (D 6) (R 6) [6,136,288,66,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11286
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11287 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 4, region := 260, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 138 292 74 49 96 85 149 277), lower := (rows 7 138 292 74 49 96 64 128 256), losses := [] }

theorem u11287 : Upper (D 6) (R 6) [6,136,288,66,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11287
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11288 : Route 9 := (fun mask => (mask,id))

def c11288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11288 : Upper (D 6) (R 6) [6,136,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,66,68,1] 13 (by decide) (choices 1) [1,16,32] r11288 c11288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1742
  · exact u1743
  · exact u1744

def b11289 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 372, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 138 292 74 84 48 97 161 289), lower := (rows 7 138 292 74 84 48 64 128 256), losses := [] }

theorem u11289 : Upper (D 6) (R 6) [6,136,288,66,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11289
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11290 : Route 9 := (fun mask => (mask,id))

def c11290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11290 : Upper (D 6) (R 6) [6,136,288,66,96,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,66,96,1] 13 (by decide) (choices 1) [1,4,16] r11290 c11290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1745
  · exact u1746
  · exact u1747

def b11291 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 74 112 36 81 145 273), lower := (rows 7 138 292 74 112 36 64 128 256), losses := [] }

theorem u11291 : Upper (D 6) (R 6) [6,136,288,66,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11291
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11292 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 74 112 48 69 133 261), lower := (rows 7 138 292 74 112 48 64 128 256), losses := [] }

theorem u11292 : Upper (D 6) (R 6) [6,136,288,66,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11292
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11293 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 76 49 33 82 210 338), lower := (rows 7 138 292 76 49 33 64 128 256), losses := [] }

theorem u11293 : Upper (D 6) (R 6) [6,136,288,68,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11293
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11294 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 332, targets := 2 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 7 138 292 76 49 34 81 209 337), lower := (rows 7 138 292 76 49 34 64 128 256), losses := [] }

theorem u11294 : Upper (D 6) (R 6) [6,136,288,68,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11294
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11295 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 76 49 48 67 195 323), lower := (rows 7 138 292 76 49 48 64 128 256), losses := [] }

theorem u11295 : Upper (D 6) (R 6) [6,136,288,68,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11295
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11296 : Route 9 := (fun mask => (mask,id))

def c11296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11296 : Upper (D 6) (R 6) [6,136,288,68,33,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,33,64] 13 (by decide) (choices 1) [1,2,16] r11296 c11296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1748
  · exact u1749
  · exact u1750

def r11297 : Route 9 := (fun mask => (mask,id))

def c11297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11297 : Upper (D 6) (R 6) [6,136,288,68,34,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,34,1] 13 (by decide) (choices 1) [1,16] r11297 c11297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1751
  · exact u1752

def b11298 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 138 292 76 50 48 65 193 321), lower := (rows 7 138 292 76 50 48 64 128 256), losses := [] }

theorem u11298 : Upper (D 6) (R 6) [6,136,288,68,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11298
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11299 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 261, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 138 292 76 50 96 81 145 273), lower := (rows 7 138 292 76 50 96 64 128 256), losses := [] }

theorem u11299 : Upper (D 6) (R 6) [6,136,288,68,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11299
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11300 : Route 9 := (fun mask => (mask,id))

def c11300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11300 : Upper (D 6) (R 6) [6,136,288,68,65,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,65,1] 13 (by decide) (choices 1) [2,16,32] r11300 c11300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1753
  · exact u1754
  · exact u1755

def r11301 : Route 9 := (fun mask => (mask,id))

def c11301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11301 : Upper (D 6) (R 6) [6,136,288,68,65,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,65,2] 13 (by decide) (choices 1) [1,16,32] r11301 c11301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1756
  · exact u1757
  · exact u1758

def r11302 : Route 9 := (fun mask => (mask,id))

def c11302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11302 : Upper (D 6) (R 6) [6,136,288,68,65,16] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,65,16] 13 (by decide) (choices 1) [1,2,32] r11302 c11302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1759
  · exact u1760
  · exact u1761

def r11303 : Route 9 := (fun mask => (mask,id))

def c11303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11303 : Upper (D 6) (R 6) [6,136,288,68,96,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,96,1] 13 (by decide) (choices 1) [1,2,16] r11303 c11303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1762
  · exact u1763
  · exact u1764

def r11304 : Route 9 := (fun mask => (mask,id))

def c11304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11304 : Upper (D 6) (R 6) [6,136,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,96,2] 13 (by decide) (choices 1) [1,16] r11304 c11304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1765
  · exact u1766

def b11305 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 76 112 48 67 131 259), lower := (rows 7 138 292 76 112 48 64 128 256), losses := [] }

theorem u11305 : Upper (D 6) (R 6) [6,136,288,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11305
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11306 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 7 138 292 88 49 33 70 198 326), lower := (rows 7 138 292 88 49 33 64 128 256), losses := [] }

theorem u11306 : Upper (D 6) (R 6) [6,136,288,80,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11306
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11307 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 138 292 88 49 34 69 197 325), lower := (rows 7 138 292 88 49 34 64 128 256), losses := [] }

theorem u11307 : Upper (D 6) (R 6) [6,136,288,80,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11307
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11308 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 138 292 88 49 36 67 195 323), lower := (rows 7 138 292 88 49 36 64 128 256), losses := [] }

theorem u11308 : Upper (D 6) (R 6) [6,136,288,80,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11308
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11309 : PairBound 9 := { available := 7, camps := [], pairs := [(0,6),(1,5),(3,5)], upper := (rows 7 138 292 88 49 96 71 135 263), lower := (rows 7 138 292 88 49 96 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 24 16 0 65 129 257), good := (rows 455 138 260 90 475 64 64 128 256) },{ target := 6, region := (rows 9 10 20 8 16 32 0 137 265), good := (rows 391 395 292 415 437 32 0 128 256) }] }

theorem u11309 : Upper (D 6) (R 6) [6,136,288,80,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11309
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11310 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 138 292 88 50 33 69 197 325), lower := (rows 7 138 292 88 50 33 64 128 256), losses := [] }

theorem u11310 : Upper (D 6) (R 6) [6,136,288,80,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11310
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11311 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 88 50 36 65 193 321), lower := (rows 7 138 292 88 50 36 64 128 256), losses := [] }

theorem u11311 : Upper (D 6) (R 6) [6,136,288,80,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11311
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11312 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 261, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 7 138 292 88 50 96 69 133 261), lower := (rows 7 138 292 88 50 96 64 128 256), losses := [] }

theorem u11312 : Upper (D 6) (R 6) [6,136,288,80,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11312
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11313 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(3,2),(4,5)], upper := (rows 7 138 292 104 81 33 86 150 278), lower := (rows 7 138 292 104 81 33 64 128 256), losses := [] }

theorem u11313 : Upper (D 6) (R 6) [6,136,288,96,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11313
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11314 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(3,0),(4,1),(4,5)], upper := (rows 7 138 292 104 81 34 85 149 277), lower := (rows 7 138 292 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 38 170 292 104 120 34 64 128 256) }] }

theorem u11314 : Upper (D 6) (R 6) [6,136,288,96,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11314
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11315 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 104 81 36 83 147 275), lower := (rows 7 138 292 104 81 36 64 128 256), losses := [] }

theorem u11315 : Upper (D 6) (R 6) [6,136,288,96,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11315
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11316 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 104 81 48 71 135 263), lower := (rows 7 138 292 104 81 48 64 128 256), losses := [] }

theorem u11316 : Upper (D 6) (R 6) [6,136,288,96,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11316
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11317 : Route 9 := (fun mask => (mask,id))

def c11317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11317 : Upper (D 6) (R 6) [6,136,288,96,68,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,96,68,1] 13 (by decide) (choices 1) [1,2,16] r11317 c11317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1767
  · exact u1768
  · exact u1769

def r11318 : Route 9 := (fun mask => (mask,id))

def c11318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11318 : Upper (D 6) (R 6) [6,136,288,96,68,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,96,68,2] 13 (by decide) (choices 1) [1,16] r11318 c11318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1770
  · exact u1771

def b11319 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 104 84 48 67 131 259), lower := (rows 7 138 292 104 84 48 64 128 256), losses := [] }

theorem u11319 : Upper (D 6) (R 6) [6,136,288,96,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11319
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11320 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 162 292 25 88 33 70 198 326), lower := (rows 7 162 292 25 88 33 64 128 256), losses := [] }

theorem u11320 : Upper (D 6) (R 6) [6,160,288,17,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11320
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11321 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 162 292 25 88 34 69 197 325), lower := (rows 7 162 292 25 88 34 64 128 256), losses := [] }

theorem u11321 : Upper (D 6) (R 6) [6,160,288,17,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11321
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11322 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 162 292 25 88 96 71 135 263), lower := (rows 7 162 292 25 88 96 64 128 256), losses := [] }

theorem u11322 : Upper (D 6) (R 6) [6,160,288,17,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11322
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11323 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 162 292 26 81 33 76 204 332), lower := (rows 7 162 292 26 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 37 160 292 508 113 33 64 128 256) }] }

theorem u11323 : Upper (D 6) (R 6) [6,160,288,18,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11323
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11324 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 162 292 26 81 36 73 201 329), lower := (rows 7 162 292 26 81 36 64 128 256), losses := [] }

theorem u11324 : Upper (D 6) (R 6) [6,160,288,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11324
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11325 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 162 292 26 81 40 69 197 325), lower := (rows 7 162 292 26 81 40 64 128 256), losses := [] }

theorem u11325 : Upper (D 6) (R 6) [6,160,288,18,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11325
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11326 : Route 9 := (fun mask => (mask,id))

def c11326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11326 : Upper (D 6) (R 6) [6,160,288,18,65,64] 13 := by
  apply FastRouting.sound _ _ [6,160,288,18,65,64] 13 (by decide) (choices 1) [1,4,8] r11326 c11326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1772
  · exact u1773
  · exact u1774

def r11327 : Route 9 := (fun mask => (mask,id))

def c11327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11327 : Upper (D 6) (R 6) [6,160,288,18,68,1] 13 := by
  apply FastRouting.sound _ _ [6,160,288,18,68,1] 13 (by decide) (choices 1) [1,8] r11327 c11327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1775
  · exact u1776

def b11328 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 162 292 26 84 40 65 193 321), lower := (rows 7 162 292 26 84 40 64 128 256), losses := [] }

theorem u11328 : Upper (D 6) (R 6) [6,160,288,18,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11328
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11329 : Route 9 := (fun mask => (mask,id))

def c11329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11329 : Upper (D 6) (R 6) [6,160,288,18,68,64] 13 := by
  apply FastRouting.sound _ _ [6,160,288,18,68,64] 13 (by decide) (choices 1) [1,8] r11329 c11329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1777
  · exact u1778

def r11330 : Route 9 := (fun mask => (mask,id))

def c11330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11330 : Upper (D 6) (R 6) [6,160,288,65,66,1] 13 := by
  apply FastRouting.sound _ _ [6,160,288,65,66,1] 13 (by decide) (choices 1) [4,8,16] r11330 c11330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1779
  · exact u1780
  · exact u1781

def b11331 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 162 292 73 82 36 89 153 281), lower := (rows 7 162 292 73 82 36 64 128 256), losses := [] }

theorem u11331 : Upper (D 6) (R 6) [6,160,288,65,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11331
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11332 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 162 292 73 82 40 85 149 277), lower := (rows 7 162 292 73 82 40 64 128 256), losses := [] }

theorem u11332 : Upper (D 6) (R 6) [6,160,288,65,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11332
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11333 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 162 292 73 82 48 77 141 269), lower := (rows 7 162 292 73 82 48 64 128 256), losses := [] }

theorem u11333 : Upper (D 6) (R 6) [6,160,288,65,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11333
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m11334_16 : Upper (D 6) (R 6) [6,160,288,66,68,1,16] 13 :=
  permutation_upper _ _ _ [6,160,288,66,68,1,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1783

def r11334 : Route 9 := (fun mask => (mask,id))

def c11334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11334 : Upper (D 6) (R 6) [6,160,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [6,160,288,66,68,1] 13 (by decide) (choices 1) [1,8,16] r11334 c11334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1782
  · exact u1783
  · exact m11334_16

def b11335 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 162 292 74 84 40 81 145 273), lower := (rows 7 162 292 74 84 40 64 128 256), losses := [] }

theorem u11335 : Upper (D 6) (R 6) [6,160,288,66,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11335
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11336 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 162 324 25 52 33 74 202 330), lower := (rows 7 162 324 25 52 33 64 128 256), losses := [] }

theorem u11336 : Upper (D 6) (R 6) [6,160,320,17,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11336
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11337 : PairBound 9 := { available := 73, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 162 324 25 52 34 73 201 329), lower := (rows 7 162 324 25 52 34 64 128 256), losses := [] }

theorem u11337 : Upper (D 6) (R 6) [6,160,320,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11337
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11338 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 7 162 324 25 52 40 67 195 323), lower := (rows 7 162 324 25 52 40 64 128 256), losses := [] }

theorem u11338 : Upper (D 6) (R 6) [6,160,320,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11338
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11339 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 162 324 25 52 96 75 139 267), lower := (rows 7 162 324 25 52 96 64 128 256), losses := [] }

theorem u11339 : Upper (D 6) (R 6) [6,160,320,17,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11339
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11339
end Delivery.IrregularNine14.P06
