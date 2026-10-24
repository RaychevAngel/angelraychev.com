import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0027
import IrregularNine14P06C0028

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11220 : Route 9 := (fun mask => (mask,id))

def c11220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11220 : Upper (D 6) (R 6) [6,136,288,17,34,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,34,64] 13 (by decide) (choices 1) [1,4] r11220 c11220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1676
  · exact u1677

def b11221 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 138 292 25 82 33 100 228 356), lower := (rows 7 138 292 25 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 17 32 100 164 292), good := (rows 470 138 484 24 82 500 64 128 256) }] }

theorem u11221 : Upper (D 6) (R 6) [6,136,288,17,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11221
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11222 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 25 82 36 97 225 353), lower := (rows 7 138 292 25 82 36 64 128 256), losses := [] }

theorem u11222 : Upper (D 6) (R 6) [6,136,288,17,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11222
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11223 : Route 9 := (fun mask => (mask,id))

def c11223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11223 : Upper (D 6) (R 6) [6,136,288,17,66,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,66,64] 13 (by decide) (choices 1) [1,4,32] r11223 c11223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1678
  · exact u1679
  · exact u1680

def r11224 : Route 9 := (fun mask => (mask,id))

def c11224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11224 : Upper (D 6) (R 6) [6,136,288,17,68,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,68,1] 13 (by decide) (choices 1) [2,32] r11224 c11224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1681
  · exact u1682

def r11225 : Route 9 := (fun mask => (mask,id))

def c11225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11225 : Upper (D 6) (R 6) [6,136,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,68,2] 13 (by decide) (choices 1) [1,32] r11225 c11225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1683
  · exact u1684

def r11226 : Route 9 := (fun mask => (mask,id))

def c11226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11226 : Upper (D 6) (R 6) [6,136,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,68,64] 13 (by decide) (choices 1) [1,2,32] r11226 c11226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1685
  · exact u1686
  · exact u1687

def b11227 : PairBound 9 := { available := 70, camps := [], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 138 292 25 112 33 70 198 326), lower := (rows 7 138 292 25 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 48 32 65 129 257), good := (rows 454 138 308 474 116 500 64 128 256) }] }

theorem u11227 : Upper (D 6) (R 6) [6,136,288,17,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11227
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11228 : Route 9 := (fun mask => (mask,id))

def c11228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11228 : Upper (D 6) (R 6) [6,136,288,17,96,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,96,2] 13 (by decide) (choices 1) [1,4] r11228 c11228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1688
  · exact u1689

def b11229 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 25 112 36 67 195 323), lower := (rows 7 138 292 25 112 36 64 128 256), losses := [] }

theorem u11229 : Upper (D 6) (R 6) [6,136,288,17,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11229
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11230 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 292 25 112 96 71 135 263), lower := (rows 7 138 292 25 112 96 64 128 256), losses := [] }

theorem u11230 : Upper (D 6) (R 6) [6,136,288,17,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11230
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11231 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 5, region := 324, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 138 292 26 81 33 100 228 356), lower := (rows 7 138 292 26 81 33 64 128 256), losses := [] }

theorem u11231 : Upper (D 6) (R 6) [6,136,288,18,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11231
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11232 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 26 81 36 97 225 353), lower := (rows 7 138 292 26 81 36 64 128 256), losses := [] }

theorem u11232 : Upper (D 6) (R 6) [6,136,288,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11232
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11233 : Route 9 := (fun mask => (mask,id))

def c11233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11233 : Upper (D 6) (R 6) [6,136,288,18,65,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,65,64] 13 (by decide) (choices 1) [1,4,32] r11233 c11233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1690
  · exact u1691
  · exact u1692

def r11234 : Route 9 := (fun mask => (mask,id))

def c11234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11234 : Upper (D 6) (R 6) [6,136,288,18,68,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,68,1] 13 (by decide) (choices 1) [1,32] r11234 c11234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1693
  · exact u1694

def r11235 : Route 9 := (fun mask => (mask,id))

def c11235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11235 : Upper (D 6) (R 6) [6,136,288,18,68,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,68,64] 13 (by decide) (choices 1) [1,32] r11235 c11235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1695
  · exact u1696

def r11236 : Route 9 := (fun mask => (mask,id))

def c11236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11236 : Upper (D 6) (R 6) [6,136,288,18,96,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,96,1] 13 (by decide) (choices 1) [1,4] r11236 c11236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1697
  · exact u1698

def b11237 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 26 112 36 65 193 321), lower := (rows 7 138 292 26 112 36 64 128 256), losses := [] }

theorem u11237 : Upper (D 6) (R 6) [6,136,288,18,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11237
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11238 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 292 26 112 96 69 133 261), lower := (rows 7 138 292 26 112 96 64 128 256), losses := [] }

theorem u11238 : Upper (D 6) (R 6) [6,136,288,18,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11238
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11239 : Route 9 := (fun mask => (mask,id))

def c11239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11239 : Upper (D 6) (R 6) [6,136,288,20,65,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,65,1] 13 (by decide) (choices 1) [2,32] r11239 c11239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1699
  · exact u1700

def r11240 : Route 9 := (fun mask => (mask,id))

def c11240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11240 : Upper (D 6) (R 6) [6,136,288,20,65,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,65,2] 13 (by decide) (choices 1) [1,32] r11240 c11240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1701
  · exact u1702

def r11241 : Route 9 := (fun mask => (mask,id))

def c11241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11241 : Upper (D 6) (R 6) [6,136,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,65,64] 13 (by decide) (choices 1) [1,2,32] r11241 c11241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1703
  · exact u1704
  · exact u1705

def r11242 : Route 9 := (fun mask => (mask,id))

def c11242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11242 : Upper (D 6) (R 6) [6,136,288,20,66,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,66,1] 13 (by decide) (choices 1) [1,32] r11242 c11242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1706
  · exact u1707

def r11243 : Route 9 := (fun mask => (mask,id))

def c11243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11243 : Upper (D 6) (R 6) [6,136,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,66,64] 13 (by decide) (choices 1) [1,32] r11243 c11243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1708
  · exact u1709

def b11244 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 138 292 41 81 34 84 212 340), lower := (rows 7 138 292 41 81 34 64 128 256), losses := [] }

theorem u11244 : Upper (D 6) (R 6) [6,136,288,33,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11244
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11245 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 138 292 41 81 36 82 210 338), lower := (rows 7 138 292 41 81 36 64 128 256), losses := [] }

theorem u11245 : Upper (D 6) (R 6) [6,136,288,33,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11245
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11246 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 138 292 41 81 48 70 198 326), lower := (rows 7 138 292 41 81 48 64 128 256), losses := [] }

theorem u11246 : Upper (D 6) (R 6) [6,136,288,33,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11246
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11247 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(3,2),(4,5)], upper := (rows 7 138 292 41 81 96 86 150 278), lower := (rows 7 138 292 41 81 96 64 128 256), losses := [] }

theorem u11247 : Upper (D 6) (R 6) [6,136,288,33,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11247
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11248 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 138 292 41 82 33 84 212 340), lower := (rows 7 138 292 41 82 33 64 128 256), losses := [] }

theorem u11248 : Upper (D 6) (R 6) [6,136,288,33,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11248
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11249 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 138 292 41 82 36 81 209 337), lower := (rows 7 138 292 41 82 36 64 128 256), losses := [] }

theorem u11249 : Upper (D 6) (R 6) [6,136,288,33,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11249
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11250 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 80, targets := 32 },{ cop := 3, region := 324, targets := 2 }], pairs := [(2,1),(4,5)], upper := (rows 7 138 292 41 82 48 69 197 325), lower := (rows 7 138 292 41 82 48 64 128 256), losses := [] }

theorem u11250 : Upper (D 6) (R 6) [6,136,288,33,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11250
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11251 : Route 9 := (fun mask => (mask,id))

def c11251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11251 : Upper (D 6) (R 6) [6,136,288,33,66,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,33,66,64] 13 (by decide) (choices 1) [1,4,16] r11251 c11251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1710
  · exact u1711
  · exact u1712

def b11252 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 138 292 41 84 33 82 210 338), lower := (rows 7 138 292 41 84 33 64 128 256), losses := [] }

theorem u11252 : Upper (D 6) (R 6) [6,136,288,33,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11252
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11253 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 138 292 41 84 34 81 209 337), lower := (rows 7 138 292 41 84 34 64 128 256), losses := [] }

theorem u11253 : Upper (D 6) (R 6) [6,136,288,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11253
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11254 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 138 292 41 84 48 67 195 323), lower := (rows 7 138 292 41 84 48 64 128 256), losses := [] }

theorem u11254 : Upper (D 6) (R 6) [6,136,288,33,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11254
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11255 : Route 9 := (fun mask => (mask,id))

def c11255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11255 : Upper (D 6) (R 6) [6,136,288,33,68,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,33,68,64] 13 (by decide) (choices 1) [1,2,16] r11255 c11255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1713
  · exact u1714
  · exact u1715

def b11256 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 138 292 56 81 33 70 198 326), lower := (rows 7 138 292 56 81 33 64 128 256), losses := [] }

theorem u11256 : Upper (D 6) (R 6) [6,136,288,48,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11256
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11257 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(3,0),(4,1),(4,5)], upper := (rows 7 138 292 56 81 34 69 197 325), lower := (rows 7 138 292 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 38 170 292 56 120 34 64 128 256) }] }

theorem u11257 : Upper (D 6) (R 6) [6,136,288,48,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11257
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11258 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 56 81 36 67 195 323), lower := (rows 7 138 292 56 81 36 64 128 256), losses := [] }

theorem u11258 : Upper (D 6) (R 6) [6,136,288,48,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11258
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11259 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 292 56 81 96 71 135 263), lower := (rows 7 138 292 56 81 96 64 128 256), losses := [] }

theorem u11259 : Upper (D 6) (R 6) [6,136,288,48,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11259
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11260 : Route 9 := (fun mask => (mask,id))

def c11260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11260 : Upper (D 6) (R 6) [6,136,288,48,66,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48,66,1] 13 (by decide) (choices 1) [1,4] r11260 c11260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1716
  · exact u1717

def b11261 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 56 82 36 65 193 321), lower := (rows 7 138 292 56 82 36 64 128 256), losses := [] }

theorem u11261 : Upper (D 6) (R 6) [6,136,288,48,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11261
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11262 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 292 56 82 96 69 133 261), lower := (rows 7 138 292 56 82 96 64 128 256), losses := [] }

theorem u11262 : Upper (D 6) (R 6) [6,136,288,48,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11262
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11263 : Route 9 := (fun mask => (mask,id))

def c11263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11263 : Upper (D 6) (R 6) [6,136,288,48,68,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48,68,1] 13 (by decide) (choices 1) [1,2] r11263 c11263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1718
  · exact u1719

def r11264 : Route 9 := (fun mask => (mask,id))

def c11264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11264 : Upper (D 6) (R 6) [6,136,288,48,68,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48,68,2] 13 (by decide) (choices 1) [1] r11264 c11264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u1720

def b11265 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 292 56 84 96 67 131 259), lower := (rows 7 138 292 56 84 96 64 128 256), losses := [] }

theorem u11265 : Upper (D 6) (R 6) [6,136,288,48,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11265
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11266 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 138 292 73 49 34 84 212 340), lower := (rows 7 138 292 73 49 34 64 128 256), losses := [] }

theorem u11266 : Upper (D 6) (R 6) [6,136,288,65,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11266
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11267 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 138 292 73 49 36 82 210 338), lower := (rows 7 138 292 73 49 36 64 128 256), losses := [] }

theorem u11267 : Upper (D 6) (R 6) [6,136,288,65,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11267
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11268 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 138 292 73 49 48 70 198 326), lower := (rows 7 138 292 73 49 48 64 128 256), losses := [] }

theorem u11268 : Upper (D 6) (R 6) [6,136,288,65,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11268
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11269 : Route 9 := (fun mask => (mask,id))

def c11269 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11269 : Upper (D 6) (R 6) [6,136,288,65,33,64] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,33,64] 13 (by decide) (choices 1) [2,4,16] r11269 c11269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1721
  · exact u1722
  · exact u1723

def b11270 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 7 138 292 73 50 33 84 212 340), lower := (rows 7 138 292 73 50 33 64 128 256), losses := [] }

theorem u11270 : Upper (D 6) (R 6) [6,136,288,65,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11270
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11271 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 73 50 36 81 209 337), lower := (rows 7 138 292 73 50 36 64 128 256), losses := [] }

theorem u11271 : Upper (D 6) (R 6) [6,136,288,65,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11271
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11272 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 138 292 73 50 48 69 197 325), lower := (rows 7 138 292 73 50 48 64 128 256), losses := [] }

theorem u11272 : Upper (D 6) (R 6) [6,136,288,65,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11272
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11273 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 261, targets := 64 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 138 292 73 50 96 85 149 277), lower := (rows 7 138 292 73 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 104 64 128 256), good := (rows 22 186 292 104 50 96 96 128 256) }] }

theorem u11273 : Upper (D 6) (R 6) [6,136,288,65,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11273
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11274 : Route 9 := (fun mask => (mask,id))

def c11274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11274 : Upper (D 6) (R 6) [6,136,288,65,66,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,66,1] 13 (by decide) (choices 1) [4,16,32] r11274 c11274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1724
  · exact u1725
  · exact u1726

def b11275 : PairBound 9 := { available := 49, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 73 82 36 113 177 305), lower := (rows 7 138 292 73 82 36 64 128 256), losses := [] }

theorem u11275 : Upper (D 6) (R 6) [6,136,288,65,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11275
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11276 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 138 292 73 82 48 101 165 293), lower := (rows 7 138 292 73 82 48 64 128 256), losses := [] }

theorem u11276 : Upper (D 6) (R 6) [6,136,288,65,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11276
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11277 : Route 9 := (fun mask => (mask,id))

def c11277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11277 : Upper (D 6) (R 6) [6,136,288,65,68,1] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,68,1] 13 (by decide) (choices 1) [2,16,32] r11277 c11277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1727
  · exact u1728
  · exact u1729

def r11278 : Route 9 := (fun mask => (mask,id))

def c11278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11278 : Upper (D 6) (R 6) [6,136,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,68,2] 13 (by decide) (choices 1) [1,16,32] r11278 c11278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1730
  · exact u1731
  · exact u1732

def r11279 : Route 9 := (fun mask => (mask,id))

def c11279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11279 : Upper (D 6) (R 6) [6,136,288,65,68,16] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,68,16] 13 (by decide) (choices 1) [1,2,32] r11279 c11279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1733
  · exact u1734
  · exact u1735

#print axioms u11279
end Delivery.IrregularNine14.P06
