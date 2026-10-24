import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0028
import IrregularNine14P08C0029

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8280 : Route 9 := (fun mask => (mask,id))

def c8280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8280 : Upper (D 8) (R 8) [34,5,264,96,192] 13 := by
  apply FastRouting.sound _ _ [34,5,264,96,192] 13 (by decide) (choices 1) [1,16,128] r8280 c8280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1708
  · exact u1709
  · exact u1710

def b8281 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 200 49 240 240 240 496), lower := (rows 35 7 268 200 49 32 64 128 256), losses := [] }

theorem u8281 : Upper (D 8) (R 8) [34,5,264,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8282 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 200 81 176 240 176 432), lower := (rows 35 7 268 200 81 32 64 128 256), losses := [] }

theorem u8282 : Upper (D 8) (R 8) [34,5,264,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8283 : Route 9 := (fun mask => (mask,id))

def c8283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8283 : Upper (D 8) (R 8) [34,5,264,192,96] 13 := by
  apply FastRouting.sound _ _ [34,5,264,192,96] 13 (by decide) (choices 1) [1,16,128] r8283 c8283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1711
  · exact u1712
  · exact u1713

def b8284 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 268 200 208 49 113 177 305), lower := (rows 35 7 268 200 208 32 64 128 256), losses := [] }

theorem u8284 : Upper (D 8) (R 8) [34,5,264,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8285 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 25 56 224 224 224 480), lower := (rows 35 7 324 25 56 32 64 128 256), losses := [] }

theorem u8285 : Upper (D 8) (R 8) [34,5,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8286 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 25 88 160 224 160 416), lower := (rows 35 7 324 25 88 32 64 128 256), losses := [] }

theorem u8286 : Upper (D 8) (R 8) [34,5,320,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8287 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 25 112 168 232 168 424), lower := (rows 35 7 324 25 112 32 64 128 256), losses := [] }

theorem u8287 : Upper (D 8) (R 8) [34,5,320,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8288 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 25 152 224 224 224 480), lower := (rows 35 7 324 25 152 32 64 128 256), losses := [] }

theorem u8288 : Upper (D 8) (R 8) [34,5,320,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8289 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 25 176 232 232 232 488), lower := (rows 35 7 324 25 176 32 64 128 256), losses := [] }

theorem u8289 : Upper (D 8) (R 8) [34,5,320,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8290 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 25 208 168 232 168 424), lower := (rows 35 7 324 25 208 32 64 128 256), losses := [] }

theorem u8290 : Upper (D 8) (R 8) [34,5,320,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8291 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 56 240 208 208 464), lower := (rows 35 7 324 41 56 32 64 128 256), losses := [] }

theorem u8291 : Upper (D 8) (R 8) [34,5,320,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8292 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 88 176 240 176 432), lower := (rows 35 7 324 41 88 32 64 128 256), losses := [] }

theorem u8292 : Upper (D 8) (R 8) [34,5,320,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8293 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 112 184 216 152 408), lower := (rows 35 7 324 41 112 32 64 128 256), losses := [] }

theorem u8293 : Upper (D 8) (R 8) [34,5,320,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8294 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 152 240 240 240 496), lower := (rows 35 7 324 41 152 32 64 128 256), losses := [] }

theorem u8294 : Upper (D 8) (R 8) [34,5,320,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8295 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 176 248 216 216 472), lower := (rows 35 7 324 41 176 32 64 128 256), losses := [] }

theorem u8295 : Upper (D 8) (R 8) [34,5,320,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8296 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 208 184 248 184 440), lower := (rows 35 7 324 41 208 32 64 128 256), losses := [] }

theorem u8296 : Upper (D 8) (R 8) [34,5,320,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8297 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 56 56 225 193 193 449), lower := (rows 35 7 324 56 56 32 64 128 256), losses := [] }

theorem u8297 : Upper (D 8) (R 8) [34,5,320,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8298 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 56 81 168 232 168 424), lower := (rows 35 7 324 56 81 32 64 128 256), losses := [] }

theorem u8298 : Upper (D 8) (R 8) [34,5,320,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8299 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 56 88 161 225 161 417), lower := (rows 35 7 324 56 88 32 64 128 256), losses := [] }

theorem u8299 : Upper (D 8) (R 8) [34,5,320,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8300 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 56 112 169 201 137 393), lower := (rows 35 7 324 56 112 32 64 128 256), losses := [] }

theorem u8300 : Upper (D 8) (R 8) [34,5,320,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8301 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 56 145 232 232 232 488), lower := (rows 35 7 324 56 145 32 64 128 256), losses := [] }

theorem u8301 : Upper (D 8) (R 8) [34,5,320,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8302 : Route 9 := (fun mask => (mask,id))

def c8302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8302 : Upper (D 8) (R 8) [34,5,320,48,136] 13 := by
  apply FastRouting.sound _ _ [34,5,320,48,136] 13 (by decide) (choices 1) [1,64,128] r8302 c8302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1714
  · exact u1715
  · exact u1716

def b8303 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 56 176 233 201 201 457), lower := (rows 35 7 324 56 176 32 64 128 256), losses := [] }

theorem u8303 : Upper (D 8) (R 8) [34,5,320,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8304 : Route 9 := (fun mask => (mask,id))

def c8304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8304 : Upper (D 8) (R 8) [34,5,320,48,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,48,192] 13 (by decide) (choices 1) [1,8,128] r8304 c8304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1717
  · exact u1718
  · exact u1719

def b8305 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 73 152 176 240 176 432), lower := (rows 35 7 324 73 152 32 64 128 256), losses := [] }

theorem u8305 : Upper (D 8) (R 8) [34,5,320,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8306 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 73 176 184 248 184 440), lower := (rows 35 7 324 73 176 32 64 128 256), losses := [] }

theorem u8306 : Upper (D 8) (R 8) [34,5,320,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8307 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 88 145 168 232 168 424), lower := (rows 35 7 324 88 145 32 64 128 256), losses := [] }

theorem u8307 : Upper (D 8) (R 8) [34,5,320,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8308 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 88 152 161 225 161 417), lower := (rows 35 7 324 88 152 32 64 128 256), losses := [] }

theorem u8308 : Upper (D 8) (R 8) [34,5,320,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8309 : Route 9 := (fun mask => (mask,id))

def c8309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8309 : Upper (D 8) (R 8) [34,5,320,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,320,80,160] 13 (by decide) (choices 1) [1,8,128] r8309 c8309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1720
  · exact u1721
  · exact u1722

def b8310 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 104 145 184 248 184 440), lower := (rows 35 7 324 104 145 32 64 128 256), losses := [] }

theorem u8310 : Upper (D 8) (R 8) [34,5,320,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8311 : Route 9 := (fun mask => (mask,id))

def c8311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8311 : Upper (D 8) (R 8) [34,5,320,96,136] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,136] 13 (by decide) (choices 1) [1,16,128] r8311 c8311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1723
  · exact u1724
  · exact u1725

def r8312 : Route 9 := (fun mask => (mask,id))

def c8312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8312 : Upper (D 8) (R 8) [34,5,320,96,160] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,160] 13 (by decide) (choices 1) [1,8,16,128] r8312 c8312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1726
  · exact u1727
  · exact u1728
  · exact u1729

def b8313 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 137 152 112 112 240 368), lower := (rows 35 7 324 137 152 32 64 128 256), losses := [] }

theorem u8313 : Upper (D 8) (R 8) [34,5,320,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8314 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 137 176 120 120 248 376), lower := (rows 35 7 324 137 176 32 64 128 256), losses := [] }

theorem u8314 : Upper (D 8) (R 8) [34,5,320,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8315 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 137 208 56 120 184 312), lower := (rows 35 7 324 137 208 32 64 128 256), losses := [] }

theorem u8315 : Upper (D 8) (R 8) [34,5,320,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8316 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 152 152 97 97 225 353), lower := (rows 35 7 324 152 152 32 64 128 256), losses := [] }

theorem u8316 : Upper (D 8) (R 8) [34,5,320,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8317 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 152 176 105 105 233 361), lower := (rows 35 7 324 152 176 32 64 128 256), losses := [] }

theorem u8317 : Upper (D 8) (R 8) [34,5,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8318 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 152 208 41 105 169 297), lower := (rows 35 7 324 152 208 32 64 128 256), losses := [] }

theorem u8318 : Upper (D 8) (R 8) [34,5,320,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8319 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 324 168 176 121 89 217 345), lower := (rows 35 7 324 168 176 32 64 128 256), losses := [] }

theorem u8319 : Upper (D 8) (R 8) [34,5,320,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8320 : Route 9 := (fun mask => (mask,id))

def c8320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8320 : Upper (D 8) (R 8) [34,5,320,160,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,160,192] 13 (by decide) (choices 1) [1,8,16] r8320 c8320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1730
  · exact u1731
  · exact u1732

def b8321 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 104 49 480 448 448 448), lower := (rows 35 14 21 104 49 32 64 128 256), losses := [] }

theorem u8321 : Upper (D 8) (R 8) [34,12,17,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8322 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 104 81 416 480 416 416), lower := (rows 35 14 21 104 81 32 64 128 256), losses := [] }

theorem u8322 : Upper (D 8) (R 8) [34,12,17,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8323 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 104 112 417 449 385 385), lower := (rows 35 14 21 104 112 32 64 128 256), losses := [] }

theorem u8323 : Upper (D 8) (R 8) [34,12,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8324 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 104 145 480 480 480 480), lower := (rows 35 14 21 104 145 32 64 128 256), losses := [] }

theorem u8324 : Upper (D 8) (R 8) [34,12,17,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8325 : Route 9 := (fun mask => (mask,id))

def c8325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8325 : Upper (D 8) (R 8) [34,12,17,96,160] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,160] 13 (by decide) (choices 1) [1,64,128,256] r8325 c8325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1733
  · exact u1734
  · exact u1735
  · exact u1736

def b8326 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 104 208 417 481 417 417), lower := (rows 35 14 21 104 208 32 64 128 256), losses := [] }

theorem u8326 : Upper (D 8) (R 8) [34,12,17,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8327 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 104 273 224 224 224 480), lower := (rows 35 14 21 104 273 32 64 128 256), losses := [] }

theorem u8327 : Upper (D 8) (R 8) [34,12,17,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8328 : Route 9 := (fun mask => (mask,id))

def c8328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8328 : Upper (D 8) (R 8) [34,12,17,96,288] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,288] 13 (by decide) (choices 1) [1,64,128] r8328 c8328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1737
  · exact u1738
  · exact u1739

def b8329 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 104 336 161 225 161 417), lower := (rows 35 14 21 104 336 32 64 128 256), losses := [] }

theorem u8329 : Upper (D 8) (R 8) [34,12,17,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8330 : Route 9 := (fun mask => (mask,id))

def c8330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8330 : Upper (D 8) (R 8) [34,12,17,96,384] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,384] 13 (by decide) (choices 1) [1,64,128] r8330 c8330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1740
  · exact u1741
  · exact u1742

def b8331 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 200 49 480 480 480 480), lower := (rows 35 14 21 200 49 32 64 128 256), losses := [] }

theorem u8331 : Upper (D 8) (R 8) [34,12,17,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8332 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 490, targets := 1 }], pairs := [(1,0)], upper := (rows 35 14 21 200 81 416 480 416 416), lower := (rows 35 14 21 200 81 32 64 128 256), losses := [] }

theorem u8332 : Upper (D 8) (R 8) [34,12,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8333 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 200 112 417 481 417 417), lower := (rows 35 14 21 200 112 32 64 128 256), losses := [] }

theorem u8333 : Upper (D 8) (R 8) [34,12,17,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8334 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 21 200 208 289 353 417 289), lower := (rows 35 14 21 200 208 32 64 128 256), losses := [] }

theorem u8334 : Upper (D 8) (R 8) [34,12,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8335 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 200 273 224 224 224 480), lower := (rows 35 14 21 200 273 32 64 128 256), losses := [] }

theorem u8335 : Upper (D 8) (R 8) [34,12,17,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8336 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8336 : Upper (D 8) (R 8) [34,12,17,192,288] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,288] 13 (by decide) (choices 1) [1,64] r8336 c8336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1743
  · exact u1744

def b8337 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 200 336 161 225 161 417), lower := (rows 35 14 21 200 336 32 64 128 256), losses := [] }

theorem u8337 : Upper (D 8) (R 8) [34,12,17,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8338 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 296 49 224 192 192 448), lower := (rows 35 14 21 296 49 32 64 128 256), losses := [] }

theorem u8338 : Upper (D 8) (R 8) [34,12,17,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8339 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 296 81 224 224 224 480), lower := (rows 35 14 21 296 81 32 64 128 256), losses := [] }

theorem u8339 : Upper (D 8) (R 8) [34,12,17,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8339
end Delivery.IrregularNine14.P08
