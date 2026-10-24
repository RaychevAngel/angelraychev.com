import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0044

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13260 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 200 49 36 337 401 273), lower := (rows 11 38 70 200 49 36 64 128 256), losses := [] }

theorem u13260 : Upper (D 6) (R 6) [10,36,66,192,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13261 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 200 49 48 325 389 261), lower := (rows 11 38 70 200 49 48 64 128 256), losses := [] }

theorem u13261 : Upper (D 6) (R 6) [10,36,66,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13261 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13262 : Route 9 := (fun mask => (mask,id))

def c13262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13262 : Upper (D 6) (R 6) [10,36,66,192,33,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,33,256] 13 (by decide) (choices 1) [1,4,16] r13262 c13262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2659
  · exact u2660
  · exact u2661

def r13263 : Route 9 := (fun mask => (mask,id))

def c13263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13263 : Upper (D 6) (R 6) [10,36,66,192,257,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,257,1] 13 (by decide) (choices 1) [4,16,32] r13263 c13263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2662
  · exact u2663
  · exact u2664

def b13264 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 200 273 36 113 177 305), lower := (rows 11 38 70 200 273 36 64 128 256), losses := [] }

theorem u13264 : Upper (D 6) (R 6) [10,36,66,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13265 : Route 9 := (fun mask => (mask,id))

def c13265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13265 : Upper (D 6) (R 6) [10,36,66,192,257,16] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,257,16] 13 (by decide) (choices 1) [1,4,32] r13265 c13265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2665
  · exact u2666
  · exact u2667

def r13266 : Route 9 := (fun mask => (mask,id))

def c13266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13266 : Upper (D 6) (R 6) [10,36,66,192,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,260,1] 13 (by decide) (choices 1) [1,16,32] r13266 c13266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2668
  · exact u2669
  · exact u2670

def b13267 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 200 276 48 97 161 289), lower := (rows 11 38 70 200 276 48 64 128 256), losses := [] }

theorem u13267 : Upper (D 6) (R 6) [10,36,66,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13267 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13268 : Route 9 := (fun mask => (mask,id))

def c13268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13268 : Upper (D 6) (R 6) [10,36,66,192,288,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,288,1] 13 (by decide) (choices 1) [1,4,16] r13268 c13268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2671
  · exact u2672
  · exact u2673

def b13269 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 200 304 36 81 145 273), lower := (rows 11 38 70 200 304 36 64 128 256), losses := [] }

theorem u13269 : Upper (D 6) (R 6) [10,36,66,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13270 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 70 200 304 48 69 133 261), lower := (rows 11 38 70 200 304 48 64 128 256), losses := [] }

theorem u13270 : Upper (D 6) (R 6) [10,36,66,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13270 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13271 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 488, targets := 6 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 38 70 392 21 33 112 240 368), lower := (rows 11 38 70 392 21 33 64 128 256), losses := [] }

theorem u13271 : Upper (D 6) (R 6) [10,36,66,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13272 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 392 21 48 97 225 353), lower := (rows 11 38 70 392 21 48 64 128 256), losses := [] }

theorem u13272 : Upper (D 6) (R 6) [10,36,66,384,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13272 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13273 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 392 21 96 113 177 305), lower := (rows 11 38 70 392 21 96 64 128 256), losses := [] }

theorem u13273 : Upper (D 6) (R 6) [10,36,66,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13274 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 392 49 33 84 212 340), lower := (rows 11 38 70 392 49 33 64 128 256), losses := [] }

theorem u13274 : Upper (D 6) (R 6) [10,36,66,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13275 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 392 49 36 81 209 337), lower := (rows 11 38 70 392 49 36 64 128 256), losses := [] }

theorem u13275 : Upper (D 6) (R 6) [10,36,66,384,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13276 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 392 49 48 69 197 325), lower := (rows 11 38 70 392 49 48 64 128 256), losses := [] }

theorem u13276 : Upper (D 6) (R 6) [10,36,66,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13276 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13277 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 392 49 96 85 149 277), lower := (rows 11 38 70 392 49 96 64 128 256), losses := [] }

theorem u13277 : Upper (D 6) (R 6) [10,36,66,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13278 : Route 9 := (fun mask => (mask,id))

def c13278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13278 : Upper (D 6) (R 6) [10,36,66,384,65,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384,65,1] 13 (by decide) (choices 1) [4,16,32] r13278 c13278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2674
  · exact u2675
  · exact u2676

def b13279 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 392 81 36 113 177 305), lower := (rows 11 38 70 392 81 36 64 128 256), losses := [] }

theorem u13279 : Upper (D 6) (R 6) [10,36,66,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13280 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 393, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 70 392 81 48 101 165 293), lower := (rows 11 38 70 392 81 48 64 128 256), losses := [] }

theorem u13280 : Upper (D 6) (R 6) [10,36,66,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13280 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13281 : Route 9 := (fun mask => (mask,id))

def c13281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13281 : Upper (D 6) (R 6) [10,36,66,384,96,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384,96,1] 13 (by decide) (choices 1) [1,4,16] r13281 c13281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2677
  · exact u2678
  · exact u2679

def b13282 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 392 112 36 81 145 273), lower := (rows 11 38 70 392 112 36 64 128 256), losses := [] }

theorem u13282 : Upper (D 6) (R 6) [10,36,66,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13283 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 70 392 112 48 69 133 261), lower := (rows 11 38 70 392 112 48 64 128 256), losses := [] }

theorem u13283 : Upper (D 6) (R 6) [10,36,66,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13283 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13284 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 73 146 33 356 420 292), lower := (rows 11 38 84 73 146 33 64 128 256), losses := [] }

theorem u13284 : Upper (D 6) (R 6) [10,36,80,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13285 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 73 146 36 353 417 289), lower := (rows 11 38 84 73 146 36 64 128 256), losses := [] }

theorem u13285 : Upper (D 6) (R 6) [10,36,80,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13286 : Route 9 := (fun mask => (mask,id))

def c13286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13286 : Upper (D 6) (R 6) [10,36,80,65,130,256] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65,130,256] 13 (by decide) (choices 1) [1,4,32] r13286 c13286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2680
  · exact u2681
  · exact u2682

def b13287 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 73 148 33 354 418 290), lower := (rows 11 38 84 73 148 33 64 128 256), losses := [] }

theorem u13287 : Upper (D 6) (R 6) [10,36,80,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13288 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 84 73 148 34 353 417 289), lower := (rows 11 38 84 73 148 34 64 128 256), losses := [] }

theorem u13288 : Upper (D 6) (R 6) [10,36,80,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13289 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 84 73 148 288 99 163 291), lower := (rows 11 38 84 73 148 288 64 128 256), losses := [] }

theorem u13289 : Upper (D 6) (R 6) [10,36,80,65,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13289 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13290 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 73 176 33 326 390 262), lower := (rows 11 38 84 73 176 33 64 128 256), losses := [] }

theorem u13290 : Upper (D 6) (R 6) [10,36,80,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13291 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 84 73 176 34 325 389 261), lower := (rows 11 38 84 73 176 34 64 128 256), losses := [] }

theorem u13291 : Upper (D 6) (R 6) [10,36,80,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13292 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 73 176 36 323 387 259), lower := (rows 11 38 84 73 176 36 64 128 256), losses := [] }

theorem u13292 : Upper (D 6) (R 6) [10,36,80,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13293 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 84 73 176 288 71 135 263), lower := (rows 11 38 84 73 176 288 64 128 256), losses := [] }

theorem u13293 : Upper (D 6) (R 6) [10,36,80,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13293 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13294 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 73 400 33 102 166 294), lower := (rows 11 38 84 73 400 33 64 128 256), losses := [] }

theorem u13294 : Upper (D 6) (R 6) [10,36,80,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13295 : Route 9 := (fun mask => (mask,id))

def c13295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13295 : Upper (D 6) (R 6) [10,36,80,65,384,2] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65,384,2] 13 (by decide) (choices 1) [1,4,32] r13295 c13295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2683
  · exact u2684
  · exact u2685

def b13296 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 73 400 36 99 163 291), lower := (rows 11 38 84 73 400 36 64 128 256), losses := [] }

theorem u13296 : Upper (D 6) (R 6) [10,36,80,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13297 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 328, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 84 104 145 33 326 390 262), lower := (rows 11 38 84 104 145 33 64 128 256), losses := [] }

theorem u13297 : Upper (D 6) (R 6) [10,36,80,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13298 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 84 104 145 34 325 389 261), lower := (rows 11 38 84 104 145 34 64 128 256), losses := [] }

theorem u13298 : Upper (D 6) (R 6) [10,36,80,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13299 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 104 145 36 323 387 259), lower := (rows 11 38 84 104 145 36 64 128 256), losses := [] }

theorem u13299 : Upper (D 6) (R 6) [10,36,80,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13300 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 84 104 145 288 71 135 263), lower := (rows 11 38 84 104 145 288 64 128 256), losses := [] }

theorem u13300 : Upper (D 6) (R 6) [10,36,80,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13300 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13301 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 84 104 146 33 325 389 261), lower := (rows 11 38 84 104 146 33 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 12 16 51 64 128 256), good := (rows 43 43 120 104 179 33 64 128 256) }] }

theorem u13301 : Upper (D 6) (R 6) [10,36,80,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13302 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 104 146 36 321 385 257), lower := (rows 11 38 84 104 146 36 64 128 256), losses := [] }

theorem u13302 : Upper (D 6) (R 6) [10,36,80,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13303 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 84 104 146 288 69 133 261), lower := (rows 11 38 84 104 146 288 64 128 256), losses := [] }

theorem u13303 : Upper (D 6) (R 6) [10,36,80,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13303 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13304 : Route 9 := (fun mask => (mask,id))

def c13304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13304 : Upper (D 6) (R 6) [10,36,80,96,384,1] 13 := by
  apply FastRouting.sound _ _ [10,36,80,96,384,1] 13 (by decide) (choices 1) [1,2,4] r13304 c13304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2686
  · exact u2687
  · exact u2688

def b13305 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 84 104 400 34 69 133 261), lower := (rows 11 38 84 104 400 34 64 128 256), losses := [] }

theorem u13305 : Upper (D 6) (R 6) [10,36,80,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13306 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 104 400 36 67 131 259), lower := (rows 11 38 84 104 400 36 64 128 256), losses := [] }

theorem u13306 : Upper (D 6) (R 6) [10,36,80,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13307 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 84 137 273 34 100 228 356), lower := (rows 11 38 84 137 273 34 64 128 256), losses := [] }

theorem u13307 : Upper (D 6) (R 6) [10,36,80,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13308 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 137 273 36 98 226 354), lower := (rows 11 38 84 137 273 36 64 128 256), losses := [] }

theorem u13308 : Upper (D 6) (R 6) [10,36,80,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13309 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 137 273 96 102 166 294), lower := (rows 11 38 84 137 273 96 64 128 256), losses := [] }

theorem u13309 : Upper (D 6) (R 6) [10,36,80,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13310 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 137 274 33 100 228 356), lower := (rows 11 38 84 137 274 33 64 128 256), losses := [] }

theorem u13310 : Upper (D 6) (R 6) [10,36,80,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13311 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 137 274 36 97 225 353), lower := (rows 11 38 84 137 274 36 64 128 256), losses := [] }

theorem u13311 : Upper (D 6) (R 6) [10,36,80,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13312 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 137 274 96 101 165 293), lower := (rows 11 38 84 137 274 96 64 128 256), losses := [] }

theorem u13312 : Upper (D 6) (R 6) [10,36,80,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13313 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 137 276 33 98 226 354), lower := (rows 11 38 84 137 276 33 64 128 256), losses := [] }

theorem u13313 : Upper (D 6) (R 6) [10,36,80,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13314 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 201, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 84 137 276 34 97 225 353), lower := (rows 11 38 84 137 276 34 64 128 256), losses := [] }

theorem u13314 : Upper (D 6) (R 6) [10,36,80,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13315 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 137 276 96 99 163 291), lower := (rows 11 38 84 137 276 96 64 128 256), losses := [] }

theorem u13315 : Upper (D 6) (R 6) [10,36,80,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13316 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 84 137 304 33 70 198 326), lower := (rows 11 38 84 137 304 33 64 128 256), losses := [] }

theorem u13316 : Upper (D 6) (R 6) [10,36,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13317 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 84 137 304 34 69 197 325), lower := (rows 11 38 84 137 304 34 64 128 256), losses := [] }

theorem u13317 : Upper (D 6) (R 6) [10,36,80,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13318 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 137 304 36 67 195 323), lower := (rows 11 38 84 137 304 36 64 128 256), losses := [] }

theorem u13318 : Upper (D 6) (R 6) [10,36,80,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13319 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 137 304 96 71 135 263), lower := (rows 11 38 84 137 304 96 64 128 256), losses := [] }

theorem u13319 : Upper (D 6) (R 6) [10,36,80,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13319
end Delivery.IrregularNine14.P06
