import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0044
import IrregularNine14P06C0045

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13320 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 84 140 273 33 98 226 354), lower := (rows 11 38 84 140 273 33 64 128 256), losses := [] }

theorem u13320 : Upper (D 6) (R 6) [10,36,80,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13321 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 84 140 273 34 97 225 353), lower := (rows 11 38 84 140 273 34 64 128 256), losses := [] }

theorem u13321 : Upper (D 6) (R 6) [10,36,80,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13322 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 140 273 96 99 163 291), lower := (rows 11 38 84 140 273 96 64 128 256), losses := [] }

theorem u13322 : Upper (D 6) (R 6) [10,36,80,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13323 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 84 140 274 33 97 225 353), lower := (rows 11 38 84 140 274 33 64 128 256), losses := [] }

theorem u13323 : Upper (D 6) (R 6) [10,36,80,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13324 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 140 274 96 97 161 289), lower := (rows 11 38 84 140 274 96 64 128 256), losses := [] }

theorem u13324 : Upper (D 6) (R 6) [10,36,80,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13325 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 200, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 84 168 273 33 70 198 326), lower := (rows 11 38 84 168 273 33 64 128 256), losses := [] }

theorem u13325 : Upper (D 6) (R 6) [10,36,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13326 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 84 168 273 34 69 197 325), lower := (rows 11 38 84 168 273 34 64 128 256), losses := [] }

theorem u13326 : Upper (D 6) (R 6) [10,36,80,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13327 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 168 273 36 67 195 323), lower := (rows 11 38 84 168 273 36 64 128 256), losses := [] }

theorem u13327 : Upper (D 6) (R 6) [10,36,80,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13328 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 168 273 96 71 135 263), lower := (rows 11 38 84 168 273 96 64 128 256), losses := [] }

theorem u13328 : Upper (D 6) (R 6) [10,36,80,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13329 : Route 9 := (fun mask => (mask,id))

def c13329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13329 : Upper (D 6) (R 6) [10,36,80,160,258,1] 13 := by
  apply FastRouting.sound _ _ [10,36,80,160,258,1] 13 (by decide) (choices 1) [1,4] r13329 c13329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2689
  · exact u2690

def b13330 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 168 274 36 65 193 321), lower := (rows 11 38 84 168 274 36 64 128 256), losses := [] }

theorem u13330 : Upper (D 6) (R 6) [10,36,80,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13331 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 168 274 96 69 133 261), lower := (rows 11 38 84 168 274 96 64 128 256), losses := [] }

theorem u13331 : Upper (D 6) (R 6) [10,36,80,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13332 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 84 200 49 33 326 390 262), lower := (rows 11 38 84 200 49 33 64 128 256), losses := [] }

theorem u13332 : Upper (D 6) (R 6) [10,36,80,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13333 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 84 200 49 34 325 389 261), lower := (rows 11 38 84 200 49 34 64 128 256), losses := [] }

theorem u13333 : Upper (D 6) (R 6) [10,36,80,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13334 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 200 49 36 323 387 259), lower := (rows 11 38 84 200 49 36 64 128 256), losses := [] }

theorem u13334 : Upper (D 6) (R 6) [10,36,80,192,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13335 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 201, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 84 200 49 288 71 135 263), lower := (rows 11 38 84 200 49 288 64 128 256), losses := [] }

theorem u13335 : Upper (D 6) (R 6) [10,36,80,192,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13335 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13336 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 200, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 38 84 200 273 33 102 166 294), lower := (rows 11 38 84 200 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 17 49 0 134 262), good := (rows 443 422 438 136 305 49 0 128 256) }] }

theorem u13336 : Upper (D 6) (R 6) [10,36,80,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13337 : Route 9 := (fun mask => (mask,id))

def c13337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13337 : Upper (D 6) (R 6) [10,36,80,192,257,2] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,257,2] 13 (by decide) (choices 1) [1,4,32] r13337 c13337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2691
  · exact u2692
  · exact u2693

def b13338 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 200 273 36 99 163 291), lower := (rows 11 38 84 200 273 36 64 128 256), losses := [] }

theorem u13338 : Upper (D 6) (R 6) [10,36,80,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13339 : Route 9 := (fun mask => (mask,id))

def c13339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13339 : Upper (D 6) (R 6) [10,36,80,192,258,1] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,258,1] 13 (by decide) (choices 1) [1,4,32] r13339 c13339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2694
  · exact u2695
  · exact u2696

def b13340 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 200 274 36 97 161 289), lower := (rows 11 38 84 200 274 36 64 128 256), losses := [] }

theorem u13340 : Upper (D 6) (R 6) [10,36,80,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13341 : Route 9 := (fun mask => (mask,id))

def c13341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13341 : Upper (D 6) (R 6) [10,36,80,192,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,260,1] 13 (by decide) (choices 1) [1,2,32] r13341 c13341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2697
  · exact u2698
  · exact u2699

def b13342 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 201, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 84 200 276 34 97 161 289), lower := (rows 11 38 84 200 276 34 64 128 256), losses := [] }

theorem u13342 : Upper (D 6) (R 6) [10,36,80,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13343 : Route 9 := (fun mask => (mask,id))

def c13343 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13343 : Upper (D 6) (R 6) [10,36,80,192,288,1] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,288,1] 13 (by decide) (choices 1) [1,2,4] r13343 c13343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2700
  · exact u2701
  · exact u2702

def b13344 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 84 200 304 34 69 133 261), lower := (rows 11 38 84 200 304 34 64 128 256), losses := [] }

theorem u13344 : Upper (D 6) (R 6) [10,36,80,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13345 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 200 304 36 67 131 259), lower := (rows 11 38 84 200 304 36 64 128 256), losses := [] }

theorem u13345 : Upper (D 6) (R 6) [10,36,80,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13346 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 457, targets := 4 },{ cop := 1, region := 456, targets := 1 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 38 84 392 21 33 98 226 354), lower := (rows 11 38 84 392 21 33 64 128 256), losses := [] }

theorem u13346 : Upper (D 6) (R 6) [10,36,80,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13347 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 457, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 84 392 21 34 97 225 353), lower := (rows 11 38 84 392 21 34 64 128 256), losses := [] }

theorem u13347 : Upper (D 6) (R 6) [10,36,80,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13348 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 392 21 96 99 163 291), lower := (rows 11 38 84 392 21 96 64 128 256), losses := [] }

theorem u13348 : Upper (D 6) (R 6) [10,36,80,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13349 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 84 392 49 33 70 198 326), lower := (rows 11 38 84 392 49 33 64 128 256), losses := [] }

theorem u13349 : Upper (D 6) (R 6) [10,36,80,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13350 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 84 392 49 34 69 197 325), lower := (rows 11 38 84 392 49 34 64 128 256), losses := [] }

theorem u13350 : Upper (D 6) (R 6) [10,36,80,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13351 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 84 392 49 36 67 195 323), lower := (rows 11 38 84 392 49 36 64 128 256), losses := [] }

theorem u13351 : Upper (D 6) (R 6) [10,36,80,384,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13352 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 84 392 49 96 71 135 263), lower := (rows 11 38 84 392 49 96 64 128 256), losses := [] }

theorem u13352 : Upper (D 6) (R 6) [10,36,80,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13353 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 133 25 84 34 352 480 352), lower := (rows 11 38 133 25 84 34 64 128 256), losses := [] }

theorem u13353 : Upper (D 6) (R 6) [10,36,129,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13354 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 38 133 25 84 96 354 418 290), lower := (rows 11 38 133 25 84 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 32 0 130 258), good := (rows 399 422 133 29 20 32 0 128 256) }] }

theorem u13354 : Upper (D 6) (R 6) [10,36,129,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13355 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 25 84 288 98 226 354), lower := (rows 11 38 133 25 84 288 64 128 256), losses := [] }

theorem u13355 : Upper (D 6) (R 6) [10,36,129,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13355 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13356 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 133 25 276 34 96 224 352), lower := (rows 11 38 133 25 276 34 64 128 256), losses := [] }

theorem u13356 : Upper (D 6) (R 6) [10,36,129,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13357 : Route 9 := (fun mask => (mask,id))

def c13357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13357 : Upper (D 6) (R 6) [10,36,129,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,17,260,64] 13 (by decide) (choices 1) [2,32] r13357 c13357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2703
  · exact u2704

def b13358 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 25 336 34 100 228 356), lower := (rows 11 38 133 25 336 34 64 128 256), losses := [] }

theorem u13358 : Upper (D 6) (R 6) [10,36,129,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13359 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 25 336 36 98 226 354), lower := (rows 11 38 133 25 336 36 64 128 256), losses := [] }

theorem u13359 : Upper (D 6) (R 6) [10,36,129,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13360 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 38 133 25 336 96 102 166 294), lower := (rows 11 38 133 25 336 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 32 0 130 258), good := (rows 399 422 133 29 272 32 0 128 256) }] }

theorem u13360 : Upper (D 6) (R 6) [10,36,129,17,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13361 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 133 28 81 34 352 480 352), lower := (rows 11 38 133 28 81 34 64 128 256), losses := [] }

theorem u13361 : Upper (D 6) (R 6) [10,36,129,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13362 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(2,6),(4,2)], upper := (rows 11 38 133 28 81 96 354 418 290), lower := (rows 11 38 133 28 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 24 16 32 0 130 258), good := (rows 399 422 133 28 29 32 0 128 256) }] }

theorem u13362 : Upper (D 6) (R 6) [10,36,129,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13363 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 11 38 133 28 81 288 98 226 354), lower := (rows 11 38 133 28 81 288 64 128 256), losses := [] }

theorem u13363 : Upper (D 6) (R 6) [10,36,129,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13363 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13364 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 28 82 33 352 480 352), lower := (rows 11 38 133 28 82 33 64 128 256), losses := [] }

theorem u13364 : Upper (D 6) (R 6) [10,36,129,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13365 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 11 38 133 28 82 96 353 417 289), lower := (rows 11 38 133 28 82 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 112 64 128 256), good := (rows 10 38 132 62 114 96 96 128 256) }] }

theorem u13365 : Upper (D 6) (R 6) [10,36,129,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13366 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(4,2)], upper := (rows 11 38 133 28 82 288 97 225 353), lower := (rows 11 38 133 28 82 288 64 128 256), losses := [] }

theorem u13366 : Upper (D 6) (R 6) [10,36,129,20,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13366 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13367 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 28 112 33 322 450 322), lower := (rows 11 38 133 28 112 33 64 128 256), losses := [] }

theorem u13367 : Upper (D 6) (R 6) [10,36,129,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13368 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 133 28 112 34 321 449 321), lower := (rows 11 38 133 28 112 34 64 128 256), losses := [] }

theorem u13368 : Upper (D 6) (R 6) [10,36,129,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13369 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 28 112 96 323 387 259), lower := (rows 11 38 133 28 112 96 64 128 256), losses := [] }

theorem u13369 : Upper (D 6) (R 6) [10,36,129,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13370 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,2)], upper := (rows 11 38 133 28 112 288 67 195 323), lower := (rows 11 38 133 28 112 288 64 128 256), losses := [] }

theorem u13370 : Upper (D 6) (R 6) [10,36,129,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13370 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13371 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 133 28 273 34 96 224 352), lower := (rows 11 38 133 28 273 34 64 128 256), losses := [] }

theorem u13371 : Upper (D 6) (R 6) [10,36,129,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13372 : Route 9 := (fun mask => (mask,id))

def c13372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13372 : Upper (D 6) (R 6) [10,36,129,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,257,64] 13 (by decide) (choices 1) [2,32] r13372 c13372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2705
  · exact u2706

def b13373 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 28 274 33 96 224 352), lower := (rows 11 38 133 28 274 33 64 128 256), losses := [] }

theorem u13373 : Upper (D 6) (R 6) [10,36,129,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13374 : Route 9 := (fun mask => (mask,id))

def c13374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13374 : Upper (D 6) (R 6) [10,36,129,20,258,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,258,64] 13 (by decide) (choices 1) [1,32] r13374 c13374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2707
  · exact u2708

def b13375 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 28 304 33 66 194 322), lower := (rows 11 38 133 28 304 33 64 128 256), losses := [] }

theorem u13375 : Upper (D 6) (R 6) [10,36,129,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13376 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 133 28 304 34 65 193 321), lower := (rows 11 38 133 28 304 34 64 128 256), losses := [] }

theorem u13376 : Upper (D 6) (R 6) [10,36,129,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13377 : Route 9 := (fun mask => (mask,id))

def c13377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13377 : Upper (D 6) (R 6) [10,36,129,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,288,64] 13 (by decide) (choices 1) [1,2] r13377 c13377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2709
  · exact u2710

def b13378 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 28 336 33 98 226 354), lower := (rows 11 38 133 28 336 33 64 128 256), losses := [] }

theorem u13378 : Upper (D 6) (R 6) [10,36,129,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13379 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 28 336 34 97 225 353), lower := (rows 11 38 133 28 336 34 64 128 256), losses := [] }

theorem u13379 : Upper (D 6) (R 6) [10,36,129,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13379
end Delivery.IrregularNine14.P06
