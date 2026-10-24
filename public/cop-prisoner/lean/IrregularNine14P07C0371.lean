import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0112

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22260 : Route 9 := (fun mask => (mask,id))

def c22260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22260 : Upper (D 7) (R 7) [36,40,65,192,258,16] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,258,16] 13 (by decide) (choices 1) [1,2,128] r22260 c22260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6724
  · exact u6725
  · exact u6726

def b22261 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 200 274 160 83 147 275), lower := (rows 37 42 69 200 274 160 64 128 256), losses := [] }

theorem u22261 : Upper (D 7) (R 7) [36,40,65,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22262 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 200 400 33 82 146 274), lower := (rows 37 42 69 200 400 33 64 128 256), losses := [] }

theorem u22262 : Upper (D 7) (R 7) [36,40,65,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22263 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 200 400 34 83 147 275), lower := (rows 37 42 69 200 400 34 64 128 256), losses := [] }

theorem u22263 : Upper (D 7) (R 7) [36,40,65,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22264 : Route 9 := (fun mask => (mask,id))

def c22264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22264 : Upper (D 7) (R 7) [36,40,65,192,384,16] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,384,16] 13 (by decide) (choices 1) [1,2] r22264 c22264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6727
  · exact u6728

def b22265 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 265 82 34 208 144 400), lower := (rows 37 42 69 265 82 34 64 128 256), losses := [] }

theorem u22265 : Upper (D 7) (R 7) [36,40,65,257,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22266 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 265 82 48 194 130 386), lower := (rows 37 42 69 265 82 48 64 128 256), losses := [] }

theorem u22266 : Upper (D 7) (R 7) [36,40,65,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22266 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22267 : Route 9 := (fun mask => (mask,id))

def c22267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22267 : Upper (D 7) (R 7) [36,40,65,257,66,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,257,66,128] 13 (by decide) (choices 1) [2,16,128] r22267 c22267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6729
  · exact u6730
  · exact u6731

def b22268 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 265 146 34 208 208 464), lower := (rows 37 42 69 265 146 34 64 128 256), losses := [] }

theorem u22268 : Upper (D 7) (R 7) [36,40,65,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22269 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 42 69 265 146 48 194 194 450), lower := (rows 37 42 69 265 146 48 64 128 256), losses := [] }

theorem u22269 : Upper (D 7) (R 7) [36,40,65,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22269 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22270 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 265 146 96 210 146 402), lower := (rows 37 42 69 265 146 96 64 128 256), losses := [] }

theorem u22270 : Upper (D 7) (R 7) [36,40,65,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22271 : Route 9 := (fun mask => (mask,id))

def c22271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22271 : Upper (D 7) (R 7) [36,40,65,257,130,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,257,130,128] 13 (by decide) (choices 1) [2,16] r22271 c22271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6732
  · exact u6733

def b22272 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 265 208 34 210 146 402), lower := (rows 37 42 69 265 208 34 64 128 256), losses := [] }

theorem u22272 : Upper (D 7) (R 7) [36,40,65,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22273 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 265 208 48 194 130 386), lower := (rows 37 42 69 265 208 48 64 128 256), losses := [] }

theorem u22273 : Upper (D 7) (R 7) [36,40,65,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22273 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22274 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 42 69 265 208 160 82 146 274), lower := (rows 37 42 69 265 208 160 64 128 256), losses := [] }

theorem u22274 : Upper (D 7) (R 7) [36,40,65,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22275 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 266 82 33 208 144 400), lower := (rows 37 42 69 266 82 33 64 128 256), losses := [] }

theorem u22275 : Upper (D 7) (R 7) [36,40,65,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22276 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 37 42 69 266 82 48 193 129 385), lower := (rows 37 42 69 266 82 48 64 128 256), losses := [] }

theorem u22276 : Upper (D 7) (R 7) [36,40,65,258,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22276 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22277 : Route 9 := (fun mask => (mask,id))

def c22277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22277 : Upper (D 7) (R 7) [36,40,65,258,66,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,66,128] 13 (by decide) (choices 1) [1,16,128] r22277 c22277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6734
  · exact u6735
  · exact u6736

def b22278 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 69 266 145 34 208 208 464), lower := (rows 37 42 69 266 145 34 64 128 256), losses := [] }

theorem u22278 : Upper (D 7) (R 7) [36,40,65,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22279 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 42 69 266 145 48 194 194 450), lower := (rows 37 42 69 266 145 48 64 128 256), losses := [] }

theorem u22279 : Upper (D 7) (R 7) [36,40,65,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22279 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22280 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 266 145 96 210 146 402), lower := (rows 37 42 69 266 145 96 64 128 256), losses := [] }

theorem u22280 : Upper (D 7) (R 7) [36,40,65,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22281 : Route 9 := (fun mask => (mask,id))

def c22281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22281 : Upper (D 7) (R 7) [36,40,65,258,129,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,129,128] 13 (by decide) (choices 1) [2,16] r22281 c22281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6737
  · exact u6738

def b22282 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 266 146 33 208 208 464), lower := (rows 37 42 69 266 146 33 64 128 256), losses := [] }

theorem u22282 : Upper (D 7) (R 7) [36,40,65,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22283 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 37 42 69 266 146 48 193 193 449), lower := (rows 37 42 69 266 146 48 64 128 256), losses := [] }

theorem u22283 : Upper (D 7) (R 7) [36,40,65,258,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22283 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22284 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 266 146 96 209 145 401), lower := (rows 37 42 69 266 146 96 64 128 256), losses := [] }

theorem u22284 : Upper (D 7) (R 7) [36,40,65,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22285 : Route 9 := (fun mask => (mask,id))

def c22285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22285 : Upper (D 7) (R 7) [36,40,65,258,130,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,130,128] 13 (by decide) (choices 1) [1,16] r22285 c22285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6739
  · exact u6740

def b22286 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 266 208 33 210 146 402), lower := (rows 37 42 69 266 208 33 64 128 256), losses := [] }

theorem u22286 : Upper (D 7) (R 7) [36,40,65,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22287 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 69 266 208 34 209 145 401), lower := (rows 37 42 69 266 208 34 64 128 256), losses := [] }

theorem u22287 : Upper (D 7) (R 7) [36,40,65,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22288 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 266 208 48 195 131 387), lower := (rows 37 42 69 266 208 48 64 128 256), losses := [] }

theorem u22288 : Upper (D 7) (R 7) [36,40,65,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22288 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22289 : Route 9 := (fun mask => (mask,id))

def c22289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22289 : Upper (D 7) (R 7) [36,40,65,258,192,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258,192,128] 13 (by decide) (choices 1) [1,2,16] r22289 c22289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6741
  · exact u6742
  · exact u6743

def b22290 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 280 82 33 194 130 386), lower := (rows 37 42 69 280 82 33 64 128 256), losses := [] }

theorem u22290 : Upper (D 7) (R 7) [36,40,65,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22291 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 42 69 280 82 34 193 129 385), lower := (rows 37 42 69 280 82 34 64 128 256), losses := [] }

theorem u22291 : Upper (D 7) (R 7) [36,40,65,272,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22292 : Route 9 := (fun mask => (mask,id))

def c22292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22292 : Upper (D 7) (R 7) [36,40,65,272,66,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272,66,128] 13 (by decide) (choices 1) [1,2,128] r22292 c22292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6744
  · exact u6745
  · exact u6746

def b22293 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 69 280 145 34 194 194 450), lower := (rows 37 42 69 280 145 34 64 128 256), losses := [] }

theorem u22293 : Upper (D 7) (R 7) [36,40,65,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22294 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 280 145 96 194 130 386), lower := (rows 37 42 69 280 145 96 64 128 256), losses := [] }

theorem u22294 : Upper (D 7) (R 7) [36,40,65,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22295 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 42 69 280 145 160 66 194 322), lower := (rows 37 42 69 280 145 160 64 128 256), losses := [] }

theorem u22295 : Upper (D 7) (R 7) [36,40,65,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22296 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 280 146 33 194 194 450), lower := (rows 37 42 69 280 146 33 64 128 256), losses := [] }

theorem u22296 : Upper (D 7) (R 7) [36,40,65,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22297 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 42 69 280 146 34 193 193 449), lower := (rows 37 42 69 280 146 34 64 128 256), losses := [] }

theorem u22297 : Upper (D 7) (R 7) [36,40,65,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22298 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 280 146 96 195 131 387), lower := (rows 37 42 69 280 146 96 64 128 256), losses := [] }

theorem u22298 : Upper (D 7) (R 7) [36,40,65,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22299 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 37 42 69 280 146 160 67 195 323), lower := (rows 37 42 69 280 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 42 68 314 178 160 64 160 256) },{ target := 6, region := (rows 1 10 4 8 16 176 0 128 256), good := (rows 37 42 5 314 178 160 0 160 256) }] }

theorem u22299 : Upper (D 7) (R 7) [36,40,65,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22300 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 280 208 33 194 130 386), lower := (rows 37 42 69 280 208 33 64 128 256), losses := [] }

theorem u22300 : Upper (D 7) (R 7) [36,40,65,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22301 : Route 9 := (fun mask => (mask,id))

def c22301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22301 : Upper (D 7) (R 7) [36,40,65,272,192,2] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272,192,2] 13 (by decide) (choices 1) [1,2,128] r22301 c22301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6747
  · exact u6748
  · exact u6749

def b22302 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 280 208 160 67 131 259), lower := (rows 37 42 69 280 208 160 64 128 256), losses := [] }

theorem u22302 : Upper (D 7) (R 7) [36,40,65,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22303 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 328 145 34 210 146 402), lower := (rows 37 42 69 328 145 34 64 128 256), losses := [] }

theorem u22303 : Upper (D 7) (R 7) [36,40,65,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22304 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 42 69 328 145 48 194 130 386), lower := (rows 37 42 69 328 145 48 64 128 256), losses := [] }

theorem u22304 : Upper (D 7) (R 7) [36,40,65,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22305 : Route 9 := (fun mask => (mask,id))

def c22305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22305 : Upper (D 7) (R 7) [36,40,65,320,129,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320,129,128] 13 (by decide) (choices 1) [2,16] r22305 c22305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6750
  · exact u6751

def b22306 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 328 146 33 210 146 402), lower := (rows 37 42 69 328 146 33 64 128 256), losses := [] }

theorem u22306 : Upper (D 7) (R 7) [36,40,65,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22307 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 328 146 34 209 145 401), lower := (rows 37 42 69 328 146 34 64 128 256), losses := [] }

theorem u22307 : Upper (D 7) (R 7) [36,40,65,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22308 : Route 9 := (fun mask => (mask,id))

def c22308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22308 : Upper (D 7) (R 7) [36,40,65,320,130,16] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320,130,16] 13 (by decide) (choices 1) [1,2,128] r22308 c22308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6752
  · exact u6753
  · exact u6754

def r22309 : Route 9 := (fun mask => (mask,id))

def c22309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22309 : Upper (D 7) (R 7) [36,40,65,320,130,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320,130,128] 13 (by decide) (choices 1) [1,2,16] r22309 c22309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6755
  · exact u6756
  · exact u6757

def b22310 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 392 82 33 210 146 402), lower := (rows 37 42 69 392 82 33 64 128 256), losses := [] }

theorem u22310 : Upper (D 7) (R 7) [36,40,65,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22311 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 37 42 69 392 82 34 209 145 401), lower := (rows 37 42 69 392 82 34 64 128 256), losses := [] }

theorem u22311 : Upper (D 7) (R 7) [36,40,65,384,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22312 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 392 82 48 195 131 387), lower := (rows 37 42 69 392 82 48 64 128 256), losses := [] }

theorem u22312 : Upper (D 7) (R 7) [36,40,65,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22312 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22313 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 392 82 160 83 147 275), lower := (rows 37 42 69 392 82 160 64 128 256), losses := [] }

theorem u22313 : Upper (D 7) (R 7) [36,40,65,384,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22314 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 69 392 145 34 82 210 338), lower := (rows 37 42 69 392 145 34 64 128 256), losses := [] }

theorem u22314 : Upper (D 7) (R 7) [36,40,65,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22315 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(3,0)], upper := (rows 37 42 69 392 145 48 66 194 322), lower := (rows 37 42 69 392 145 48 64 128 256), losses := [] }

theorem u22315 : Upper (D 7) (R 7) [36,40,65,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22315 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22316 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 392 145 96 82 146 274), lower := (rows 37 42 69 392 145 96 64 128 256), losses := [] }

theorem u22316 : Upper (D 7) (R 7) [36,40,65,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22317 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 392 146 33 82 210 338), lower := (rows 37 42 69 392 146 33 64 128 256), losses := [] }

theorem u22317 : Upper (D 7) (R 7) [36,40,65,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22318 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 42 69 392 146 34 81 209 337), lower := (rows 37 42 69 392 146 34 64 128 256), losses := [] }

theorem u22318 : Upper (D 7) (R 7) [36,40,65,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22319 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 392 146 48 67 195 323), lower := (rows 37 42 69 392 146 48 64 128 256), losses := [] }

theorem u22319 : Upper (D 7) (R 7) [36,40,65,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22319 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22319
end Delivery.IrregularNine14.P07
