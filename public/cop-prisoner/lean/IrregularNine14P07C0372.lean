import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0112
import IrregularNine14P07C0113

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22320 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 392 146 96 83 147 275), lower := (rows 37 42 69 392 146 96 64 128 256), losses := [] }

theorem u22320 : Upper (D 7) (R 7) [36,40,65,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22321 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 392 208 33 82 146 274), lower := (rows 37 42 69 392 208 33 64 128 256), losses := [] }

theorem u22321 : Upper (D 7) (R 7) [36,40,65,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22322 : Route 9 := (fun mask => (mask,id))

def c22322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22322 : Upper (D 7) (R 7) [36,40,65,384,192,2] 13 := by
  apply FastRouting.sound _ _ [36,40,65,384,192,2] 13 (by decide) (choices 1) [1,2,16] r22322 c22322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6758
  · exact u6759
  · exact u6760

def b22323 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 392 208 48 67 131 259), lower := (rows 37 42 69 392 208 48 64 128 256), losses := [] }

theorem u22323 : Upper (D 7) (R 7) [36,40,65,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22323 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22324 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 1, region := 452, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 37 42 70 88 145 33 450 386 386), lower := (rows 37 42 70 88 145 33 64 128 256), losses := [] }

theorem u22324 : Upper (D 7) (R 7) [36,40,66,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22325 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 88 145 34 449 385 385), lower := (rows 37 42 70 88 145 34 64 128 256), losses := [] }

theorem u22325 : Upper (D 7) (R 7) [36,40,66,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22326 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 88 145 160 323 387 259), lower := (rows 37 42 70 88 145 160 64 128 256), losses := [] }

theorem u22326 : Upper (D 7) (R 7) [36,40,66,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22327 : Route 9 := (fun mask => (mask,id))

def c22327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22327 : Upper (D 7) (R 7) [36,40,66,80,129,256] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,129,256] 13 (by decide) (choices 1) [1,2,128] r22327 c22327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6761
  · exact u6762
  · exact u6763

def b22328 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 88 146 33 449 385 385), lower := (rows 37 42 70 88 146 33 64 128 256), losses := [] }

theorem u22328 : Upper (D 7) (R 7) [36,40,66,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22329 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 88 146 160 321 385 257), lower := (rows 37 42 70 88 146 160 64 128 256), losses := [] }

theorem u22329 : Upper (D 7) (R 7) [36,40,66,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22330 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(0,6),(4,6)], upper := (rows 37 42 70 88 146 288 193 129 385), lower := (rows 37 42 70 88 146 288 64 128 256), losses := [] }

theorem u22330 : Upper (D 7) (R 7) [36,40,66,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22330 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22331 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 1, region := 196, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 37 42 70 88 273 33 194 130 386), lower := (rows 37 42 70 88 273 33 64 128 256), losses := [] }

theorem u22331 : Upper (D 7) (R 7) [36,40,66,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22332 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 88 273 34 193 129 385), lower := (rows 37 42 70 88 273 34 64 128 256), losses := [] }

theorem u22332 : Upper (D 7) (R 7) [36,40,66,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22333 : Route 9 := (fun mask => (mask,id))

def c22333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22333 : Upper (D 7) (R 7) [36,40,66,80,257,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,257,128] 13 (by decide) (choices 1) [1,2,128] r22333 c22333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6764
  · exact u6765
  · exact u6766

def b22334 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 88 274 33 193 129 385), lower := (rows 37 42 70 88 274 33 64 128 256), losses := [] }

theorem u22334 : Upper (D 7) (R 7) [36,40,66,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22335 : Route 9 := (fun mask => (mask,id))

def c22335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22335 : Upper (D 7) (R 7) [36,40,66,80,258,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,258,128] 13 (by decide) (choices 1) [1,128] r22335 c22335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6767
  · exact u6768

def b22336 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 88 400 33 195 131 387), lower := (rows 37 42 70 88 400 33 64 128 256), losses := [] }

theorem u22336 : Upper (D 7) (R 7) [36,40,66,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22337 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 88 400 34 193 129 385), lower := (rows 37 42 70 88 400 34 64 128 256), losses := [] }

theorem u22337 : Upper (D 7) (R 7) [36,40,66,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22338 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 88 400 160 67 131 259), lower := (rows 37 42 70 88 400 160 64 128 256), losses := [] }

theorem u22338 : Upper (D 7) (R 7) [36,40,66,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22339 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 137 81 34 464 400 400), lower := (rows 37 42 70 137 81 34 64 128 256), losses := [] }

theorem u22339 : Upper (D 7) (R 7) [36,40,66,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22340 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 42 70 137 81 48 450 386 386), lower := (rows 37 42 70 137 81 48 64 128 256), losses := [] }

theorem u22340 : Upper (D 7) (R 7) [36,40,66,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22341 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 137 81 160 338 402 274), lower := (rows 37 42 70 137 81 160 64 128 256), losses := [] }

theorem u22341 : Upper (D 7) (R 7) [36,40,66,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22342 : Route 9 := (fun mask => (mask,id))

def c22342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22342 : Upper (D 7) (R 7) [36,40,66,129,65,256] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,65,256] 13 (by decide) (choices 1) [2,16,128] r22342 c22342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6769
  · exact u6770
  · exact u6771

def b22343 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 70 137 208 33 338 402 274), lower := (rows 37 42 70 137 208 33 64 128 256), losses := [] }

theorem u22343 : Upper (D 7) (R 7) [36,40,66,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22344 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 42 70 137 208 48 323 387 259), lower := (rows 37 42 70 137 208 48 64 128 256), losses := [] }

theorem u22344 : Upper (D 7) (R 7) [36,40,66,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22344 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22345 : Route 9 := (fun mask => (mask,id))

def c22345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22345 : Upper (D 7) (R 7) [36,40,66,129,192,256] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,192,256] 13 (by decide) (choices 1) [1,2,16] r22345 c22345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6772
  · exact u6773
  · exact u6774

def b22346 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 137 273 34 208 208 464), lower := (rows 37 42 70 137 273 34 64 128 256), losses := [] }

theorem u22346 : Upper (D 7) (R 7) [36,40,66,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22347 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 196, targets := 33 }], pairs := [(2,0),(2,5),(3,5)], upper := (rows 37 42 70 137 273 48 194 194 450), lower := (rows 37 42 70 137 273 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 17 0 70 134 262), good := (rows 477 462 454 153 281 16 64 128 256) }] }

theorem u22347 : Upper (D 7) (R 7) [36,40,66,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22347 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22348 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 137 273 96 210 146 402), lower := (rows 37 42 70 137 273 96 64 128 256), losses := [] }

theorem u22348 : Upper (D 7) (R 7) [36,40,66,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22349 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 137 273 160 82 210 338), lower := (rows 37 42 70 137 273 160 64 128 256), losses := [] }

theorem u22349 : Upper (D 7) (R 7) [36,40,66,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22350 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 70 137 336 33 210 146 402), lower := (rows 37 42 70 137 336 33 64 128 256), losses := [] }

theorem u22350 : Upper (D 7) (R 7) [36,40,66,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22351 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 137 336 34 209 145 401), lower := (rows 37 42 70 137 336 34 64 128 256), losses := [] }

theorem u22351 : Upper (D 7) (R 7) [36,40,66,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22352 : Route 9 := (fun mask => (mask,id))

def c22352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22352 : Upper (D 7) (R 7) [36,40,66,129,320,16] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,320,16] 13 (by decide) (choices 1) [1,2,128] r22352 c22352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6775
  · exact u6776
  · exact u6777

def b22353 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 137 336 160 83 147 275), lower := (rows 37 42 70 137 336 160 64 128 256), losses := [] }

theorem u22353 : Upper (D 7) (R 7) [36,40,66,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22354 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 42 70 152 81 33 450 386 386), lower := (rows 37 42 70 152 81 33 64 128 256), losses := [] }

theorem u22354 : Upper (D 7) (R 7) [36,40,66,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22355 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 152 81 34 449 385 385), lower := (rows 37 42 70 152 81 34 64 128 256), losses := [] }

theorem u22355 : Upper (D 7) (R 7) [36,40,66,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22356 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 152 81 160 323 387 259), lower := (rows 37 42 70 152 81 160 64 128 256), losses := [] }

theorem u22356 : Upper (D 7) (R 7) [36,40,66,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22357 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 42 70 152 81 288 195 131 387), lower := (rows 37 42 70 152 81 288 64 128 256), losses := [] }

theorem u22357 : Upper (D 7) (R 7) [36,40,66,144,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22357 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22358 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 1, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 42 70 152 273 33 194 194 450), lower := (rows 37 42 70 152 273 33 64 128 256), losses := [] }

theorem u22358 : Upper (D 7) (R 7) [36,40,66,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22359 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 152 273 34 193 193 449), lower := (rows 37 42 70 152 273 34 64 128 256), losses := [] }

theorem u22359 : Upper (D 7) (R 7) [36,40,66,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22360 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 152 273 96 195 131 387), lower := (rows 37 42 70 152 273 96 64 128 256), losses := [] }

theorem u22360 : Upper (D 7) (R 7) [36,40,66,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22361 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 152 273 160 67 195 323), lower := (rows 37 42 70 152 273 160 64 128 256), losses := [] }

theorem u22361 : Upper (D 7) (R 7) [36,40,66,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22362 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 42 70 152 274 33 193 193 449), lower := (rows 37 42 70 152 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 97 161 289), good := (rows 453 478 94 152 286 449 64 128 256) }] }

theorem u22362 : Upper (D 7) (R 7) [36,40,66,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22363 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 152 274 96 193 129 385), lower := (rows 37 42 70 152 274 96 64 128 256), losses := [] }

theorem u22363 : Upper (D 7) (R 7) [36,40,66,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22364 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 152 274 160 65 193 321), lower := (rows 37 42 70 152 274 160 64 128 256), losses := [] }

theorem u22364 : Upper (D 7) (R 7) [36,40,66,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22365 : Route 9 := (fun mask => (mask,id))

def c22365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22365 : Upper (D 7) (R 7) [36,40,66,144,320,1] 13 := by
  apply FastRouting.sound _ _ [36,40,66,144,320,1] 13 (by decide) (choices 1) [1,2,128] r22365 c22365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6778
  · exact u6779
  · exact u6780

def b22366 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 152 336 34 193 129 385), lower := (rows 37 42 70 152 336 34 64 128 256), losses := [] }

theorem u22366 : Upper (D 7) (R 7) [36,40,66,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22367 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 152 336 160 67 131 259), lower := (rows 37 42 70 152 336 160 64 128 256), losses := [] }

theorem u22367 : Upper (D 7) (R 7) [36,40,66,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22368 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 200 145 33 338 402 274), lower := (rows 37 42 70 200 145 33 64 128 256), losses := [] }

theorem u22368 : Upper (D 7) (R 7) [36,40,66,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22369 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 200 145 34 337 401 273), lower := (rows 37 42 70 200 145 34 64 128 256), losses := [] }

theorem u22369 : Upper (D 7) (R 7) [36,40,66,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22370 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7)], upper := (rows 37 42 70 200 145 48 323 387 259), lower := (rows 37 42 70 200 145 48 64 128 256), losses := [] }

theorem u22370 : Upper (D 7) (R 7) [36,40,66,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22370 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22371 : Route 9 := (fun mask => (mask,id))

def c22371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22371 : Upper (D 7) (R 7) [36,40,66,192,129,256] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192,129,256] 13 (by decide) (choices 1) [1,2,16] r22371 c22371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6781
  · exact u6782
  · exact u6783

def b22372 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 200 273 33 210 146 402), lower := (rows 37 42 70 200 273 33 64 128 256), losses := [] }

theorem u22372 : Upper (D 7) (R 7) [36,40,66,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22373 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 200 273 34 209 145 401), lower := (rows 37 42 70 200 273 34 64 128 256), losses := [] }

theorem u22373 : Upper (D 7) (R 7) [36,40,66,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22374 : Route 9 := (fun mask => (mask,id))

def c22374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22374 : Upper (D 7) (R 7) [36,40,66,192,257,16] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192,257,16] 13 (by decide) (choices 1) [1,2,128] r22374 c22374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6784
  · exact u6785
  · exact u6786

def b22375 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,7)], upper := (rows 37 42 70 200 273 160 83 147 275), lower := (rows 37 42 70 200 273 160 64 128 256), losses := [] }

theorem u22375 : Upper (D 7) (R 7) [36,40,66,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22376 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 200 274 33 209 145 401), lower := (rows 37 42 70 200 274 33 64 128 256), losses := [] }

theorem u22376 : Upper (D 7) (R 7) [36,40,66,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22377 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(3,5)], upper := (rows 37 42 70 200 274 48 193 129 385), lower := (rows 37 42 70 200 274 48 64 128 256), losses := [] }

theorem u22377 : Upper (D 7) (R 7) [36,40,66,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22377 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22378 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,7)], upper := (rows 37 42 70 200 274 160 81 145 273), lower := (rows 37 42 70 200 274 160 64 128 256), losses := [] }

theorem u22378 : Upper (D 7) (R 7) [36,40,66,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22379 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 200 400 33 83 147 275), lower := (rows 37 42 70 200 400 33 64 128 256), losses := [] }

theorem u22379 : Upper (D 7) (R 7) [36,40,66,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22379
end Delivery.IrregularNine14.P07
