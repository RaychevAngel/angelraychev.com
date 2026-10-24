import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0113

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22380 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 200 400 34 81 145 273), lower := (rows 37 42 70 200 400 34 64 128 256), losses := [] }

theorem u22380 : Upper (D 7) (R 7) [36,40,66,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22381 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7)], upper := (rows 37 42 70 200 400 48 67 131 259), lower := (rows 37 42 70 200 400 48 64 128 256), losses := [] }

theorem u22381 : Upper (D 7) (R 7) [36,40,66,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22381 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22382 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 265 81 34 208 144 400), lower := (rows 37 42 70 265 81 34 64 128 256), losses := [] }

theorem u22382 : Upper (D 7) (R 7) [36,40,66,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22383 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 42 70 265 81 48 194 130 386), lower := (rows 37 42 70 265 81 48 64 128 256), losses := [] }

theorem u22383 : Upper (D 7) (R 7) [36,40,66,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22383 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22384 : Route 9 := (fun mask => (mask,id))

def c22384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22384 : Upper (D 7) (R 7) [36,40,66,257,65,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,65,128] 13 (by decide) (choices 1) [2,16,128] r22384 c22384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6787
  · exact u6788
  · exact u6789

def b22385 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 265 145 34 208 208 464), lower := (rows 37 42 70 265 145 34 64 128 256), losses := [] }

theorem u22385 : Upper (D 7) (R 7) [36,40,66,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22386 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 196, targets := 33 }], pairs := [(2,0),(2,5),(3,5)], upper := (rows 37 42 70 265 145 48 194 194 450), lower := (rows 37 42 70 265 145 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 17 0 70 134 262), good := (rows 477 462 454 281 153 16 64 128 256) }] }

theorem u22386 : Upper (D 7) (R 7) [36,40,66,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22386 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22387 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 265 145 96 210 146 402), lower := (rows 37 42 70 265 145 96 64 128 256), losses := [] }

theorem u22387 : Upper (D 7) (R 7) [36,40,66,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22388 : Route 9 := (fun mask => (mask,id))

def c22388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22388 : Upper (D 7) (R 7) [36,40,66,257,129,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,129,128] 13 (by decide) (choices 1) [2,16] r22388 c22388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6790
  · exact u6791

def b22389 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 70 265 146 33 208 208 464), lower := (rows 37 42 70 265 146 33 64 128 256), losses := [] }

theorem u22389 : Upper (D 7) (R 7) [36,40,66,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22390 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 456, targets := 34 }], pairs := [(2,5),(3,1),(3,5)], upper := (rows 37 42 70 265 146 48 193 193 449), lower := (rows 37 42 70 265 146 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 18 0 73 137 265), good := (rows 461 478 86 457 150 16 64 128 256) }] }

theorem u22390 : Upper (D 7) (R 7) [36,40,66,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22390 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22391 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 265 146 96 209 145 401), lower := (rows 37 42 70 265 146 96 64 128 256), losses := [] }

theorem u22391 : Upper (D 7) (R 7) [36,40,66,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22392 : Route 9 := (fun mask => (mask,id))

def c22392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22392 : Upper (D 7) (R 7) [36,40,66,257,130,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,130,128] 13 (by decide) (choices 1) [1,16] r22392 c22392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6792
  · exact u6793

def b22393 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 70 265 208 33 210 146 402), lower := (rows 37 42 70 265 208 33 64 128 256), losses := [] }

theorem u22393 : Upper (D 7) (R 7) [36,40,66,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22394 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 265 208 34 209 145 401), lower := (rows 37 42 70 265 208 34 64 128 256), losses := [] }

theorem u22394 : Upper (D 7) (R 7) [36,40,66,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22395 : Route 9 := (fun mask => (mask,id))

def c22395 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22395 : Upper (D 7) (R 7) [36,40,66,257,192,16] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,192,16] 13 (by decide) (choices 1) [1,2,128] r22395 c22395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6794
  · exact u6795
  · exact u6796

def r22396 : Route 9 := (fun mask => (mask,id))

def c22396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22396 : Upper (D 7) (R 7) [36,40,66,257,192,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,192,128] 13 (by decide) (choices 1) [1,2,16] r22396 c22396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6797
  · exact u6798
  · exact u6799

def b22397 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 42 70 266 145 33 208 208 464), lower := (rows 37 42 70 266 145 33 64 128 256), losses := [] }

theorem u22397 : Upper (D 7) (R 7) [36,40,66,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22398 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 37 42 70 266 145 48 193 193 449), lower := (rows 37 42 70 266 145 48 64 128 256), losses := [] }

theorem u22398 : Upper (D 7) (R 7) [36,40,66,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22398 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22399 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 266 145 96 209 145 401), lower := (rows 37 42 70 266 145 96 64 128 256), losses := [] }

theorem u22399 : Upper (D 7) (R 7) [36,40,66,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22400 : Route 9 := (fun mask => (mask,id))

def c22400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22400 : Upper (D 7) (R 7) [36,40,66,258,129,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,258,129,128] 13 (by decide) (choices 1) [1,16] r22400 c22400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6800
  · exact u6801

def b22401 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 42 70 266 208 33 209 145 401), lower := (rows 37 42 70 266 208 33 64 128 256), losses := [] }

theorem u22401 : Upper (D 7) (R 7) [36,40,66,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22402 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 37 42 70 266 208 48 193 129 385), lower := (rows 37 42 70 266 208 48 64 128 256), losses := [] }

theorem u22402 : Upper (D 7) (R 7) [36,40,66,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22402 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22403 : Route 9 := (fun mask => (mask,id))

def c22403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22403 : Upper (D 7) (R 7) [36,40,66,258,192,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,258,192,128] 13 (by decide) (choices 1) [1,16] r22403 c22403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6802
  · exact u6803

def b22404 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 42 70 280 81 33 194 130 386), lower := (rows 37 42 70 280 81 33 64 128 256), losses := [] }

theorem u22404 : Upper (D 7) (R 7) [36,40,66,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22405 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 280 81 34 193 129 385), lower := (rows 37 42 70 280 81 34 64 128 256), losses := [] }

theorem u22405 : Upper (D 7) (R 7) [36,40,66,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22406 : Route 9 := (fun mask => (mask,id))

def c22406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22406 : Upper (D 7) (R 7) [36,40,66,272,65,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272,65,128] 13 (by decide) (choices 1) [1,2,128] r22406 c22406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6804
  · exact u6805
  · exact u6806

def b22407 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 1, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 42 70 280 145 33 194 194 450), lower := (rows 37 42 70 280 145 33 64 128 256), losses := [] }

theorem u22407 : Upper (D 7) (R 7) [36,40,66,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22408 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 280 145 34 193 193 449), lower := (rows 37 42 70 280 145 34 64 128 256), losses := [] }

theorem u22408 : Upper (D 7) (R 7) [36,40,66,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22409 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 280 145 96 195 131 387), lower := (rows 37 42 70 280 145 96 64 128 256), losses := [] }

theorem u22409 : Upper (D 7) (R 7) [36,40,66,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22410 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 37 42 70 280 145 160 67 195 323), lower := (rows 37 42 70 280 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 42 70 314 176 160 64 160 256) },{ target := 6, region := (rows 1 10 4 8 16 176 0 128 256), good := (rows 37 42 6 314 177 160 0 160 256) }] }

theorem u22410 : Upper (D 7) (R 7) [36,40,66,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22411 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 42 70 280 146 33 193 193 449), lower := (rows 37 42 70 280 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 97 161 289), good := (rows 453 478 94 280 158 449 64 128 256) }] }

theorem u22411 : Upper (D 7) (R 7) [36,40,66,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22412 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 280 146 96 193 129 385), lower := (rows 37 42 70 280 146 96 64 128 256), losses := [] }

theorem u22412 : Upper (D 7) (R 7) [36,40,66,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22413 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(2,7)], upper := (rows 37 42 70 280 146 160 65 193 321), lower := (rows 37 42 70 280 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 42 70 314 178 160 64 160 256) }] }

theorem u22413 : Upper (D 7) (R 7) [36,40,66,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22414 : Route 9 := (fun mask => (mask,id))

def c22414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22414 : Upper (D 7) (R 7) [36,40,66,272,192,1] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272,192,1] 13 (by decide) (choices 1) [1,2,128] r22414 c22414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6807
  · exact u6808
  · exact u6809

def b22415 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 280 208 34 193 129 385), lower := (rows 37 42 70 280 208 34 64 128 256), losses := [] }

theorem u22415 : Upper (D 7) (R 7) [36,40,66,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22416 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(2,7)], upper := (rows 37 42 70 280 208 160 67 131 259), lower := (rows 37 42 70 280 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 42 70 314 240 160 64 160 256) }] }

theorem u22416 : Upper (D 7) (R 7) [36,40,66,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22417 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 328 145 33 210 146 402), lower := (rows 37 42 70 328 145 33 64 128 256), losses := [] }

theorem u22417 : Upper (D 7) (R 7) [36,40,66,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22418 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 328 145 34 209 145 401), lower := (rows 37 42 70 328 145 34 64 128 256), losses := [] }

theorem u22418 : Upper (D 7) (R 7) [36,40,66,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22419 : Route 9 := (fun mask => (mask,id))

def c22419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22419 : Upper (D 7) (R 7) [36,40,66,320,129,16] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,129,16] 13 (by decide) (choices 1) [1,2,128] r22419 c22419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6810
  · exact u6811
  · exact u6812

def r22420 : Route 9 := (fun mask => (mask,id))

def c22420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22420 : Upper (D 7) (R 7) [36,40,66,320,129,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,129,128] 13 (by decide) (choices 1) [1,2,16] r22420 c22420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6813
  · exact u6814
  · exact u6815

def b22421 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 42 70 328 146 33 209 145 401), lower := (rows 37 42 70 328 146 33 64 128 256), losses := [] }

theorem u22421 : Upper (D 7) (R 7) [36,40,66,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22422 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(3,5)], upper := (rows 37 42 70 328 146 48 193 129 385), lower := (rows 37 42 70 328 146 48 64 128 256), losses := [] }

theorem u22422 : Upper (D 7) (R 7) [36,40,66,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22422 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22423 : Route 9 := (fun mask => (mask,id))

def c22423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22423 : Upper (D 7) (R 7) [36,40,66,320,130,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,130,128] 13 (by decide) (choices 1) [1,16] r22423 c22423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6816
  · exact u6817

def b22424 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 42 70 392 19 33 208 208 464), lower := (rows 37 42 70 392 19 33 64 128 256), losses := [] }

theorem u22424 : Upper (D 7) (R 7) [36,40,66,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22425 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 42 70 392 19 48 193 193 449), lower := (rows 37 42 70 392 19 48 64 128 256), losses := [] }

theorem u22425 : Upper (D 7) (R 7) [36,40,66,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22425 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22426 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 392 19 96 209 145 401), lower := (rows 37 42 70 392 19 96 64 128 256), losses := [] }

theorem u22426 : Upper (D 7) (R 7) [36,40,66,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22427 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 392 19 160 81 209 337), lower := (rows 37 42 70 392 19 160 64 128 256), losses := [] }

theorem u22427 : Upper (D 7) (R 7) [36,40,66,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22428 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 42 70 392 81 33 210 146 402), lower := (rows 37 42 70 392 81 33 64 128 256), losses := [] }

theorem u22428 : Upper (D 7) (R 7) [36,40,66,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22429 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 392 81 34 209 145 401), lower := (rows 37 42 70 392 81 34 64 128 256), losses := [] }

theorem u22429 : Upper (D 7) (R 7) [36,40,66,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22430 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 42 70 392 81 48 195 131 387), lower := (rows 37 42 70 392 81 48 64 128 256), losses := [] }

theorem u22430 : Upper (D 7) (R 7) [36,40,66,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22430 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22431 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 70 392 81 160 83 147 275), lower := (rows 37 42 70 392 81 160 64 128 256), losses := [] }

theorem u22431 : Upper (D 7) (R 7) [36,40,66,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22432 : Route 9 := (fun mask => (mask,id))

def c22432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22432 : Upper (D 7) (R 7) [36,40,66,384,129,1] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,129,1] 13 (by decide) (choices 1) [2,16] r22432 c22432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6818
  · exact u6819

def b22433 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 392 145 34 81 209 337), lower := (rows 37 42 70 392 145 34 64 128 256), losses := [] }

theorem u22433 : Upper (D 7) (R 7) [36,40,66,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22434 : Route 9 := (fun mask => (mask,id))

def c22434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22434 : Upper (D 7) (R 7) [36,40,66,384,129,16] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,129,16] 13 (by decide) (choices 1) [1,2] r22434 c22434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6820
  · exact u6821

def b22435 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 392 145 96 83 147 275), lower := (rows 37 42 70 392 145 96 64 128 256), losses := [] }

theorem u22435 : Upper (D 7) (R 7) [36,40,66,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22436 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 42 70 392 146 33 81 209 337), lower := (rows 37 42 70 392 146 33 64 128 256), losses := [] }

theorem u22436 : Upper (D 7) (R 7) [36,40,66,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22437 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 70 392 146 48 65 193 321), lower := (rows 37 42 70 392 146 48 64 128 256), losses := [] }

theorem u22437 : Upper (D 7) (R 7) [36,40,66,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22437 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22438 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 70 392 146 96 81 145 273), lower := (rows 37 42 70 392 146 96 64 128 256), losses := [] }

theorem u22438 : Upper (D 7) (R 7) [36,40,66,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22439 : Route 9 := (fun mask => (mask,id))

def c22439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22439 : Upper (D 7) (R 7) [36,40,66,384,192,1] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,192,1] 13 (by decide) (choices 1) [1,2,16] r22439 c22439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6822
  · exact u6823
  · exact u6824

#print axioms u22439
end Delivery.IrregularNine14.P07
