import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0146
import IrregularNine14P07C0147

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r25380 : Route 9 := (fun mask => (mask,id))

def c25380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25380 : Upper (D 7) (R 7) [36,192,72,258,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,129,16] 13 (by decide) (choices 1) [1,2,32] r25380 c25380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8773
  · exact u8774
  · exact u8775

def r25381 : Route 9 := (fun mask => (mask,id))

def c25381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25381 : Upper (D 7) (R 7) [36,192,72,258,160,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,160,1] 13 (by decide) (choices 1) [1,2,16] r25381 c25381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8776
  · exact u8777
  · exact u8778

def b25382 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,6),(4,0),(4,1),(4,6)], upper := (rows 37 194 76 266 176 34 81 145 273), lower := (rows 37 194 76 266 176 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 23 42 0 133 261), good := (rows 437 178 445 314 176 50 0 128 256) }] }

theorem u25382 : Upper (D 7) (R 7) [36,192,72,258,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25383 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 266 176 48 67 131 259), lower := (rows 37 194 76 266 176 48 64 128 256), losses := [] }

theorem u25383 : Upper (D 7) (R 7) [36,192,72,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25383 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25384 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 280 19 33 226 162 418), lower := (rows 37 194 76 280 19 33 64 128 256), losses := [] }

theorem u25384 : Upper (D 7) (R 7) [36,192,72,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25385 : Route 9 := (fun mask => (mask,id))

def c25385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25385 : Upper (D 7) (R 7) [36,192,72,272,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,3,2] 13 (by decide) (choices 1) [1,32,128] r25385 c25385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8779
  · exact u8780
  · exact u8781

def r25386 : Route 9 := (fun mask => (mask,id))

def c25386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25386 : Upper (D 7) (R 7) [36,192,72,272,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,3,128] 13 (by decide) (choices 1) [1,2,32] r25386 c25386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8782
  · exact u8783
  · exact u8784

def b25387 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 280 50 33 195 131 387), lower := (rows 37 194 76 280 50 33 64 128 256), losses := [] }

theorem u25387 : Upper (D 7) (R 7) [36,192,72,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25388 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 76 280 50 34 193 129 385), lower := (rows 37 194 76 280 50 34 64 128 256), losses := [] }

theorem u25388 : Upper (D 7) (R 7) [36,192,72,272,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25389 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 76 280 50 160 67 131 259), lower := (rows 37 194 76 280 50 160 64 128 256), losses := [] }

theorem u25389 : Upper (D 7) (R 7) [36,192,72,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25390 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 280 145 33 98 162 290), lower := (rows 37 194 76 280 145 33 64 128 256), losses := [] }

theorem u25390 : Upper (D 7) (R 7) [36,192,72,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25391 : Route 9 := (fun mask => (mask,id))

def c25391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25391 : Upper (D 7) (R 7) [36,192,72,272,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,129,2] 13 (by decide) (choices 1) [1,2,32] r25391 c25391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8785
  · exact u8786
  · exact u8787

def b25392 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 280 176 33 67 131 259), lower := (rows 37 194 76 280 176 33 64 128 256), losses := [] }

theorem u25392 : Upper (D 7) (R 7) [36,192,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25393 : Route 9 := (fun mask => (mask,id))

def c25393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25393 : Upper (D 7) (R 7) [36,192,72,272,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,160,2] 13 (by decide) (choices 1) [1,2] r25393 c25393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8788
  · exact u8789

def b25394 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 296 19 33 210 146 402), lower := (rows 37 194 76 296 19 33 64 128 256), losses := [] }

theorem u25394 : Upper (D 7) (R 7) [36,192,72,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25395 : Route 9 := (fun mask => (mask,id))

def c25395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25395 : Upper (D 7) (R 7) [36,192,72,288,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,288,3,2] 13 (by decide) (choices 1) [1,16,128] r25395 c25395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8790
  · exact u8791
  · exact u8792

def b25396 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 37 194 76 296 19 48 195 131 387), lower := (rows 37 194 76 296 19 48 64 128 256), losses := [] }

theorem u25396 : Upper (D 7) (R 7) [36,192,72,288,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25396 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25397 : Route 9 := (fun mask => (mask,id))

def c25397 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25397 : Upper (D 7) (R 7) [36,192,72,288,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,288,3,128] 13 (by decide) (choices 1) [1,2,16] r25397 c25397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8793
  · exact u8794
  · exact u8795

def b25398 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 296 145 33 82 146 274), lower := (rows 37 194 76 296 145 33 64 128 256), losses := [] }

theorem u25398 : Upper (D 7) (R 7) [36,192,72,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25399 : Route 9 := (fun mask => (mask,id))

def c25399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25399 : Upper (D 7) (R 7) [36,192,72,288,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,288,129,2] 13 (by decide) (choices 1) [1,2,16] r25399 c25399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8796
  · exact u8797
  · exact u8798

def r25400 : Route 9 := (fun mask => (mask,id))

def c25400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25400 : Upper (D 7) (R 7) [36,192,72,288,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,288,129,16] 13 (by decide) (choices 1) [1,2] r25400 c25400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8799
  · exact u8800

def b25401 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 194 76 392 19 33 114 178 306), lower := (rows 37 194 76 392 19 33 64 128 256), losses := [] }

theorem u25401 : Upper (D 7) (R 7) [36,192,72,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25402 : Route 9 := (fun mask => (mask,id))

def c25402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25402 : Upper (D 7) (R 7) [36,192,72,384,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,3,2] 13 (by decide) (choices 1) [1,16,32] r25402 c25402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8801
  · exact u8802
  · exact u8803

def r25403 : Route 9 := (fun mask => (mask,id))

def c25403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25403 : Upper (D 7) (R 7) [36,192,72,384,3,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,3,16] 13 (by decide) (choices 1) [1,2,32] r25403 c25403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8804
  · exact u8805
  · exact u8806

def r25404 : Route 9 := (fun mask => (mask,id))

def c25404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25404 : Upper (D 7) (R 7) [36,192,72,384,34,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,34,1] 13 (by decide) (choices 1) [1,2,16] r25404 c25404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8807
  · exact u8808
  · exact u8809

def b25405 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 76 392 50 34 81 145 273), lower := (rows 37 194 76 392 50 34 64 128 256), losses := [] }

theorem u25405 : Upper (D 7) (R 7) [36,192,72,384,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25406 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 392 50 48 67 131 259), lower := (rows 37 194 76 392 50 48 64 128 256), losses := [] }

theorem u25406 : Upper (D 7) (R 7) [36,192,72,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25406 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25407 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 3, region := 48, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 261 11 50 40 208 208 464), lower := (rows 37 194 261 11 50 40 64 128 256), losses := [] }

theorem u25407 : Upper (D 7) (R 7) [36,192,257,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25407 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25408 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 261 11 50 48 200 200 456), lower := (rows 37 194 261 11 50 48 64 128 256), losses := [] }

theorem u25408 : Upper (D 7) (R 7) [36,192,257,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25409 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 261 11 50 96 216 152 408), lower := (rows 37 194 261 11 50 96 64 128 256), losses := [] }

theorem u25409 : Upper (D 7) (R 7) [36,192,257,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25410 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 48, targets := 192 }], pairs := [(1,0),(4,0),(4,6),(4,7)], upper := (rows 37 194 261 11 56 34 208 208 464), lower := (rows 37 194 261 11 56 34 64 128 256), losses := [] }

theorem u25410 : Upper (D 7) (R 7) [36,192,257,3,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25411 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 261 11 56 48 194 194 450), lower := (rows 37 194 261 11 56 48 64 128 256), losses := [] }

theorem u25411 : Upper (D 7) (R 7) [36,192,257,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25411 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25412 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 37 194 261 11 56 96 210 146 402), lower := (rows 37 194 261 11 56 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 98 64 128 256), good := (rows 37 224 261 57 56 96 96 128 256) }] }

theorem u25412 : Upper (D 7) (R 7) [36,192,257,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25413 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 261 11 88 34 240 176 432), lower := (rows 37 194 261 11 88 34 64 128 256), losses := [{ target := 6, region := (rows 17 2 20 8 16 42 0 144 272), good := (rows 37 162 261 43 445 34 0 128 256) }] }

theorem u25413 : Upper (D 7) (R 7) [36,192,257,3,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25414 : Route 9 := (fun mask => (mask,id))

def c25414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25414 : Upper (D 7) (R 7) [36,192,257,3,72,16] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,72,16] 13 (by decide) (choices 1) [2,32,128] r25414 c25414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8810
  · exact u8811
  · exact u8812

def r25415 : Route 9 := (fun mask => (mask,id))

def c25415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25415 : Upper (D 7) (R 7) [36,192,257,3,72,128] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,72,128] 13 (by decide) (choices 1) [2,16,32] r25415 c25415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8813
  · exact u8814
  · exact u8815

def r25416 : Route 9 := (fun mask => (mask,id))

def c25416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25416 : Upper (D 7) (R 7) [36,192,257,3,96,2] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,96,2] 13 (by decide) (choices 1) [8,16,128] r25416 c25416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8816
  · exact u8817
  · exact u8818

def b25417 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 4, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 261 11 112 40 210 146 402), lower := (rows 37 194 261 11 112 40 64 128 256), losses := [] }

theorem u25417 : Upper (D 7) (R 7) [36,192,257,3,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25417 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25418 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 261 11 112 48 202 138 394), lower := (rows 37 194 261 11 112 48 64 128 256), losses := [] }

theorem u25418 : Upper (D 7) (R 7) [36,192,257,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25418 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25419 : Route 9 := (fun mask => (mask,id))

def c25419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25419 : Upper (D 7) (R 7) [36,192,257,3,96,128] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,96,128] 13 (by decide) (choices 1) [2,8,16] r25419 c25419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8819
  · exact u8820
  · exact u8821

def b25420 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 5, region := 453, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 261 25 26 34 224 224 480), lower := (rows 37 194 261 25 26 34 64 128 256), losses := [] }

theorem u25420 : Upper (D 7) (R 7) [36,192,257,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25421 : Route 9 := (fun mask => (mask,id))

def c25421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25421 : Upper (D 7) (R 7) [36,192,257,17,10,64] 13 := by
  apply FastRouting.sound _ _ [36,192,257,17,10,64] 13 (by decide) (choices 1) [2,32,128] r25421 c25421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8822
  · exact u8823
  · exact u8824

def b25422 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 261 26 56 33 194 194 450), lower := (rows 37 194 261 26 56 33 64 128 256), losses := [] }

theorem u25422 : Upper (D 7) (R 7) [36,192,257,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25423 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 194 261 26 56 34 193 193 449), lower := (rows 37 194 261 26 56 34 64 128 256), losses := [] }

theorem u25423 : Upper (D 7) (R 7) [36,192,257,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25424 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 194 261 26 56 96 195 131 387), lower := (rows 37 194 261 26 56 96 64 128 256), losses := [] }

theorem u25424 : Upper (D 7) (R 7) [36,192,257,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25425 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 261 26 112 33 202 138 394), lower := (rows 37 194 261 26 112 33 64 128 256), losses := [] }

theorem u25425 : Upper (D 7) (R 7) [36,192,257,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25426 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 194 261 26 112 34 201 137 393), lower := (rows 37 194 261 26 112 34 64 128 256), losses := [] }

theorem u25426 : Upper (D 7) (R 7) [36,192,257,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25427 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 194 261 26 112 40 195 131 387), lower := (rows 37 194 261 26 112 40 64 128 256), losses := [] }

theorem u25427 : Upper (D 7) (R 7) [36,192,257,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25427 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25428 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 37 194 261 26 112 160 75 139 267), lower := (rows 37 194 261 26 112 160 64 128 256), losses := [] }

theorem u25428 : Upper (D 7) (R 7) [36,192,257,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25429 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 194 261 42 81 34 216 152 408), lower := (rows 37 194 261 42 81 34 64 128 256), losses := [] }

theorem u25429 : Upper (D 7) (R 7) [36,192,257,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25430 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 261 42 81 40 210 146 402), lower := (rows 37 194 261 42 81 40 64 128 256), losses := [] }

theorem u25430 : Upper (D 7) (R 7) [36,192,257,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25430 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25431 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 3, region := 389, targets := 64 }], pairs := [(0,6),(1,0),(3,0)], upper := (rows 37 194 261 42 81 48 202 138 394), lower := (rows 37 194 261 42 81 48 64 128 256), losses := [] }

theorem u25431 : Upper (D 7) (R 7) [36,192,257,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25431 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25432 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 261 42 81 160 90 154 282), lower := (rows 37 194 261 42 81 160 64 128 256), losses := [] }

theorem u25432 : Upper (D 7) (R 7) [36,192,257,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25433 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 261 42 88 33 210 146 402), lower := (rows 37 194 261 42 88 33 64 128 256), losses := [] }

theorem u25433 : Upper (D 7) (R 7) [36,192,257,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25434 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 194 261 42 88 34 209 145 401), lower := (rows 37 194 261 42 88 34 64 128 256), losses := [] }

theorem u25434 : Upper (D 7) (R 7) [36,192,257,34,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25435 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 194 261 42 88 48 195 131 387), lower := (rows 37 194 261 42 88 48 64 128 256), losses := [] }

theorem u25435 : Upper (D 7) (R 7) [36,192,257,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25435 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25436 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 261 42 88 160 83 147 275), lower := (rows 37 194 261 42 88 160 64 128 256), losses := [] }

theorem u25436 : Upper (D 7) (R 7) [36,192,257,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25437 : Route 9 := (fun mask => (mask,id))

def c25437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25437 : Upper (D 7) (R 7) [36,192,257,48,65,2] 13 := by
  apply FastRouting.sound _ _ [36,192,257,48,65,2] 13 (by decide) (choices 1) [2,8,128] r25437 c25437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8825
  · exact u8826
  · exact u8827

def b25438 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 261 56 81 40 194 130 386), lower := (rows 37 194 261 56 81 40 64 128 256), losses := [] }

theorem u25438 : Upper (D 7) (R 7) [36,192,257,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25438 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25439 : Route 9 := (fun mask => (mask,id))

def c25439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25439 : Upper (D 7) (R 7) [36,192,257,48,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,257,48,65,128] 13 (by decide) (choices 1) [2,8] r25439 c25439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8828
  · exact u8829

#print axioms u25439
end Delivery.IrregularNine14.P07
