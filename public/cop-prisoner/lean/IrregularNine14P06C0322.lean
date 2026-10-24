import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0096
import IrregularNine14P06C0097

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19320 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 26 145 288 68 196 324), lower := (rows 35 67 44 26 145 288 64 128 256), losses := [] }

theorem u19320 : Upper (D 6) (R 6) [34,65,40,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19320 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19321 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 26 148 33 324 452 324), lower := (rows 35 67 44 26 148 33 64 128 256), losses := [] }

theorem u19321 : Upper (D 6) (R 6) [34,65,40,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19322 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 322, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 67 44 26 148 36 321 449 321), lower := (rows 35 67 44 26 148 36 64 128 256), losses := [] }

theorem u19322 : Upper (D 6) (R 6) [34,65,40,18,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19323 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 26 148 96 325 389 261), lower := (rows 35 67 44 26 148 96 64 128 256), losses := [] }

theorem u19323 : Upper (D 6) (R 6) [34,65,40,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19324 : Route 9 := (fun mask => (mask,id))

def c19324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19324 : Upper (D 6) (R 6) [34,65,40,18,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,18,132,256] 13 (by decide) (choices 1) [1,4] r19324 c19324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5803
  · exact u5804

def b19325 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 26 208 33 324 388 260), lower := (rows 35 67 44 26 208 33 64 128 256), losses := [] }

theorem u19325 : Upper (D 6) (R 6) [34,65,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19326 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 26 208 36 325 389 261), lower := (rows 35 67 44 26 208 36 64 128 256), losses := [] }

theorem u19326 : Upper (D 6) (R 6) [34,65,40,18,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19327 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 44 26 208 288 69 133 261), lower := (rows 35 67 44 26 208 288 64 128 256), losses := [] }

theorem u19327 : Upper (D 6) (R 6) [34,65,40,18,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19327 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19328 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 26 400 33 68 196 324), lower := (rows 35 67 44 26 400 33 64 128 256), losses := [] }

theorem u19328 : Upper (D 6) (R 6) [34,65,40,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19329 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 26 400 36 69 197 325), lower := (rows 35 67 44 26 400 36 64 128 256), losses := [] }

theorem u19329 : Upper (D 6) (R 6) [34,65,40,18,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19330 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 26 400 96 69 133 261), lower := (rows 35 67 44 26 400 96 64 128 256), losses := [] }

theorem u19330 : Upper (D 6) (R 6) [34,65,40,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19331 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 28 145 34 324 452 324), lower := (rows 35 67 44 28 145 34 64 128 256), losses := [] }

theorem u19331 : Upper (D 6) (R 6) [34,65,40,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19332 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 28 145 36 322 450 322), lower := (rows 35 67 44 28 145 36 64 128 256), losses := [] }

theorem u19332 : Upper (D 6) (R 6) [34,65,40,20,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19333 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 28 145 96 326 390 262), lower := (rows 35 67 44 28 145 96 64 128 256), losses := [] }

theorem u19333 : Upper (D 6) (R 6) [34,65,40,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19334 : Route 9 := (fun mask => (mask,id))

def c19334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19334 : Upper (D 6) (R 6) [34,65,40,20,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,129,256] 13 (by decide) (choices 1) [2,4] r19334 c19334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5805
  · exact u5806

def b19335 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 28 146 33 324 452 324), lower := (rows 35 67 44 28 146 33 64 128 256), losses := [] }

theorem u19335 : Upper (D 6) (R 6) [34,65,40,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19336 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 67 44 28 146 36 321 449 321), lower := (rows 35 67 44 28 146 36 64 128 256), losses := [] }

theorem u19336 : Upper (D 6) (R 6) [34,65,40,20,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19337 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 28 146 96 325 389 261), lower := (rows 35 67 44 28 146 96 64 128 256), losses := [] }

theorem u19337 : Upper (D 6) (R 6) [34,65,40,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19338 : Route 9 := (fun mask => (mask,id))

def c19338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19338 : Upper (D 6) (R 6) [34,65,40,20,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,130,256] 13 (by decide) (choices 1) [1,4] r19338 c19338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5807
  · exact u5808

def b19339 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 28 208 33 326 390 262), lower := (rows 35 67 44 28 208 33 64 128 256), losses := [] }

theorem u19339 : Upper (D 6) (R 6) [34,65,40,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19340 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 28 208 34 325 389 261), lower := (rows 35 67 44 28 208 34 64 128 256), losses := [] }

theorem u19340 : Upper (D 6) (R 6) [34,65,40,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19341 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 28 208 36 323 387 259), lower := (rows 35 67 44 28 208 36 64 128 256), losses := [] }

theorem u19341 : Upper (D 6) (R 6) [34,65,40,20,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19342 : Route 9 := (fun mask => (mask,id))

def c19342 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19342 : Upper (D 6) (R 6) [34,65,40,20,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,192,256] 13 (by decide) (choices 1) [1,2,4] r19342 c19342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5809
  · exact u5810
  · exact u5811

def b19343 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 28 400 33 70 198 326), lower := (rows 35 67 44 28 400 33 64 128 256), losses := [] }

theorem u19343 : Upper (D 6) (R 6) [34,65,40,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19344 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 28 400 34 69 197 325), lower := (rows 35 67 44 28 400 34 64 128 256), losses := [] }

theorem u19344 : Upper (D 6) (R 6) [34,65,40,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19345 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 28 400 36 67 195 323), lower := (rows 35 67 44 28 400 36 64 128 256), losses := [] }

theorem u19345 : Upper (D 6) (R 6) [34,65,40,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19346 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 28 400 96 71 135 263), lower := (rows 35 67 44 28 400 96 64 128 256), losses := [] }

theorem u19346 : Upper (D 6) (R 6) [34,65,40,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19347 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 145 34 324 388 260), lower := (rows 35 67 44 88 145 34 64 128 256), losses := [] }

theorem u19347 : Upper (D 6) (R 6) [34,65,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19348 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 88 145 36 326 390 262), lower := (rows 35 67 44 88 145 36 64 128 256), losses := [] }

theorem u19348 : Upper (D 6) (R 6) [34,65,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19349 : Route 9 := (fun mask => (mask,id))

def c19349 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19349 : Upper (D 6) (R 6) [34,65,40,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129,256] 13 (by decide) (choices 1) [2,4] r19349 c19349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5812
  · exact u5813

def b19350 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 146 33 324 388 260), lower := (rows 35 67 44 88 146 33 64 128 256), losses := [] }

theorem u19350 : Upper (D 6) (R 6) [34,65,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19351 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 88 146 36 325 389 261), lower := (rows 35 67 44 88 146 36 64 128 256), losses := [] }

theorem u19351 : Upper (D 6) (R 6) [34,65,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19352 : Route 9 := (fun mask => (mask,id))

def c19352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19352 : Upper (D 6) (R 6) [34,65,40,80,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,130,256] 13 (by decide) (choices 1) [1,4] r19352 c19352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5814
  · exact u5815

def b19353 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 148 33 326 390 262), lower := (rows 35 67 44 88 148 33 64 128 256), losses := [] }

theorem u19353 : Upper (D 6) (R 6) [34,65,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19354 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 148 34 325 389 261), lower := (rows 35 67 44 88 148 34 64 128 256), losses := [] }

theorem u19354 : Upper (D 6) (R 6) [34,65,40,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19355 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 88 148 36 323 387 259), lower := (rows 35 67 44 88 148 36 64 128 256), losses := [] }

theorem u19355 : Upper (D 6) (R 6) [34,65,40,80,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19356 : Route 9 := (fun mask => (mask,id))

def c19356 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19356 : Upper (D 6) (R 6) [34,65,40,80,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,132,256] 13 (by decide) (choices 1) [1,2,4] r19356 c19356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5816
  · exact u5817
  · exact u5818

def b19357 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 400 33 70 134 262), lower := (rows 35 67 44 88 400 33 64 128 256), losses := [] }

theorem u19357 : Upper (D 6) (R 6) [34,65,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19358 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 400 34 69 133 261), lower := (rows 35 67 44 88 400 34 64 128 256), losses := [] }

theorem u19358 : Upper (D 6) (R 6) [34,65,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19359 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 88 400 36 71 135 263), lower := (rows 35 67 44 88 400 36 64 128 256), losses := [] }

theorem u19359 : Upper (D 6) (R 6) [34,65,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19360 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 22 36 336 464 336), lower := (rows 35 67 44 137 22 36 64 128 256), losses := [] }

theorem u19360 : Upper (D 6) (R 6) [34,65,40,129,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19361 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 137 22 48 324 452 324), lower := (rows 35 67 44 137 22 48 64 128 256), losses := [] }

theorem u19361 : Upper (D 6) (R 6) [34,65,40,129,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19361 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19362 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 22 96 340 404 276), lower := (rows 35 67 44 137 22 96 64 128 256), losses := [] }

theorem u19362 : Upper (D 6) (R 6) [34,65,40,129,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19363 : Route 9 := (fun mask => (mask,id))

def c19363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19363 : Upper (D 6) (R 6) [34,65,40,129,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,6,256] 13 (by decide) (choices 1) [4,16] r19363 c19363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5819
  · exact u5820

def b19364 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 84 34 340 404 276), lower := (rows 35 67 44 137 84 34 64 128 256), losses := [] }

theorem u19364 : Upper (D 6) (R 6) [34,65,40,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19365 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 84 36 338 402 274), lower := (rows 35 67 44 137 84 36 64 128 256), losses := [] }

theorem u19365 : Upper (D 6) (R 6) [34,65,40,129,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19366 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 137 84 48 326 390 262), lower := (rows 35 67 44 137 84 48 64 128 256), losses := [] }

theorem u19366 : Upper (D 6) (R 6) [34,65,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19366 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19367 : Route 9 := (fun mask => (mask,id))

def c19367 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19367 : Upper (D 6) (R 6) [34,65,40,129,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,68,256] 13 (by decide) (choices 1) [2,4,16] r19367 c19367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5821
  · exact u5822
  · exact u5823

def b19368 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 274 36 84 212 340), lower := (rows 35 67 44 137 274 36 64 128 256), losses := [] }

theorem u19368 : Upper (D 6) (R 6) [34,65,40,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19369 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 137 274 48 68 196 324), lower := (rows 35 67 44 137 274 48 64 128 256), losses := [] }

theorem u19369 : Upper (D 6) (R 6) [34,65,40,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19369 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19370 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 274 96 84 148 276), lower := (rows 35 67 44 137 274 96 64 128 256), losses := [] }

theorem u19370 : Upper (D 6) (R 6) [34,65,40,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19371 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 276 34 84 212 340), lower := (rows 35 67 44 137 276 34 64 128 256), losses := [] }

theorem u19371 : Upper (D 6) (R 6) [34,65,40,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19372 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 276 36 82 210 338), lower := (rows 35 67 44 137 276 36 64 128 256), losses := [] }

theorem u19372 : Upper (D 6) (R 6) [34,65,40,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19373 : Route 9 := (fun mask => (mask,id))

def c19373 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19373 : Upper (D 6) (R 6) [34,65,40,129,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260,16] 13 (by decide) (choices 1) [2,4] r19373 c19373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5824
  · exact u5825

def b19374 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 276 96 86 150 278), lower := (rows 35 67 44 137 276 96 64 128 256), losses := [] }

theorem u19374 : Upper (D 6) (R 6) [34,65,40,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19375 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 336 34 84 148 276), lower := (rows 35 67 44 137 336 34 64 128 256), losses := [] }

theorem u19375 : Upper (D 6) (R 6) [34,65,40,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19376 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 336 36 86 150 278), lower := (rows 35 67 44 137 336 36 64 128 256), losses := [] }

theorem u19376 : Upper (D 6) (R 6) [34,65,40,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19377 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 137 336 48 70 134 262), lower := (rows 35 67 44 137 336 48 64 128 256), losses := [] }

theorem u19377 : Upper (D 6) (R 6) [34,65,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19377 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19378 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 67 44 138 21 36 336 464 336), lower := (rows 35 67 44 138 21 36 64 128 256), losses := [] }

theorem u19378 : Upper (D 6) (R 6) [34,65,40,130,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19379 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 44 138 21 48 324 452 324), lower := (rows 35 67 44 138 21 48 64 128 256), losses := [] }

theorem u19379 : Upper (D 6) (R 6) [34,65,40,130,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19379 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19379
end Delivery.IrregularNine14.P06
