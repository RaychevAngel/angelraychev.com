import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0111
import IrregularNine14P06C0112

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22320 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 73 280 48 70 134 262), lower := (rows 35 131 100 73 280 48 64 128 256), losses := [] }

theorem u22320 : Upper (D 6) (R 6) [34,129,96,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22320 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22321 : Route 9 := (fun mask => (mask,id))

def c22321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22321 : Upper (D 6) (R 6) [34,129,96,66,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,257,4] 13 (by decide) (choices 1) [4,8,16] r22321 c22321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6680
  · exact u6681
  · exact u6682

def b22322 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 74 273 40 84 148 276), lower := (rows 35 131 100 74 273 40 64 128 256), losses := [] }

theorem u22322 : Upper (D 6) (R 6) [34,129,96,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22322 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22323 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 100 74 273 48 76 140 268), lower := (rows 35 131 100 74 273 48 64 128 256), losses := [] }

theorem u22323 : Upper (D 6) (R 6) [34,129,96,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22323 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22324 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 74 276 33 92 156 284), lower := (rows 35 131 100 74 276 33 64 128 256), losses := [] }

theorem u22324 : Upper (D 6) (R 6) [34,129,96,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22325 : Route 9 := (fun mask => (mask,id))

def c22325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22325 : Upper (D 6) (R 6) [34,129,96,66,260,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,260,4] 13 (by decide) (choices 1) [1,8,16] r22325 c22325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6683
  · exact u6684
  · exact u6685

def b22326 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 74 276 40 85 149 277), lower := (rows 35 131 100 74 276 40 64 128 256), losses := [] }

theorem u22326 : Upper (D 6) (R 6) [34,129,96,66,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22326 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22327 : Route 9 := (fun mask => (mask,id))

def c22327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22327 : Upper (D 6) (R 6) [34,129,96,66,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,260,16] 13 (by decide) (choices 1) [1,4,8] r22327 c22327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6686
  · exact u6687
  · exact u6688

def b22328 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 74 280 33 84 148 276), lower := (rows 35 131 100 74 280 33 64 128 256), losses := [] }

theorem u22328 : Upper (D 6) (R 6) [34,129,96,66,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22329 : Route 9 := (fun mask => (mask,id))

def c22329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22329 : Upper (D 6) (R 6) [34,129,96,66,264,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,264,4] 13 (by decide) (choices 1) [1,4,16] r22329 c22329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6689
  · exact u6690
  · exact u6691

def b22330 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 74 280 48 69 133 261), lower := (rows 35 131 100 74 280 48 64 128 256), losses := [] }

theorem u22330 : Upper (D 6) (R 6) [34,129,96,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22330 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22331 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 88 273 34 76 140 268), lower := (rows 35 131 100 88 273 34 64 128 256), losses := [] }

theorem u22331 : Upper (D 6) (R 6) [34,129,96,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22332 : Route 9 := (fun mask => (mask,id))

def c22332 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22332 : Upper (D 6) (R 6) [34,129,96,80,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80,257,4] 13 (by decide) (choices 1) [2,4,8] r22332 c22332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6692
  · exact u6693
  · exact u6694

def b22333 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 88 273 40 70 134 262), lower := (rows 35 131 100 88 273 40 64 128 256), losses := [] }

theorem u22333 : Upper (D 6) (R 6) [34,129,96,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22333 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22334 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 88 274 33 76 140 268), lower := (rows 35 131 100 88 274 33 64 128 256), losses := [] }

theorem u22334 : Upper (D 6) (R 6) [34,129,96,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22335 : Route 9 := (fun mask => (mask,id))

def c22335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22335 : Upper (D 6) (R 6) [34,129,96,80,258,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80,258,4] 13 (by decide) (choices 1) [1,4,8] r22335 c22335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6695
  · exact u6696
  · exact u6697

def b22336 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 88 274 40 69 133 261), lower := (rows 35 131 100 88 274 40 64 128 256), losses := [] }

theorem u22336 : Upper (D 6) (R 6) [34,129,96,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22336 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22337 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 88 276 33 78 142 270), lower := (rows 35 131 100 88 276 33 64 128 256), losses := [] }

theorem u22337 : Upper (D 6) (R 6) [34,129,96,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22338 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 88 276 34 77 141 269), lower := (rows 35 131 100 88 276 34 64 128 256), losses := [] }

theorem u22338 : Upper (D 6) (R 6) [34,129,96,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22339 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 88 276 36 75 139 267), lower := (rows 35 131 100 88 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 136 264), good := (rows 35 131 36 443 308 36 0 128 256) }] }

theorem u22339 : Upper (D 6) (R 6) [34,129,96,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22340 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 88 276 40 71 135 263), lower := (rows 35 131 100 88 276 40 64 128 256), losses := [] }

theorem u22340 : Upper (D 6) (R 6) [34,129,96,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22340 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22341 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 88 280 33 70 134 262), lower := (rows 35 131 100 88 280 33 64 128 256), losses := [] }

theorem u22341 : Upper (D 6) (R 6) [34,129,96,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22342 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 88 280 34 69 133 261), lower := (rows 35 131 100 88 280 34 64 128 256), losses := [] }

theorem u22342 : Upper (D 6) (R 6) [34,129,96,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22343 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 100 88 280 36 71 135 263), lower := (rows 35 131 100 88 280 36 64 128 256), losses := [] }

theorem u22343 : Upper (D 6) (R 6) [34,129,96,80,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22344 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 14 52 40 80 208 336), lower := (rows 35 131 261 14 52 40 64 128 256), losses := [] }

theorem u22344 : Upper (D 6) (R 6) [34,129,257,6,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22344 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22345 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 14 52 48 72 200 328), lower := (rows 35 131 261 14 52 48 64 128 256), losses := [] }

theorem u22345 : Upper (D 6) (R 6) [34,129,257,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22345 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22346 : Route 9 := (fun mask => (mask,id))

def c22346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22346 : Upper (D 6) (R 6) [34,129,257,6,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,36,64] 13 (by decide) (choices 1) [8,16] r22346 c22346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6698
  · exact u6699

def b22347 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 261 14 56 36 80 208 336), lower := (rows 35 131 261 14 56 36 64 128 256), losses := [] }

theorem u22347 : Upper (D 6) (R 6) [34,129,257,6,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22348 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 261 14 56 48 68 196 324), lower := (rows 35 131 261 14 56 48 64 128 256), losses := [] }

theorem u22348 : Upper (D 6) (R 6) [34,129,257,6,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22348 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22349 : Route 9 := (fun mask => (mask,id))

def c22349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22349 : Upper (D 6) (R 6) [34,129,257,6,40,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,40,64] 13 (by decide) (choices 1) [4,16] r22349 c22349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6700
  · exact u6701

def b22350 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 14 84 40 112 240 368), lower := (rows 35 131 261 14 84 40 64 128 256), losses := [] }

theorem u22350 : Upper (D 6) (R 6) [34,129,257,6,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22350 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22351 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 14 84 48 104 232 360), lower := (rows 35 131 261 14 84 48 64 128 256), losses := [] }

theorem u22351 : Upper (D 6) (R 6) [34,129,257,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22351 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22352 : Route 9 := (fun mask => (mask,id))

def c22352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22352 : Upper (D 6) (R 6) [34,129,257,6,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,68,64] 13 (by decide) (choices 1) [8,16,32] r22352 c22352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6702
  · exact u6703
  · exact u6704

def b22353 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 261 14 88 36 112 240 368), lower := (rows 35 131 261 14 88 36 64 128 256), losses := [] }

theorem u22353 : Upper (D 6) (R 6) [34,129,257,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22354 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 14 88 48 100 228 356), lower := (rows 35 131 261 14 88 48 64 128 256), losses := [] }

theorem u22354 : Upper (D 6) (R 6) [34,129,257,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22354 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22355 : Route 9 := (fun mask => (mask,id))

def c22355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22355 : Upper (D 6) (R 6) [34,129,257,6,72,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,72,64] 13 (by decide) (choices 1) [4,16,32] r22355 c22355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6705
  · exact u6706
  · exact u6707

def b22356 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 261 14 112 36 88 216 344), lower := (rows 35 131 261 14 112 36 64 128 256), losses := [] }

theorem u22356 : Upper (D 6) (R 6) [34,129,257,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22357 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 14 112 40 84 212 340), lower := (rows 35 131 261 14 112 40 64 128 256), losses := [] }

theorem u22357 : Upper (D 6) (R 6) [34,129,257,6,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22357 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22358 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 261 14 112 48 76 204 332), lower := (rows 35 131 261 14 112 48 64 128 256), losses := [] }

theorem u22358 : Upper (D 6) (R 6) [34,129,257,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22358 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22359 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 14 112 96 92 156 284), lower := (rows 35 131 261 14 112 96 64 128 256), losses := [] }

theorem u22359 : Upper (D 6) (R 6) [34,129,257,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22360 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 131 261 26 28 36 96 224 352), lower := (rows 35 131 261 26 28 36 64 128 256), losses := [] }

theorem u22360 : Upper (D 6) (R 6) [34,129,257,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22361 : Route 9 := (fun mask => (mask,id))

def c22361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22361 : Upper (D 6) (R 6) [34,129,257,18,12,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,12,64] 13 (by decide) (choices 1) [4,32] r22361 c22361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6708
  · exact u6709

def b22362 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 261 26 52 36 72 200 328), lower := (rows 35 131 261 26 52 36 64 128 256), losses := [] }

theorem u22362 : Upper (D 6) (R 6) [34,129,257,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22363 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 26 52 40 68 196 324), lower := (rows 35 131 261 26 52 40 64 128 256), losses := [] }

theorem u22363 : Upper (D 6) (R 6) [34,129,257,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22363 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22364 : Route 9 := (fun mask => (mask,id))

def c22364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22364 : Upper (D 6) (R 6) [34,129,257,18,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,36,64] 13 (by decide) (choices 1) [4,8] r22364 c22364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6710
  · exact u6711

def b22365 : PairBound 9 := { available := 104, camps := [], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 131 261 26 84 36 104 232 360), lower := (rows 35 131 261 26 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 52 52 77 141 269), good := (rows 506 458 508 506 500 500 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 131 293 59 52 36 0 128 256) }] }

theorem u22365 : Upper (D 6) (R 6) [34,129,257,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22366 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 26 84 40 100 228 356), lower := (rows 35 131 261 26 84 40 64 128 256), losses := [] }

theorem u22366 : Upper (D 6) (R 6) [34,129,257,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22366 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22367 : Route 9 := (fun mask => (mask,id))

def c22367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22367 : Upper (D 6) (R 6) [34,129,257,18,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,68,64] 13 (by decide) (choices 1) [4,8,32] r22367 c22367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6712
  · exact u6713
  · exact u6714

def b22368 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 35 131 261 26 88 36 100 228 356), lower := (rows 35 131 261 26 88 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 21 36 100 164 292), good := (rows 506 154 508 26 88 500 64 128 256) }] }

theorem u22368 : Upper (D 6) (R 6) [34,129,257,18,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22369 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 26 88 96 100 164 292), lower := (rows 35 131 261 26 88 96 64 128 256), losses := [] }

theorem u22369 : Upper (D 6) (R 6) [34,129,257,18,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22370 : Route 9 := (fun mask => (mask,id))

def c22370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22370 : Upper (D 6) (R 6) [34,129,257,18,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,96,4] 13 (by decide) (choices 1) [4,8] r22370 c22370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6715
  · exact u6716

def b22371 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 261 26 112 40 68 196 324), lower := (rows 35 131 261 26 112 40 64 128 256), losses := [] }

theorem u22371 : Upper (D 6) (R 6) [34,129,257,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22371 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22372 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 261 26 112 96 76 140 268), lower := (rows 35 131 261 26 112 96 64 128 256), losses := [] }

theorem u22372 : Upper (D 6) (R 6) [34,129,257,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22373 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 28 56 34 68 196 324), lower := (rows 35 131 261 28 56 34 64 128 256), losses := [] }

theorem u22373 : Upper (D 6) (R 6) [34,129,257,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22374 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 261 28 56 36 66 194 322), lower := (rows 35 131 261 28 56 36 64 128 256), losses := [] }

theorem u22374 : Upper (D 6) (R 6) [34,129,257,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22375 : Route 9 := (fun mask => (mask,id))

def c22375 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22375 : Upper (D 6) (R 6) [34,129,257,20,40,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,40,64] 13 (by decide) (choices 1) [2,4] r22375 c22375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6717
  · exact u6718

def r22376 : Route 9 := (fun mask => (mask,id))

def c22376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22376 : Upper (D 6) (R 6) [34,129,257,20,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,66,4] 13 (by decide) (choices 1) [8,32] r22376 c22376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6719
  · exact u6720

def b22377 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 261 28 82 40 100 228 356), lower := (rows 35 131 261 28 82 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 56 89 153 281), good := (rows 485 453 453 508 508 488 64 128 256) }] }

theorem u22377 : Upper (D 6) (R 6) [34,129,257,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22377 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22378 : Route 9 := (fun mask => (mask,id))

def c22378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22378 : Upper (D 6) (R 6) [34,129,257,20,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,66,64] 13 (by decide) (choices 1) [4,8,32] r22378 c22378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6721
  · exact u6722
  · exact u6723

def b22379 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 28 88 34 100 228 356), lower := (rows 35 131 261 28 88 34 64 128 256), losses := [] }

theorem u22379 : Upper (D 6) (R 6) [34,129,257,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22379
end Delivery.IrregularNine14.P06
