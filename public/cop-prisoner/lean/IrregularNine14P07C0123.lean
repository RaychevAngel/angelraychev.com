import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7380 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 266 81 48 96 129 385), lower := (rows 37 74 134 266 81 48 96 128 256), losses := [] }

theorem u7380 : Upper (D 7) (R 7) [36,72,130,258,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7380 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7381 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 298, targets := 128 }], pairs := [(0,1),(1,7),(4,1)], upper := (rows 37 74 134 266 81 48 192 161 289), lower := (rows 37 74 134 266 81 48 192 128 256), losses := [] }

theorem u7381 : Upper (D 7) (R 7) [36,72,130,258,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7381 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7382 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 134 296 81 33 66 144 400), lower := (rows 37 74 134 296 81 33 66 128 256), losses := [] }

theorem u7382 : Upper (D 7) (R 7) [36,72,130,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7383 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 74 134 296 81 33 80 130 386), lower := (rows 37 74 134 296 81 33 80 128 256), losses := [] }

theorem u7383 : Upper (D 7) (R 7) [36,72,130,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7383 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7384 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 74 134 296 81 33 192 146 274), lower := (rows 37 74 134 296 81 33 192 128 256), losses := [] }

theorem u7384 : Upper (D 7) (R 7) [36,72,130,288,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7385 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 74 134 296 81 48 65 130 386), lower := (rows 37 74 134 296 81 48 65 128 256), losses := [] }

theorem u7385 : Upper (D 7) (R 7) [36,72,130,288,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7385 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7386 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 134 296 81 48 66 129 385), lower := (rows 37 74 134 296 81 48 66 128 256), losses := [] }

theorem u7386 : Upper (D 7) (R 7) [36,72,130,288,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7386 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7387 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 298, targets := 128 }], pairs := [(0,1),(1,7),(4,1)], upper := (rows 37 74 134 296 81 48 192 131 259), lower := (rows 37 74 134 296 81 48 192 128 256), losses := [] }

theorem u7387 : Upper (D 7) (R 7) [36,72,130,288,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7387 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7388 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 134 296 208 33 65 146 274), lower := (rows 37 74 134 296 208 33 65 128 256), losses := [] }

theorem u7388 : Upper (D 7) (R 7) [36,72,130,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7389 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 2, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 74 134 296 208 33 66 145 273), lower := (rows 37 74 134 296 208 33 66 128 256), losses := [] }

theorem u7389 : Upper (D 7) (R 7) [36,72,130,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7390 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 134 296 208 33 80 131 259), lower := (rows 37 74 134 296 208 33 80 128 256), losses := [] }

theorem u7390 : Upper (D 7) (R 7) [36,72,130,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7390 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7391 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 113, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 134 296 208 48 65 131 259), lower := (rows 37 74 134 296 208 48 65 128 256), losses := [] }

theorem u7391 : Upper (D 7) (R 7) [36,72,130,288,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7391 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7392 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 134 296 208 48 66 129 257), lower := (rows 37 74 134 296 208 48 66 128 256), losses := [] }

theorem u7392 : Upper (D 7) (R 7) [36,72,130,288,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7393 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 37 74 134 392 81 48 65 162 290), lower := (rows 37 74 134 392 81 48 65 128 256), losses := [] }

theorem u7393 : Upper (D 7) (R 7) [36,72,130,384,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7393 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7394 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 134 392 81 48 66 161 289), lower := (rows 37 74 134 392 81 48 66 128 256), losses := [] }

theorem u7394 : Upper (D 7) (R 7) [36,72,130,384,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7394 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7395 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 392 81 48 96 131 259), lower := (rows 37 74 134 392 81 48 96 128 256), losses := [] }

theorem u7395 : Upper (D 7) (R 7) [36,72,130,384,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7395 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7396 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 105, targets := 2 },{ cop := 4, region := 388, targets := 65 }], pairs := [(0,1),(2,0),(2,6),(3,1)], upper := (rows 37 74 148 168 19 96 65 386 258), lower := (rows 37 74 148 168 19 96 65 128 256), losses := [] }

theorem u7396 : Upper (D 7) (R 7) [36,72,144,160,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7397 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,6)], upper := (rows 37 74 148 168 19 96 66 385 257), lower := (rows 37 74 148 168 19 96 66 128 256), losses := [] }

theorem u7397 : Upper (D 7) (R 7) [36,72,144,160,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7398 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 132, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(0,7),(2,5),(2,6)], upper := (rows 37 74 148 168 19 96 320 131 259), lower := (rows 37 74 148 168 19 96 320 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 375 340 0 272), good := (rows 101 106 373 40 371 96 352 0 352) }] }

theorem u7398 : Upper (D 7) (R 7) [36,72,144,160,3,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7398 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7399 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 426, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 37 74 148 168 19 288 65 194 322), lower := (rows 37 74 148 168 19 288 65 128 256), losses := [] }

theorem u7399 : Upper (D 7) (R 7) [36,72,144,160,3,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7399 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7400 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 148 168 19 288 66 193 321), lower := (rows 37 74 148 168 19 288 66 128 256), losses := [] }

theorem u7400 : Upper (D 7) (R 7) [36,72,144,160,3,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7400 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7401 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 74 148 168 81 34 65 386 258), lower := (rows 37 74 148 168 81 34 65 128 256), losses := [] }

theorem u7401 : Upper (D 7) (R 7) [36,72,144,160,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7402 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 388, targets := 98 },{ cop := 0, region := 392, targets := 2 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 74 148 168 81 34 66 385 257), lower := (rows 37 74 148 168 81 34 66 128 256), losses := [] }

theorem u7402 : Upper (D 7) (R 7) [36,72,144,160,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7403 : Route 9 := (fun mask => (mask,id))

def c7403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7403 : Upper (D 7) (R 7) [36,72,144,160,65,2,256] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,65,2,256] 13 (by decide) (choices 1) [1,2] r7403 c7403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u544
  · exact u545

def b7404 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 74 148 168 81 288 65 130 258), lower := (rows 37 74 148 168 81 288 65 128 256), losses := [] }

theorem u7404 : Upper (D 7) (R 7) [36,72,144,160,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7404 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7405 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 148 168 81 288 66 131 259), lower := (rows 37 74 148 168 81 288 66 128 256), losses := [] }

theorem u7405 : Upper (D 7) (R 7) [36,72,144,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7405 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7406 : Route 9 := (fun mask => (mask,id))

def c7406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7406 : Upper (D 7) (R 7) [36,72,144,160,257,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,257,2,1] 13 (by decide) (choices 1) [2,64] r7406 c7406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u546
  · exact u547

def b7407 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 3, region := 66, targets := 128 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 148 168 273 34 66 193 321), lower := (rows 37 74 148 168 273 34 66 128 256), losses := [] }

theorem u7407 : Upper (D 7) (R 7) [36,72,144,160,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7408 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 105, targets := 2 },{ cop := 5, region := 138, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(3,1)], upper := (rows 37 74 148 168 273 96 65 130 258), lower := (rows 37 74 148 168 273 96 65 128 256), losses := [] }

theorem u7408 : Upper (D 7) (R 7) [36,72,144,160,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7409 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 3, region := 66, targets := 128 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 148 168 273 96 66 131 259), lower := (rows 37 74 148 168 273 96 66 128 256), losses := [] }

theorem u7409 : Upper (D 7) (R 7) [36,72,144,160,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7410 : Route 9 := (fun mask => (mask,id))

def c7410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7410 : Upper (D 7) (R 7) [36,72,144,160,258,64,1] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,258,64,1] 13 (by decide) (choices 1) [1,2] r7410 c7410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u548
  · exact u549

def b7411 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,6)], upper := (rows 37 74 148 168 274 96 66 129 257), lower := (rows 37 74 148 168 274 96 66 128 256), losses := [] }

theorem u7411 : Upper (D 7) (R 7) [36,72,144,160,258,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7412 : Route 9 := (fun mask => (mask,id))

def c7412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7412 : Upper (D 7) (R 7) [36,72,144,160,320,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,320,2,1] 13 (by decide) (choices 1) [1,2] r7412 c7412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u550
  · exact u551

def b7413 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,6)], upper := (rows 37 74 148 168 336 34 66 129 257), lower := (rows 37 74 148 168 336 34 66 128 256), losses := [] }

theorem u7413 : Upper (D 7) (R 7) [36,72,144,160,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7414 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(4,5)], upper := (rows 37 74 148 265 19 96 66 160 416), lower := (rows 37 74 148 265 19 96 66 128 256), losses := [] }

theorem u7414 : Upper (D 7) (R 7) [36,72,144,257,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7415 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 37 74 148 265 19 96 96 130 386), lower := (rows 37 74 148 265 19 96 96 128 256), losses := [] }

theorem u7415 : Upper (D 7) (R 7) [36,72,144,257,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7416 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 97, targets := 2 },{ cop := 3, region := 226, targets := 1 },{ cop := 4, region := 228, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(3,7)], upper := (rows 37 74 148 265 19 96 192 162 290), lower := (rows 37 74 148 265 19 96 192 128 256), losses := [{ target := 7, region := (rows 1 2 4 24 16 98 64 0 274), good := (rows 37 362 284 265 315 96 96 0 256) }] }

theorem u7416 : Upper (D 7) (R 7) [36,72,144,257,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7417 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(4,5)], upper := (rows 37 74 148 265 81 34 66 160 416), lower := (rows 37 74 148 265 81 34 66 128 256), losses := [] }

theorem u7417 : Upper (D 7) (R 7) [36,72,144,257,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7418 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 74 148 265 81 34 96 130 386), lower := (rows 37 74 148 265 81 34 96 128 256), losses := [] }

theorem u7418 : Upper (D 7) (R 7) [36,72,144,257,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7419 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 37 74 148 265 81 34 192 162 290), lower := (rows 37 74 148 265 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 196 128 256), good := (rows 117 72 212 281 81 32 192 192 256) }] }

theorem u7419 : Upper (D 7) (R 7) [36,72,144,257,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7420 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 4, region := 132, targets := 65 }], pairs := [(0,1),(0,7),(2,0),(2,6)], upper := (rows 37 74 148 296 19 96 65 130 386), lower := (rows 37 74 148 296 19 96 65 128 256), losses := [] }

theorem u7420 : Upper (D 7) (R 7) [36,72,144,288,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7421 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 148 296 19 96 66 129 385), lower := (rows 37 74 148 296 19 96 66 128 256), losses := [] }

theorem u7421 : Upper (D 7) (R 7) [36,72,144,288,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7422 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 97, targets := 2 },{ cop := 4, region := 132, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(0,1),(2,5),(2,6),(3,7)], upper := (rows 37 74 148 296 19 96 192 131 259), lower := (rows 37 74 148 296 19 96 192 128 256), losses := [{ target := 7, region := (rows 1 2 4 24 16 98 64 0 272), good := (rows 37 106 284 296 315 96 96 0 256) }] }

theorem u7422 : Upper (D 7) (R 7) [36,72,144,288,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7423 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 74 148 296 81 34 65 130 386), lower := (rows 37 74 148 296 81 34 65 128 256), losses := [] }

theorem u7423 : Upper (D 7) (R 7) [36,72,144,288,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7424 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 148 296 81 34 66 129 385), lower := (rows 37 74 148 296 81 34 66 128 256), losses := [] }

theorem u7424 : Upper (D 7) (R 7) [36,72,144,288,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7425 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 298, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 37 74 148 296 81 34 192 131 259), lower := (rows 37 74 148 296 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 196 128 256), good := (rows 117 72 212 296 81 32 192 192 256) },{ target := 5, region := (rows 1 2 4 8 17 0 196 128 256), good := (rows 85 74 212 264 81 2 192 192 256) }] }

theorem u7425 : Upper (D 7) (R 7) [36,72,144,288,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7426 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 394, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 148 392 19 96 65 162 290), lower := (rows 37 74 148 392 19 96 65 128 256), losses := [] }

theorem u7426 : Upper (D 7) (R 7) [36,72,144,384,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7427 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 37 74 148 392 19 96 66 161 289), lower := (rows 37 74 148 392 19 96 66 128 256), losses := [] }

theorem u7427 : Upper (D 7) (R 7) [36,72,144,384,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7428 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 37 74 148 392 19 96 96 131 259), lower := (rows 37 74 148 392 19 96 96 128 256), losses := [] }

theorem u7428 : Upper (D 7) (R 7) [36,72,144,384,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7429 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 74 148 392 81 34 65 162 290), lower := (rows 37 74 148 392 81 34 65 128 256), losses := [] }

theorem u7429 : Upper (D 7) (R 7) [36,72,144,384,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7430 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 37 74 148 392 81 34 66 161 289), lower := (rows 37 74 148 392 81 34 66 128 256), losses := [] }

theorem u7430 : Upper (D 7) (R 7) [36,72,144,384,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7431 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 74 148 392 81 34 96 131 259), lower := (rows 37 74 148 392 81 34 96 128 256), losses := [] }

theorem u7431 : Upper (D 7) (R 7) [36,72,144,384,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7432 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 74 196 168 19 33 80 386 258), lower := (rows 37 74 196 168 19 33 80 128 256), losses := [] }

theorem u7432 : Upper (D 7) (R 7) [36,72,192,160,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7432 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7433 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 74 196 168 19 33 320 146 274), lower := (rows 37 74 196 168 19 33 320 128 256), losses := [] }

theorem u7433 : Upper (D 7) (R 7) [36,72,192,160,3,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7433 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7434 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 2, region := 42, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 74 196 168 19 34 80 385 257), lower := (rows 37 74 196 168 19 34 80 128 256), losses := [] }

theorem u7434 : Upper (D 7) (R 7) [36,72,192,160,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7434 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7435 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 4, region := 452, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 74 196 168 19 34 320 145 273), lower := (rows 37 74 196 168 19 34 320 128 256), losses := [] }

theorem u7435 : Upper (D 7) (R 7) [36,72,192,160,3,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7435 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7436 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 452, targets := 32 },{ cop := 4, region := 168, targets := 64 }], pairs := [(2,5),(3,6)], upper := (rows 37 74 196 168 19 48 320 131 259), lower := (rows 37 74 196 168 19 48 320 128 256), losses := [] }

theorem u7436 : Upper (D 7) (R 7) [36,72,192,160,3,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7436 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7437 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 196 168 273 34 65 146 274), lower := (rows 37 74 196 168 273 34 65 128 256), losses := [] }

theorem u7437 : Upper (D 7) (R 7) [36,72,192,160,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7438 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 196 168 273 34 66 145 273), lower := (rows 37 74 196 168 273 34 66 128 256), losses := [] }

theorem u7438 : Upper (D 7) (R 7) [36,72,192,160,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7439 : Route 9 := (fun mask => (mask,id))

def c7439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7439 : Upper (D 7) (R 7) [36,72,192,160,257,2,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,257,2,16] 13 (by decide) (choices 1) [1,2] r7439 c7439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u552
  · exact u553

#print axioms u7439
end Delivery.IrregularNine14.P07
