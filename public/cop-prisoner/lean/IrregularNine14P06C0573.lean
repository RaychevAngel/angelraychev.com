import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0300
import IrregularNine14P06C0301

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34380 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 25 22 101 101 229 357), lower := (rows 11 162 324 25 22 32 64 128 256), losses := [] }

theorem u34380 : Upper (D 6) (R 6) [10,160,320,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34381 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 324 25 49 102 70 198 326), lower := (rows 11 162 324 25 49 32 64 128 256), losses := [] }

theorem u34381 : Upper (D 6) (R 6) [10,160,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34382 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 324 25 50 101 69 197 325), lower := (rows 11 162 324 25 50 32 64 128 256), losses := [] }

theorem u34382 : Upper (D 6) (R 6) [10,160,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34383 : Route 9 := (fun mask => (mask,id))

def c34383 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34383 : Upper (D 6) (R 6) [10,160,320,17,36] 13 := by
  apply FastRouting.sound _ _ [10,160,320,17,36] 13 (by decide) (choices 1) [1,2,4,64] r34383 c34383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18000
  · exact u18001
  · exact u18002
  · exact u18003

def b34384 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 324 25 81 38 102 166 294), lower := (rows 11 162 324 25 81 32 64 128 256), losses := [] }

theorem u34384 : Upper (D 6) (R 6) [10,160,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34385 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 25 82 37 101 165 293), lower := (rows 11 162 324 25 82 32 64 128 256), losses := [] }

theorem u34385 : Upper (D 6) (R 6) [10,160,320,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34386 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 324 25 84 39 103 167 295), lower := (rows 11 162 324 25 84 32 64 128 256), losses := [] }

theorem u34386 : Upper (D 6) (R 6) [10,160,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34387 : Route 9 := (fun mask => (mask,id))

def c34387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34387 : Upper (D 6) (R 6) [10,160,320,17,96] 13 := by
  apply FastRouting.sound _ _ [10,160,320,17,96] 13 (by decide) (choices 1) [1,2,4] r34387 c34387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18004
  · exact u18005
  · exact u18006

def b34388 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 324 28 19 101 101 229 357), lower := (rows 11 162 324 28 19 32 64 128 256), losses := [] }

theorem u34388 : Upper (D 6) (R 6) [10,160,320,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34389 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 324 28 21 99 99 227 355), lower := (rows 11 162 324 28 21 32 64 128 256), losses := [] }

theorem u34389 : Upper (D 6) (R 6) [10,160,320,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34390 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 324 28 22 97 97 225 353), lower := (rows 11 162 324 28 22 32 64 128 256), losses := [] }

theorem u34390 : Upper (D 6) (R 6) [10,160,320,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34391 : Route 9 := (fun mask => (mask,id))

def c34391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34391 : Upper (D 6) (R 6) [10,160,320,20,33] 13 := by
  apply FastRouting.sound _ _ [10,160,320,20,33] 13 (by decide) (choices 1) [1,2,4,64] r34391 c34391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18007
  · exact u18008
  · exact u18009
  · exact u18010

def b34392 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 324 28 50 101 69 197 325), lower := (rows 11 162 324 28 50 32 64 128 256), losses := [] }

theorem u34392 : Upper (D 6) (R 6) [10,160,320,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34393 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 324 28 52 99 67 195 323), lower := (rows 11 162 324 28 52 32 64 128 256), losses := [] }

theorem u34393 : Upper (D 6) (R 6) [10,160,320,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34394 : Route 9 := (fun mask => (mask,id))

def c34394 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34394 : Upper (D 6) (R 6) [10,160,320,20,65] 13 := by
  apply FastRouting.sound _ _ [10,160,320,20,65] 13 (by decide) (choices 1) [1,2,4] r34394 c34394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18011
  · exact u18012
  · exact u18013

def b34395 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 324 28 82 37 101 165 293), lower := (rows 11 162 324 28 82 32 64 128 256), losses := [] }

theorem u34395 : Upper (D 6) (R 6) [10,160,320,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34396 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 324 28 84 35 99 163 291), lower := (rows 11 162 324 28 84 32 64 128 256), losses := [] }

theorem u34396 : Upper (D 6) (R 6) [10,160,320,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34397 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 162 324 28 112 39 71 135 263), lower := (rows 11 162 324 28 112 32 64 128 256), losses := [] }

theorem u34397 : Upper (D 6) (R 6) [10,160,320,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34398 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 324 44 19 117 85 213 341), lower := (rows 11 162 324 44 19 32 64 128 256), losses := [] }

theorem u34398 : Upper (D 6) (R 6) [10,160,320,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34399 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 162 324 44 21 115 83 211 339), lower := (rows 11 162 324 44 21 32 64 128 256), losses := [] }

theorem u34399 : Upper (D 6) (R 6) [10,160,320,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34400 : Route 9 := (fun mask => (mask,id))

def c34400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34400 : Upper (D 6) (R 6) [10,160,320,36,6] 13 := by
  apply FastRouting.sound _ _ [10,160,320,36,6] 13 (by decide) (choices 1) [1,16,64] r34400 c34400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18014
  · exact u18015
  · exact u18016

def r34401 : Route 9 := (fun mask => (mask,id))

def c34401 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34401 : Upper (D 6) (R 6) [10,160,320,36,65] 13 := by
  apply FastRouting.sound _ _ [10,160,320,36,65] 13 (by decide) (choices 1) [1,2,4,16] r34401 c34401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18017
  · exact u18018
  · exact u18019
  · exact u18020

def r34402 : Route 9 := (fun mask => (mask,id))

def c34402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34402 : Upper (D 6) (R 6) [10,160,320,36,66] 13 := by
  apply FastRouting.sound _ _ [10,160,320,36,66] 13 (by decide) (choices 1) [1,4,16] r34402 c34402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18021
  · exact u18022
  · exact u18023

def b34403 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 324 44 84 51 83 147 275), lower := (rows 11 162 324 44 84 32 64 128 256), losses := [] }

theorem u34403 : Upper (D 6) (R 6) [10,160,320,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34404 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 324 56 19 101 69 197 325), lower := (rows 11 162 324 56 19 32 64 128 256), losses := [] }

theorem u34404 : Upper (D 6) (R 6) [10,160,320,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34405 : Route 9 := (fun mask => (mask,id))

def c34405 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34405 : Upper (D 6) (R 6) [10,160,320,48,5] 13 := by
  apply FastRouting.sound _ _ [10,160,320,48,5] 13 (by decide) (choices 1) [1,2,4,64] r34405 c34405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18024
  · exact u18025
  · exact u18026
  · exact u18027

def b34406 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 324 56 22 101 69 197 325), lower := (rows 11 162 324 56 22 32 64 128 256), losses := [] }

theorem u34406 : Upper (D 6) (R 6) [10,160,320,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34407 : Route 9 := (fun mask => (mask,id))

def c34407 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34407 : Upper (D 6) (R 6) [10,160,320,48,65] 13 := by
  apply FastRouting.sound _ _ [10,160,320,48,65] 13 (by decide) (choices 1) [1,2,4] r34407 c34407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18028
  · exact u18029
  · exact u18030

def b34408 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 324 56 82 37 69 133 261), lower := (rows 11 162 324 56 82 32 64 128 256), losses := [] }

theorem u34408 : Upper (D 6) (R 6) [10,160,320,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34409 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 324 56 84 39 71 135 263), lower := (rows 11 162 324 56 84 32 64 128 256), losses := [] }

theorem u34409 : Upper (D 6) (R 6) [10,160,320,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34410 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 324 73 19 52 116 180 308), lower := (rows 11 162 324 73 19 32 64 128 256), losses := [] }

theorem u34410 : Upper (D 6) (R 6) [10,160,320,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34411 : PairBound 9 := { available := 54, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 324 73 21 54 118 182 310), lower := (rows 11 162 324 73 21 32 64 128 256), losses := [] }

theorem u34411 : Upper (D 6) (R 6) [10,160,320,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34412 : Route 9 := (fun mask => (mask,id))

def c34412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34412 : Upper (D 6) (R 6) [10,160,320,65,6] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65,6] 13 (by decide) (choices 1) [1,4,16] r34412 c34412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18031
  · exact u18032
  · exact u18033

def r34413 : Route 9 := (fun mask => (mask,id))

def c34413 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34413 : Upper (D 6) (R 6) [10,160,320,65,33] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65,33] 13 (by decide) (choices 1) [2,4,16] r34413 c34413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18034
  · exact u18035
  · exact u18036

def b34414 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 324 73 50 53 85 149 277), lower := (rows 11 162 324 73 50 32 64 128 256), losses := [] }

theorem u34414 : Upper (D 6) (R 6) [10,160,320,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34415 : Route 9 := (fun mask => (mask,id))

def c34415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34415 : Upper (D 6) (R 6) [10,160,320,65,36] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65,36] 13 (by decide) (choices 1) [1,2,4,16] r34415 c34415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18037
  · exact u18038
  · exact u18039
  · exact u18040

def b34416 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 324 88 19 37 101 165 293), lower := (rows 11 162 324 88 19 32 64 128 256), losses := [] }

theorem u34416 : Upper (D 6) (R 6) [10,160,320,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34417 : Route 9 := (fun mask => (mask,id))

def c34417 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34417 : Upper (D 6) (R 6) [10,160,320,80,5] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,5] 13 (by decide) (choices 1) [1,2,4] r34417 c34417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18041
  · exact u18042
  · exact u18043

def r34418 : Route 9 := (fun mask => (mask,id))

def c34418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34418 : Upper (D 6) (R 6) [10,160,320,80,6] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,6] 13 (by decide) (choices 1) [1,4] r34418 c34418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18044
  · exact u18045

def r34419 : Route 9 := (fun mask => (mask,id))

def c34419 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34419 : Upper (D 6) (R 6) [10,160,320,80,33] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,33] 13 (by decide) (choices 1) [1,2,4] r34419 c34419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18046
  · exact u18047
  · exact u18048

def b34420 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 324 88 50 37 69 133 261), lower := (rows 11 162 324 88 50 32 64 128 256), losses := [] }

theorem u34420 : Upper (D 6) (R 6) [10,160,320,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34421 : Route 9 := (fun mask => (mask,id))

def c34421 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34421 : Upper (D 6) (R 6) [10,160,320,80,36] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,36] 13 (by decide) (choices 1) [1,2,4] r34421 c34421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18049
  · exact u18050
  · exact u18051

def b34422 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 324 104 19 53 85 149 277), lower := (rows 11 162 324 104 19 32 64 128 256), losses := [] }

theorem u34422 : Upper (D 6) (R 6) [10,160,320,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34423 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 324 104 21 55 87 151 279), lower := (rows 11 162 324 104 21 32 64 128 256), losses := [] }

theorem u34423 : Upper (D 6) (R 6) [10,160,320,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34424 : Route 9 := (fun mask => (mask,id))

def c34424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34424 : Upper (D 6) (R 6) [10,160,320,96,6] 13 := by
  apply FastRouting.sound _ _ [10,160,320,96,6] 13 (by decide) (choices 1) [1,4,16] r34424 c34424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18052
  · exact u18053
  · exact u18054

def b34425 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 22 13 49 100 100 228 356), lower := (rows 11 386 22 13 49 32 64 128 256), losses := [] }

theorem u34425 : Upper (D 6) (R 6) [10,384,18,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34426 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 22 13 52 97 97 225 353), lower := (rows 11 386 22 13 52 32 64 128 256), losses := [] }

theorem u34426 : Upper (D 6) (R 6) [10,384,18,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34427 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 22 13 112 101 101 229 357), lower := (rows 11 386 22 13 112 32 64 128 256), losses := [] }

theorem u34427 : Upper (D 6) (R 6) [10,384,18,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34428 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 386 22 41 49 100 68 196 324), lower := (rows 11 386 22 41 49 32 64 128 256), losses := [] }

theorem u34428 : Upper (D 6) (R 6) [10,384,18,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34429 : PairBound 9 := { available := 69, camps := [], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 386 22 41 52 101 69 197 325), lower := (rows 11 386 22 41 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 32 64 128 256), good := (rows 30 386 22 60 52 32 64 128 256) },{ target := 2, region := (rows 5 2 0 24 16 32 64 128 256), good := (rows 11 386 27 41 57 32 64 128 256) }] }

theorem u34429 : Upper (D 6) (R 6) [10,384,18,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34430 : Route 9 := (fun mask => (mask,id))

def c34430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34430 : Upper (D 6) (R 6) [10,384,18,33,65] 13 := by
  apply FastRouting.sound _ _ [10,384,18,33,65] 13 (by decide) (choices 1) [4,64] r34430 c34430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18055
  · exact u18056

def r34431 : Route 9 := (fun mask => (mask,id))

def c34431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34431 : Upper (D 6) (R 6) [10,384,18,33,68] 13 := by
  apply FastRouting.sound _ _ [10,384,18,33,68] 13 (by decide) (choices 1) [1,4,64] r34431 c34431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18057
  · exact u18058
  · exact u18059

def r34432 : Route 9 := (fun mask => (mask,id))

def c34432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34432 : Upper (D 6) (R 6) [10,384,18,33,96] 13 := by
  apply FastRouting.sound _ _ [10,384,18,33,96] 13 (by decide) (choices 1) [1,4,64] r34432 c34432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18060
  · exact u18061
  · exact u18062

def b34433 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 4, region := 454, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 386 22 44 49 101 69 197 325), lower := (rows 11 386 22 44 49 32 64 128 256), losses := [] }

theorem u34433 : Upper (D 6) (R 6) [10,384,18,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34434 : Route 9 := (fun mask => (mask,id))

def c34434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34434 : Upper (D 6) (R 6) [10,384,18,36,65] 13 := by
  apply FastRouting.sound _ _ [10,384,18,36,65] 13 (by decide) (choices 1) [1,4,64] r34434 c34434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18063
  · exact u18064
  · exact u18065

def r34435 : Route 9 := (fun mask => (mask,id))

def c34435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34435 : Upper (D 6) (R 6) [10,384,18,36,96] 13 := by
  apply FastRouting.sound _ _ [10,384,18,36,96] 13 (by decide) (choices 1) [1,4,64] r34435 c34435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18066
  · exact u18067
  · exact u18068

def b34436 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 386 22 104 112 37 69 133 261), lower := (rows 11 386 22 104 112 32 64 128 256), losses := [] }

theorem u34436 : Upper (D 6) (R 6) [10,384,18,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34437 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 37 25 22 100 100 228 356), lower := (rows 11 386 37 25 22 32 64 128 256), losses := [] }

theorem u34437 : Upper (D 6) (R 6) [10,384,33,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34438 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 386 37 25 50 100 68 196 324), lower := (rows 11 386 37 25 50 32 64 128 256), losses := [] }

theorem u34438 : Upper (D 6) (R 6) [10,384,33,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34439 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 386 37 25 52 102 70 198 326), lower := (rows 11 386 37 25 52 32 64 128 256), losses := [] }

theorem u34439 : Upper (D 6) (R 6) [10,384,33,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34439
end Delivery.IrregularNine14.P06
