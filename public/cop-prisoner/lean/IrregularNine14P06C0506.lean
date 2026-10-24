import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0198

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30360 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 328 84 35 99 163 291), lower := (rows 11 22 164 328 84 32 64 128 256), losses := [] }

theorem u30360 : Upper (D 6) (R 6) [10,20,160,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30361 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 164, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 22 164 328 112 39 71 135 263), lower := (rows 11 22 164 328 112 32 64 128 256), losses := [] }

theorem u30361 : Upper (D 6) (R 6) [10,20,160,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30362 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 388 41 19 100 100 228 356), lower := (rows 11 22 388 41 19 32 64 128 256), losses := [] }

theorem u30362 : Upper (D 6) (R 6) [10,20,384,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30363 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 388 41 21 98 98 226 354), lower := (rows 11 22 388 41 21 32 64 128 256), losses := [] }

theorem u30363 : Upper (D 6) (R 6) [10,20,384,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30364 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 388 41 22 97 97 225 353), lower := (rows 11 22 388 41 22 32 64 128 256), losses := [] }

theorem u30364 : Upper (D 6) (R 6) [10,20,384,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30365 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 388 41 49 102 70 198 326), lower := (rows 11 22 388 41 49 32 64 128 256), losses := [] }

theorem u30365 : Upper (D 6) (R 6) [10,20,384,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30366 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 388 41 50 101 69 197 325), lower := (rows 11 22 388 41 50 32 64 128 256), losses := [] }

theorem u30366 : Upper (D 6) (R 6) [10,20,384,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30367 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 388 41 52 99 67 195 323), lower := (rows 11 22 388 41 52 32 64 128 256), losses := [] }

theorem u30367 : Upper (D 6) (R 6) [10,20,384,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30368 : Route 9 := (fun mask => (mask,id))

def c30368 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30368 : Upper (D 6) (R 6) [10,20,384,33,65] 13 := by
  apply FastRouting.sound _ _ [10,20,384,33,65] 13 (by decide) (choices 1) [2,4,64] r30368 c30368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11880
  · exact u11881
  · exact u11882

def r30369 : Route 9 := (fun mask => (mask,id))

def c30369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30369 : Upper (D 6) (R 6) [10,20,384,33,66] 13 := by
  apply FastRouting.sound _ _ [10,20,384,33,66] 13 (by decide) (choices 1) [1,4,64] r30369 c30369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11883
  · exact u11884
  · exact u11885

def b30370 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 388 41 84 99 99 227 355), lower := (rows 11 22 388 41 84 32 64 128 256), losses := [] }

theorem u30370 : Upper (D 6) (R 6) [10,20,384,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30371 : Route 9 := (fun mask => (mask,id))

def c30371 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30371 : Upper (D 6) (R 6) [10,20,384,33,96] 13 := by
  apply FastRouting.sound _ _ [10,20,384,33,96] 13 (by decide) (choices 1) [1,2,4,64] r30371 c30371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11886
  · exact u11887
  · exact u11888
  · exact u11889

def b30372 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 388 44 19 97 97 225 353), lower := (rows 11 22 388 44 19 32 64 128 256), losses := [] }

theorem u30372 : Upper (D 6) (R 6) [10,20,384,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30373 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 388 44 49 99 67 195 323), lower := (rows 11 22 388 44 49 32 64 128 256), losses := [] }

theorem u30373 : Upper (D 6) (R 6) [10,20,384,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30374 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 388 44 50 97 65 193 321), lower := (rows 11 22 388 44 50 32 64 128 256), losses := [] }

theorem u30374 : Upper (D 6) (R 6) [10,20,384,36,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30375 : Route 9 := (fun mask => (mask,id))

def c30375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30375 : Upper (D 6) (R 6) [10,20,384,36,65] 13 := by
  apply FastRouting.sound _ _ [10,20,384,36,65] 13 (by decide) (choices 1) [1,2,64] r30375 c30375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11890
  · exact u11891
  · exact u11892

def b30376 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 388 44 82 97 97 225 353), lower := (rows 11 22 388 44 82 32 64 128 256), losses := [] }

theorem u30376 : Upper (D 6) (R 6) [10,20,384,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30377 : Route 9 := (fun mask => (mask,id))

def c30377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30377 : Upper (D 6) (R 6) [10,20,384,36,96] 13 := by
  apply FastRouting.sound _ _ [10,20,384,36,96] 13 (by decide) (choices 1) [1,2,64] r30377 c30377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11893
  · exact u11894
  · exact u11895

def b30378 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 388 104 19 101 101 229 357), lower := (rows 11 22 388 104 19 32 64 128 256), losses := [] }

theorem u30378 : Upper (D 6) (R 6) [10,20,384,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30379 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 388 104 21 99 99 227 355), lower := (rows 11 22 388 104 21 32 64 128 256), losses := [] }

theorem u30379 : Upper (D 6) (R 6) [10,20,384,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30380 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 388 104 22 97 97 225 353), lower := (rows 11 22 388 104 22 32 64 128 256), losses := [] }

theorem u30380 : Upper (D 6) (R 6) [10,20,384,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30381 : Route 9 := (fun mask => (mask,id))

def c30381 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30381 : Upper (D 6) (R 6) [10,20,384,96,33] 13 := by
  apply FastRouting.sound _ _ [10,20,384,96,33] 13 (by decide) (choices 1) [1,2,4,64] r30381 c30381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11896
  · exact u11897
  · exact u11898
  · exact u11899

def b30382 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 22 388 104 50 101 69 197 325), lower := (rows 11 22 388 104 50 32 64 128 256), losses := [] }

theorem u30382 : Upper (D 6) (R 6) [10,20,384,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30383 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 388 104 52 99 67 195 323), lower := (rows 11 22 388 104 52 32 64 128 256), losses := [] }

theorem u30383 : Upper (D 6) (R 6) [10,20,384,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30384 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 22 388 104 112 39 71 135 263), lower := (rows 11 22 388 104 112 32 64 128 256), losses := [] }

theorem u30384 : Upper (D 6) (R 6) [10,20,384,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30385 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 35 22 76 21 480 480 480 480), lower := (rows 11 35 22 76 21 32 64 128 256), losses := [] }

theorem u30385 : Upper (D 6) (R 6) [10,33,18,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30386 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 20, targets := 64 },{ cop := 2, region := 456, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 35 22 76 49 484 452 452 452), lower := (rows 11 35 22 76 49 32 64 128 256), losses := [] }

theorem u30386 : Upper (D 6) (R 6) [10,33,18,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30387 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 22 76 52 481 449 449 449), lower := (rows 11 35 22 76 52 32 64 128 256), losses := [] }

theorem u30387 : Upper (D 6) (R 6) [10,33,18,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30388 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 488, targets := 3 },{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 11 35 22 76 81 420 484 420 420), lower := (rows 11 35 22 76 81 32 64 128 256), losses := [] }

theorem u30388 : Upper (D 6) (R 6) [10,33,18,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30389 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 22 76 84 417 481 417 417), lower := (rows 11 35 22 76 84 32 64 128 256), losses := [] }

theorem u30389 : Upper (D 6) (R 6) [10,33,18,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30390 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 3, region := 419, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 76 112 421 453 389 389), lower := (rows 11 35 22 76 112 32 64 128 256), losses := [] }

theorem u30390 : Upper (D 6) (R 6) [10,33,18,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30391 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 360, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 35 22 76 145 356 356 484 356), lower := (rows 11 35 22 76 145 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 44 76 140 268), good := (rows 505 49 508 492 145 32 64 128 256) }] }

theorem u30391 : Upper (D 6) (R 6) [10,33,18,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30392 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 35 22 76 148 353 353 481 353), lower := (rows 11 35 22 76 148 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 489 481 508 92 156 32 64 128 256) }] }

theorem u30392 : Upper (D 6) (R 6) [10,33,18,68,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30393 : Route 9 := (fun mask => (mask,id))

def c30393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30393 : Upper (D 6) (R 6) [10,33,18,68,160] 13 := by
  apply FastRouting.sound _ _ [10,33,18,68,160] 13 (by decide) (choices 1) [1,4,64,256] r30393 c30393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11900
  · exact u11901
  · exact u11902
  · exact u11903

def r30394 : Route 9 := (fun mask => (mask,id))

def c30394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30394 : Upper (D 6) (R 6) [10,33,18,68,192] 13 := by
  apply FastRouting.sound _ _ [10,33,18,68,192] 13 (by decide) (choices 1) [1,4,256] r30394 c30394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11904
  · exact u11905
  · exact u11906

def r30395 : Route 9 := (fun mask => (mask,id))

def c30395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30395 : Upper (D 6) (R 6) [10,33,18,68,384] 13 := by
  apply FastRouting.sound _ _ [10,33,18,68,384] 13 (by decide) (choices 1) [1,4,64] r30395 c30395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11907
  · exact u11908
  · exact u11909

def b30396 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 35 22 140 21 352 352 480 352), lower := (rows 11 35 22 140 21 32 64 128 256), losses := [] }

theorem u30396 : Upper (D 6) (R 6) [10,33,18,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30397 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 20, targets := 64 },{ cop := 2, region := 456, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 35 22 140 49 356 324 452 324), lower := (rows 11 35 22 140 49 32 64 128 256), losses := [] }

theorem u30397 : Upper (D 6) (R 6) [10,33,18,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30398 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 22 140 52 353 321 449 321), lower := (rows 11 35 22 140 52 32 64 128 256), losses := [] }

theorem u30398 : Upper (D 6) (R 6) [10,33,18,132,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30399 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 488, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 35 22 140 81 356 356 484 356), lower := (rows 11 35 22 140 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 44 76 140 268), good := (rows 505 49 508 492 81 32 64 128 256) }] }

theorem u30399 : Upper (D 6) (R 6) [10,33,18,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30400 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 35 22 140 84 353 353 481 353), lower := (rows 11 35 22 140 84 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 489 481 508 156 92 32 64 128 256) }] }

theorem u30400 : Upper (D 6) (R 6) [10,33,18,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30401 : Route 9 := (fun mask => (mask,id))

def c30401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30401 : Upper (D 6) (R 6) [10,33,18,132,96] 13 := by
  apply FastRouting.sound _ _ [10,33,18,132,96] 13 (by decide) (choices 1) [1,4,64,256] r30401 c30401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11910
  · exact u11911
  · exact u11912
  · exact u11913

def b30402 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 232, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 35 22 140 273 100 100 228 356), lower := (rows 11 35 22 140 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 44 76 140 268), good := (rows 505 49 508 492 273 32 64 128 256) }] }

theorem u30402 : Upper (D 6) (R 6) [10,33,18,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30403 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 35 22 140 276 97 97 225 353), lower := (rows 11 35 22 140 276 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 489 481 508 156 284 32 64 128 256) }] }

theorem u30403 : Upper (D 6) (R 6) [10,33,18,132,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30404 : Route 9 := (fun mask => (mask,id))

def c30404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30404 : Upper (D 6) (R 6) [10,33,18,132,288] 13 := by
  apply FastRouting.sound _ _ [10,33,18,132,288] 13 (by decide) (choices 1) [1,4,64] r30404 c30404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11914
  · exact u11915
  · exact u11916

def r30405 : Route 9 := (fun mask => (mask,id))

def c30405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30405 : Upper (D 6) (R 6) [10,33,18,132,320] 13 := by
  apply FastRouting.sound _ _ [10,33,18,132,320] 13 (by decide) (choices 1) [1,4,64] r30405 c30405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11917
  · exact u11918
  · exact u11919

def b30406 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 35 22 200 21 356 356 484 356), lower := (rows 11 35 22 200 21 32 64 128 256), losses := [] }

theorem u30406 : Upper (D 6) (R 6) [10,33,18,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30407 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 20, targets := 64 },{ cop := 2, region := 456, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 35 22 200 49 356 324 452 324), lower := (rows 11 35 22 200 49 32 64 128 256), losses := [] }

theorem u30407 : Upper (D 6) (R 6) [10,33,18,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30408 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 22 200 52 357 325 453 325), lower := (rows 11 35 22 200 52 32 64 128 256), losses := [] }

theorem u30408 : Upper (D 6) (R 6) [10,33,18,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30409 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 488, targets := 3 },{ cop := 4, region := 294, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 22 200 81 292 356 420 292), lower := (rows 11 35 22 200 81 32 64 128 256), losses := [] }

theorem u30409 : Upper (D 6) (R 6) [10,33,18,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30410 : Route 9 := (fun mask => (mask,id))

def c30410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30410 : Upper (D 6) (R 6) [10,33,18,192,68] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,68] 13 (by decide) (choices 1) [1,4,256] r30410 c30410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11920
  · exact u11921
  · exact u11922

def r30411 : Route 9 := (fun mask => (mask,id))

def c30411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30411 : Upper (D 6) (R 6) [10,33,18,192,96] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,96] 13 (by decide) (choices 1) [1,4,256] r30411 c30411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11923
  · exact u11924
  · exact u11925

def r30412 : Route 9 := (fun mask => (mask,id))

def c30412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30412 : Upper (D 6) (R 6) [10,33,18,192,257] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,257] 13 (by decide) (choices 1) [4,64] r30412 c30412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11926
  · exact u11927

def r30413 : Route 9 := (fun mask => (mask,id))

def c30413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30413 : Upper (D 6) (R 6) [10,33,18,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,260] 13 (by decide) (choices 1) [1,4,64] r30413 c30413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11928
  · exact u11929
  · exact u11930

def r30414 : Route 9 := (fun mask => (mask,id))

def c30414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30414 : Upper (D 6) (R 6) [10,33,18,192,288] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,288] 13 (by decide) (choices 1) [1,4,64] r30414 c30414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11931
  · exact u11932
  · exact u11933

def r30415 : Route 9 := (fun mask => (mask,id))

def c30415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30415 : Upper (D 6) (R 6) [10,33,18,192,320] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,320] 13 (by decide) (choices 1) [1,4] r30415 c30415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11934
  · exact u11935

def b30416 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 35 22 392 21 100 100 228 356), lower := (rows 11 35 22 392 21 32 64 128 256), losses := [] }

theorem u30416 : Upper (D 6) (R 6) [10,33,18,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30417 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 20, targets := 64 },{ cop := 2, region := 456, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 35 22 392 49 100 68 196 324), lower := (rows 11 35 22 392 49 32 64 128 256), losses := [] }

theorem u30417 : Upper (D 6) (R 6) [10,33,18,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30418 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 22 392 52 101 69 197 325), lower := (rows 11 35 22 392 52 32 64 128 256), losses := [] }

theorem u30418 : Upper (D 6) (R 6) [10,33,18,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30419 : Route 9 := (fun mask => (mask,id))

def c30419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30419 : Upper (D 6) (R 6) [10,33,18,384,65] 13 := by
  apply FastRouting.sound _ _ [10,33,18,384,65] 13 (by decide) (choices 1) [4,64] r30419 c30419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11936
  · exact u11937

#print axioms u30419
end Delivery.IrregularNine14.P06
