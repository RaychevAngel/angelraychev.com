import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0150
import IrregularNine14P06C0151
import IrregularNine14P06C0152

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r27900 : Route 9 := (fun mask => (mask,id))

def c27900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27900 : Upper (D 6) (R 6) [6,9,144,288,68] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,68] 13 (by decide) (choices 1) [1,2,64] r27900 c27900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9054
  · exact u9055
  · exact u9056

def r27901 : Route 9 := (fun mask => (mask,id))

def c27901 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27901 : Upper (D 6) (R 6) [6,9,144,288,96] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,96] 13 (by decide) (choices 1) [1,2,4,64] r27901 c27901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9057
  · exact u9058
  · exact u9059
  · exact u9060

def b27902 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 27, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 26 21 352 352 480 352), lower := (rows 7 11 164 26 21 32 64 128 256), losses := [] }

theorem u27902 : Upper (D 6) (R 6) [6,9,160,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27903 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 26 49 356 324 452 324), lower := (rows 7 11 164 26 49 32 64 128 256), losses := [] }

theorem u27903 : Upper (D 6) (R 6) [6,9,160,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27904 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 26 52 353 321 449 321), lower := (rows 7 11 164 26 52 32 64 128 256), losses := [] }

theorem u27904 : Upper (D 6) (R 6) [6,9,160,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27905 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 26 81 356 356 484 356), lower := (rows 7 11 164 26 81 32 64 128 256), losses := [] }

theorem u27905 : Upper (D 6) (R 6) [6,9,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27906 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 26 84 353 353 481 353), lower := (rows 7 11 164 26 84 32 64 128 256), losses := [] }

theorem u27906 : Upper (D 6) (R 6) [6,9,160,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27907 : Route 9 := (fun mask => (mask,id))

def c27907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27907 : Upper (D 6) (R 6) [6,9,160,18,96] 13 := by
  apply FastRouting.sound _ _ [6,9,160,18,96] 13 (by decide) (choices 1) [1,4,64,256] r27907 c27907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9061
  · exact u9062
  · exact u9063
  · exact u9064

def b27908 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 26 273 100 100 228 356), lower := (rows 7 11 164 26 273 32 64 128 256), losses := [] }

theorem u27908 : Upper (D 6) (R 6) [6,9,160,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27909 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 26 276 97 97 225 353), lower := (rows 7 11 164 26 276 32 64 128 256), losses := [] }

theorem u27909 : Upper (D 6) (R 6) [6,9,160,18,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27910 : Route 9 := (fun mask => (mask,id))

def c27910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27910 : Upper (D 6) (R 6) [6,9,160,18,288] 13 := by
  apply FastRouting.sound _ _ [6,9,160,18,288] 13 (by decide) (choices 1) [1,4,64] r27910 c27910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9065
  · exact u9066
  · exact u9067

def r27911 : Route 9 := (fun mask => (mask,id))

def c27911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27911 : Upper (D 6) (R 6) [6,9,160,18,320] 13 := by
  apply FastRouting.sound _ _ [6,9,160,18,320] 13 (by decide) (choices 1) [1,4,64] r27911 c27911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9068
  · exact u9069
  · exact u9070

def b27912 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 19 356 324 452 324), lower := (rows 7 11 164 56 19 32 64 128 256), losses := [] }

theorem u27912 : Upper (D 6) (R 6) [6,9,160,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27913 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 21 354 322 450 322), lower := (rows 7 11 164 56 21 32 64 128 256), losses := [] }

theorem u27913 : Upper (D 6) (R 6) [6,9,160,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27914 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 22 353 321 449 321), lower := (rows 7 11 164 56 22 32 64 128 256), losses := [] }

theorem u27914 : Upper (D 6) (R 6) [6,9,160,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27915 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 164 56 81 358 326 454 326), lower := (rows 7 11 164 56 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 164 60 508 32 64 128 256) }] }

theorem u27915 : Upper (D 6) (R 6) [6,9,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27916 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 164 56 82 357 325 453 325), lower := (rows 7 11 164 56 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 35 67 131 259), good := (rows 485 493 164 60 508 32 64 128 256) }] }

theorem u27916 : Upper (D 6) (R 6) [6,9,160,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27917 : Route 9 := (fun mask => (mask,id))

def c27917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27917 : Upper (D 6) (R 6) [6,9,160,48,68] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,68] 13 (by decide) (choices 1) [1,2,64,256] r27917 c27917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9071
  · exact u9072
  · exact u9073
  · exact u9074

def b27918 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 228, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 164 56 273 102 70 198 326), lower := (rows 7 11 164 56 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 164 60 508 32 64 128 256) }] }

theorem u27918 : Upper (D 6) (R 6) [6,9,160,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27919 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 164 56 274 101 69 197 325), lower := (rows 7 11 164 56 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 35 67 131 259), good := (rows 485 493 164 60 508 32 64 128 256) }] }

theorem u27919 : Upper (D 6) (R 6) [6,9,160,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27920 : Route 9 := (fun mask => (mask,id))

def c27920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27920 : Upper (D 6) (R 6) [6,9,160,48,260] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,260] 13 (by decide) (choices 1) [1,2,64] r27920 c27920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9075
  · exact u9076
  · exact u9077

def r27921 : Route 9 := (fun mask => (mask,id))

def c27921 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27921 : Upper (D 6) (R 6) [6,9,160,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,320] 13 (by decide) (choices 1) [1,2,4,64] r27921 c27921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9078
  · exact u9079
  · exact u9080
  · exact u9081

def b27922 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 164 74 21 368 368 496 368), lower := (rows 7 11 164 74 21 32 64 128 256), losses := [] }

theorem u27922 : Upper (D 6) (R 6) [6,9,160,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27923 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 74 49 372 340 468 340), lower := (rows 7 11 164 74 49 32 64 128 256), losses := [] }

theorem u27923 : Upper (D 6) (R 6) [6,9,160,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27924 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 164 74 52 369 337 465 337), lower := (rows 7 11 164 74 52 32 64 128 256), losses := [] }

theorem u27924 : Upper (D 6) (R 6) [6,9,160,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27925 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 11 164 74 81 308 372 436 308), lower := (rows 7 11 164 74 81 32 64 128 256), losses := [] }

theorem u27925 : Upper (D 6) (R 6) [6,9,160,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27926 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 74 84 305 369 433 305), lower := (rows 7 11 164 74 84 32 64 128 256), losses := [] }

theorem u27926 : Upper (D 6) (R 6) [6,9,160,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27927 : Route 9 := (fun mask => (mask,id))

def c27927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27927 : Upper (D 6) (R 6) [6,9,160,66,96] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66,96] 13 (by decide) (choices 1) [1,4,16,256] r27927 c27927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9082
  · exact u9083
  · exact u9084
  · exact u9085

def b27928 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 74 273 116 116 244 372), lower := (rows 7 11 164 74 273 32 64 128 256), losses := [] }

theorem u27928 : Upper (D 6) (R 6) [6,9,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27929 : Route 9 := (fun mask => (mask,id))

def c27929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27929 : Upper (D 6) (R 6) [6,9,160,66,260] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66,260] 13 (by decide) (choices 1) [1,16,64] r27929 c27929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9086
  · exact u9087
  · exact u9088

def r27930 : Route 9 := (fun mask => (mask,id))

def c27930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27930 : Upper (D 6) (R 6) [6,9,160,66,288] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66,288] 13 (by decide) (choices 1) [1,4,16,64] r27930 c27930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9089
  · exact u9090
  · exact u9091
  · exact u9092

def r27931 : Route 9 := (fun mask => (mask,id))

def c27931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27931 : Upper (D 6) (R 6) [6,9,160,66,320] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66,320] 13 (by decide) (choices 1) [1,4,16] r27931 c27931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9093
  · exact u9094
  · exact u9095

def b27932 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 88 19 356 356 484 356), lower := (rows 7 11 164 88 19 32 64 128 256), losses := [] }

theorem u27932 : Upper (D 6) (R 6) [6,9,160,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27933 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 164 88 21 354 354 482 354), lower := (rows 7 11 164 88 21 32 64 128 256), losses := [] }

theorem u27933 : Upper (D 6) (R 6) [6,9,160,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27934 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 164 88 22 353 353 481 353), lower := (rows 7 11 164 88 22 32 64 128 256), losses := [] }

theorem u27934 : Upper (D 6) (R 6) [6,9,160,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27935 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 7 11 164 88 49 358 326 454 326), lower := (rows 7 11 164 88 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 164 92 508 32 64 128 256) },{ target := 5, region := (rows 1 18 4 24 16 0 65 129 257), good := (rows 455 459 132 90 475 0 64 128 256) }] }

theorem u27935 : Upper (D 6) (R 6) [6,9,160,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27936 : Route 9 := (fun mask => (mask,id))

def c27936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27936 : Upper (D 6) (R 6) [6,9,160,80,34] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,34] 13 (by decide) (choices 1) [1,4,64,256] r27936 c27936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9096
  · exact u9097
  · exact u9098
  · exact u9099

def b27937 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 164 88 52 355 323 451 323), lower := (rows 7 11 164 88 52 32 64 128 256), losses := [] }

theorem u27937 : Upper (D 6) (R 6) [6,9,160,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27938 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 11 164 88 81 294 358 422 294), lower := (rows 7 11 164 88 81 32 64 128 256), losses := [] }

theorem u27938 : Upper (D 6) (R 6) [6,9,160,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27939 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 88 82 293 357 421 293), lower := (rows 7 11 164 88 82 32 64 128 256), losses := [] }

theorem u27939 : Upper (D 6) (R 6) [6,9,160,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27940 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 88 84 291 355 419 291), lower := (rows 7 11 164 88 84 32 64 128 256), losses := [] }

theorem u27940 : Upper (D 6) (R 6) [6,9,160,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27941 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 88 112 295 327 391 263), lower := (rows 7 11 164 88 112 32 64 128 256), losses := [] }

theorem u27941 : Upper (D 6) (R 6) [6,9,160,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27942 : Route 9 := (fun mask => (mask,id))

def c27942 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27942 : Upper (D 6) (R 6) [6,9,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,257] 13 (by decide) (choices 1) [2,4,64] r27942 c27942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9100
  · exact u9101
  · exact u9102

def r27943 : Route 9 := (fun mask => (mask,id))

def c27943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27943 : Upper (D 6) (R 6) [6,9,160,80,258] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,258] 13 (by decide) (choices 1) [1,4,64] r27943 c27943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9103
  · exact u9104
  · exact u9105

def r27944 : Route 9 := (fun mask => (mask,id))

def c27944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27944 : Upper (D 6) (R 6) [6,9,160,80,260] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,260] 13 (by decide) (choices 1) [1,2,64] r27944 c27944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9106
  · exact u9107
  · exact u9108

def r27945 : Route 9 := (fun mask => (mask,id))

def c27945 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27945 : Upper (D 6) (R 6) [6,9,160,80,288] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,288] 13 (by decide) (choices 1) [1,2,4,64] r27945 c27945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9109
  · exact u9110
  · exact u9111
  · exact u9112

def b27946 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 88 336 39 103 167 295), lower := (rows 7 11 164 88 336 32 64 128 256), losses := [] }

theorem u27946 : Upper (D 6) (R 6) [6,9,160,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27947 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 104 19 372 340 468 340), lower := (rows 7 11 164 104 19 32 64 128 256), losses := [] }

theorem u27947 : Upper (D 6) (R 6) [6,9,160,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27948 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 11 164 104 21 370 338 466 338), lower := (rows 7 11 164 104 21 32 64 128 256), losses := [] }

theorem u27948 : Upper (D 6) (R 6) [6,9,160,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27949 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 11 164 104 22 369 337 465 337), lower := (rows 7 11 164 104 22 32 64 128 256), losses := [] }

theorem u27949 : Upper (D 6) (R 6) [6,9,160,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27950 : Route 9 := (fun mask => (mask,id))

def c27950 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27950 : Upper (D 6) (R 6) [6,9,160,96,65] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,65] 13 (by decide) (choices 1) [2,4,16,256] r27950 c27950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9113
  · exact u9114
  · exact u9115
  · exact u9116

def b27951 : PairBound 9 := { available := 277, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 7 11 164 104 82 309 341 405 277), lower := (rows 7 11 164 104 82 32 64 128 256), losses := [] }

theorem u27951 : Upper (D 6) (R 6) [6,9,160,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27952 : Route 9 := (fun mask => (mask,id))

def c27952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27952 : Upper (D 6) (R 6) [6,9,160,96,68] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,68] 13 (by decide) (choices 1) [1,2,16,256] r27952 c27952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9117
  · exact u9118
  · exact u9119
  · exact u9120

def r27953 : Route 9 := (fun mask => (mask,id))

def c27953 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27953 : Upper (D 6) (R 6) [6,9,160,96,257] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,257] 13 (by decide) (choices 1) [2,4,16,64] r27953 c27953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9121
  · exact u9122
  · exact u9123
  · exact u9124

def r27954 : Route 9 := (fun mask => (mask,id))

def c27954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27954 : Upper (D 6) (R 6) [6,9,160,96,258] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,258] 13 (by decide) (choices 1) [1,4,16,64] r27954 c27954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9125
  · exact u9126
  · exact u9127
  · exact u9128

def r27955 : Route 9 := (fun mask => (mask,id))

def c27955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27955 : Upper (D 6) (R 6) [6,9,160,96,260] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,260] 13 (by decide) (choices 1) [1,2,16,64] r27955 c27955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9129
  · exact u9130
  · exact u9131
  · exact u9132

def r27956 : Route 9 := (fun mask => (mask,id))

def c27956 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27956 : Upper (D 6) (R 6) [6,9,160,96,320] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,320] 13 (by decide) (choices 1) [1,2,4,16] r27956 c27956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9133
  · exact u9134
  · exact u9135
  · exact u9136

def b27957 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 164 266 21 112 112 240 368), lower := (rows 7 11 164 266 21 32 64 128 256), losses := [] }

theorem u27957 : Upper (D 6) (R 6) [6,9,160,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27958 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 266 49 116 84 212 340), lower := (rows 7 11 164 266 49 32 64 128 256), losses := [] }

theorem u27958 : Upper (D 6) (R 6) [6,9,160,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27959 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 164 266 52 113 81 209 337), lower := (rows 7 11 164 266 52 32 64 128 256), losses := [] }

theorem u27959 : Upper (D 6) (R 6) [6,9,160,258,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27959
end Delivery.IrregularNine14.P06
