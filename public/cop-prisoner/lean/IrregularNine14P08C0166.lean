import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0044
import IrregularNine14P08C0045

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9960 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 208 289 353 417 289), lower := (rows 67 7 44 152 208 32 64 128 256), losses := [] }

theorem u9960 : Upper (D 8) (R 8) [66,5,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9961 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 273 224 224 224 480), lower := (rows 67 7 44 152 273 32 64 128 256), losses := [] }

theorem u9961 : Upper (D 8) (R 8) [66,5,40,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9962 : Route 9 := (fun mask => (mask,id))

def c9962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9962 : Upper (D 8) (R 8) [66,5,40,144,288] 13 := by
  apply FastRouting.sound _ _ [66,5,40,144,288] 13 (by decide) (choices 1) [1,64,128] r9962 c9962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2689
  · exact u2690
  · exact u2691

def r9963 : Route 9 := (fun mask => (mask,id))

def c9963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9963 : Upper (D 8) (R 8) [66,5,40,144,320] 13 := by
  apply FastRouting.sound _ _ [66,5,40,144,320] 13 (by decide) (choices 1) [1,128] r9963 c9963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2692
  · exact u2693

def b9964 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 400 97 97 225 353), lower := (rows 67 7 44 152 400 32 64 128 256), losses := [] }

theorem u9964 : Upper (D 8) (R 8) [66,5,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9965 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 49 224 224 224 480), lower := (rows 67 7 44 280 49 32 64 128 256), losses := [] }

theorem u9965 : Upper (D 8) (R 8) [66,5,40,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9966 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 44 280 81 160 224 160 416), lower := (rows 67 7 44 280 81 32 64 128 256), losses := [] }

theorem u9966 : Upper (D 8) (R 8) [66,5,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9967 : Route 9 := (fun mask => (mask,id))

def c9967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9967 : Upper (D 8) (R 8) [66,5,40,272,96] 13 := by
  apply FastRouting.sound _ _ [66,5,40,272,96] 13 (by decide) (choices 1) [1,128] r9967 c9967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2694
  · exact u2695

def b9968 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 145 224 224 224 480), lower := (rows 67 7 44 280 145 32 64 128 256), losses := [] }

theorem u9968 : Upper (D 8) (R 8) [66,5,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9969 : Route 9 := (fun mask => (mask,id))

def c9969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9969 : Upper (D 8) (R 8) [66,5,40,272,160] 13 := by
  apply FastRouting.sound _ _ [66,5,40,272,160] 13 (by decide) (choices 1) [1,64,128] r9969 c9969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2696
  · exact u2697
  · exact u2698

def r9970 : Route 9 := (fun mask => (mask,id))

def c9970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9970 : Upper (D 8) (R 8) [66,5,40,272,192] 13 := by
  apply FastRouting.sound _ _ [66,5,40,272,192] 13 (by decide) (choices 1) [1,128] r9970 c9970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2699
  · exact u2700

def b9971 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 392 49 240 240 240 496), lower := (rows 67 7 44 392 49 32 64 128 256), losses := [] }

theorem u9971 : Upper (D 8) (R 8) [66,5,40,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9972 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 44 392 81 176 240 176 432), lower := (rows 67 7 44 392 81 32 64 128 256), losses := [] }

theorem u9972 : Upper (D 8) (R 8) [66,5,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9973 : Route 9 := (fun mask => (mask,id))

def c9973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9973 : Upper (D 8) (R 8) [66,5,40,384,96] 13 := by
  apply FastRouting.sound _ _ [66,5,40,384,96] 13 (by decide) (choices 1) [1,16,128] r9973 c9973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2701
  · exact u2702
  · exact u2703

def b9974 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 392 145 112 112 240 368), lower := (rows 67 7 44 392 145 32 64 128 256), losses := [] }

theorem u9974 : Upper (D 8) (R 8) [66,5,40,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9975 : Route 9 := (fun mask => (mask,id))

def c9975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9975 : Upper (D 8) (R 8) [66,5,40,384,160] 13 := by
  apply FastRouting.sound _ _ [66,5,40,384,160] 13 (by decide) (choices 1) [1,16,64] r9975 c9975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2704
  · exact u2705
  · exact u2706

def r9976 : Route 9 := (fun mask => (mask,id))

def c9976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9976 : Upper (D 8) (R 8) [66,5,40,384,192] 13 := by
  apply FastRouting.sound _ _ [66,5,40,384,192] 13 (by decide) (choices 1) [1,16] r9976 c9976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2707
  · exact u2708

def b9977 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 56 49 480 480 480 480), lower := (rows 67 7 140 56 49 32 64 128 256), losses := [] }

theorem u9977 : Upper (D 8) (R 8) [66,5,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9978 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 140 56 81 416 480 416 416), lower := (rows 67 7 140 56 81 32 64 128 256), losses := [] }

theorem u9978 : Upper (D 8) (R 8) [66,5,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9979 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 140 56 112 417 481 417 417), lower := (rows 67 7 140 56 112 32 64 128 256), losses := [] }

theorem u9979 : Upper (D 8) (R 8) [66,5,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9980 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 56 145 352 352 480 352), lower := (rows 67 7 140 56 145 32 64 128 256), losses := [] }

theorem u9980 : Upper (D 8) (R 8) [66,5,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9981 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 56 176 353 353 481 353), lower := (rows 67 7 140 56 176 32 64 128 256), losses := [] }

theorem u9981 : Upper (D 8) (R 8) [66,5,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9982 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 56 208 289 353 417 289), lower := (rows 67 7 140 56 208 32 64 128 256), losses := [] }

theorem u9982 : Upper (D 8) (R 8) [66,5,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9983 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 56 273 224 224 224 480), lower := (rows 67 7 140 56 273 32 64 128 256), losses := [] }

theorem u9983 : Upper (D 8) (R 8) [66,5,136,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9984 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 140 56 304 225 225 225 481), lower := (rows 67 7 140 56 304 32 64 128 256), losses := [] }

theorem u9984 : Upper (D 8) (R 8) [66,5,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9985 : Route 9 := (fun mask => (mask,id))

def c9985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9985 : Upper (D 8) (R 8) [66,5,136,48,320] 13 := by
  apply FastRouting.sound _ _ [66,5,136,48,320] 13 (by decide) (choices 1) [1,128] r9985 c9985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2709
  · exact u2710

def b9986 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 56 400 97 97 225 353), lower := (rows 67 7 140 56 400 32 64 128 256), losses := [] }

theorem u9986 : Upper (D 8) (R 8) [66,5,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9987 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 280 49 224 224 224 480), lower := (rows 67 7 140 280 49 32 64 128 256), losses := [] }

theorem u9987 : Upper (D 8) (R 8) [66,5,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9988 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 140 280 81 160 224 160 416), lower := (rows 67 7 140 280 81 32 64 128 256), losses := [] }

theorem u9988 : Upper (D 8) (R 8) [66,5,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9989 : Route 9 := (fun mask => (mask,id))

def c9989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9989 : Upper (D 8) (R 8) [66,5,136,272,96] 13 := by
  apply FastRouting.sound _ _ [66,5,136,272,96] 13 (by decide) (choices 1) [1,128] r9989 c9989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2711
  · exact u2712

def b9990 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 280 145 96 96 224 352), lower := (rows 67 7 140 280 145 32 64 128 256), losses := [] }

theorem u9990 : Upper (D 8) (R 8) [66,5,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9991 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 280 176 97 97 225 353), lower := (rows 67 7 140 280 176 32 64 128 256), losses := [] }

theorem u9991 : Upper (D 8) (R 8) [66,5,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9992 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 280 208 33 97 161 289), lower := (rows 67 7 140 280 208 32 64 128 256), losses := [] }

theorem u9992 : Upper (D 8) (R 8) [66,5,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9993 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 296 49 240 240 240 496), lower := (rows 67 7 140 296 49 32 64 128 256), losses := [] }

theorem u9993 : Upper (D 8) (R 8) [66,5,136,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9994 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 140 296 81 176 240 176 432), lower := (rows 67 7 140 296 81 32 64 128 256), losses := [] }

theorem u9994 : Upper (D 8) (R 8) [66,5,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9995 : Route 9 := (fun mask => (mask,id))

def c9995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9995 : Upper (D 8) (R 8) [66,5,136,288,96] 13 := by
  apply FastRouting.sound _ _ [66,5,136,288,96] 13 (by decide) (choices 1) [1,16,128] r9995 c9995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2713
  · exact u2714
  · exact u2715

def b9996 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 296 145 112 112 240 368), lower := (rows 67 7 140 296 145 32 64 128 256), losses := [] }

theorem u9996 : Upper (D 8) (R 8) [66,5,136,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9997 : Route 9 := (fun mask => (mask,id))

def c9997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9997 : Upper (D 8) (R 8) [66,5,136,288,160] 13 := by
  apply FastRouting.sound _ _ [66,5,136,288,160] 13 (by decide) (choices 1) [1,16,64] r9997 c9997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2716
  · exact u2717
  · exact u2718

def r9998 : Route 9 := (fun mask => (mask,id))

def c9998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9998 : Upper (D 8) (R 8) [66,5,136,288,192] 13 := by
  apply FastRouting.sound _ _ [66,5,136,288,192] 13 (by decide) (choices 1) [1,16] r9998 c9998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2719
  · exact u2720

def b9999 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 56 480 480 480 480), lower := (rows 67 7 164 25 56 32 64 128 256), losses := [] }

theorem u9999 : Upper (D 8) (R 8) [66,5,160,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10000 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 7 164 25 88 416 480 416 416), lower := (rows 67 7 164 25 88 32 64 128 256), losses := [] }

theorem u10000 : Upper (D 8) (R 8) [66,5,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10001 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 112 424 488 424 424), lower := (rows 67 7 164 25 112 32 64 128 256), losses := [] }

theorem u10001 : Upper (D 8) (R 8) [66,5,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10002 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 25 152 352 352 480 352), lower := (rows 67 7 164 25 152 32 64 128 256), losses := [] }

theorem u10002 : Upper (D 8) (R 8) [66,5,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10003 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 208 296 360 424 296), lower := (rows 67 7 164 25 208 32 64 128 256), losses := [] }

theorem u10003 : Upper (D 8) (R 8) [66,5,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10004 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 280 224 224 224 480), lower := (rows 67 7 164 25 280 32 64 128 256), losses := [] }

theorem u10004 : Upper (D 8) (R 8) [66,5,160,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10005 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 304 232 232 232 488), lower := (rows 67 7 164 25 304 32 64 128 256), losses := [] }

theorem u10005 : Upper (D 8) (R 8) [66,5,160,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10006 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 336 168 232 168 424), lower := (rows 67 7 164 25 336 32 64 128 256), losses := [] }

theorem u10006 : Upper (D 8) (R 8) [66,5,160,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10007 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 400 104 104 232 360), lower := (rows 67 7 164 25 400 32 64 128 256), losses := [] }

theorem u10007 : Upper (D 8) (R 8) [66,5,160,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10008 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 56 496 464 464 464), lower := (rows 67 7 164 41 56 32 64 128 256), losses := [] }

theorem u10008 : Upper (D 8) (R 8) [66,5,160,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10009 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 88 432 496 432 432), lower := (rows 67 7 164 41 88 32 64 128 256), losses := [] }

theorem u10009 : Upper (D 8) (R 8) [66,5,160,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10010 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 112 440 472 408 408), lower := (rows 67 7 164 41 112 32 64 128 256), losses := [] }

theorem u10010 : Upper (D 8) (R 8) [66,5,160,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10011 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 152 368 368 496 368), lower := (rows 67 7 164 41 152 32 64 128 256), losses := [] }

theorem u10011 : Upper (D 8) (R 8) [66,5,160,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10012 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 208 312 376 440 312), lower := (rows 67 7 164 41 208 32 64 128 256), losses := [] }

theorem u10012 : Upper (D 8) (R 8) [66,5,160,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10013 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 280 240 240 240 496), lower := (rows 67 7 164 41 280 32 64 128 256), losses := [] }

theorem u10013 : Upper (D 8) (R 8) [66,5,160,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10014 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 304 248 216 216 472), lower := (rows 67 7 164 41 304 32 64 128 256), losses := [] }

theorem u10014 : Upper (D 8) (R 8) [66,5,160,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10015 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 336 184 248 184 440), lower := (rows 67 7 164 41 336 32 64 128 256), losses := [] }

theorem u10015 : Upper (D 8) (R 8) [66,5,160,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10016 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 400 120 120 248 376), lower := (rows 67 7 164 41 400 32 64 128 256), losses := [] }

theorem u10016 : Upper (D 8) (R 8) [66,5,160,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10017 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 56 56 481 449 449 449), lower := (rows 67 7 164 56 56 32 64 128 256), losses := [] }

theorem u10017 : Upper (D 8) (R 8) [66,5,160,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10018 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 56 81 424 488 424 424), lower := (rows 67 7 164 56 81 32 64 128 256), losses := [] }

theorem u10018 : Upper (D 8) (R 8) [66,5,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10019 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 56 88 417 481 417 417), lower := (rows 67 7 164 56 88 32 64 128 256), losses := [] }

theorem u10019 : Upper (D 8) (R 8) [66,5,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10019
end Delivery.IrregularNine14.P08
