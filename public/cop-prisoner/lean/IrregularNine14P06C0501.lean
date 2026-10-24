import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0193
import IrregularNine14P06C0194

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30060 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 338, targets := 32 },{ cop := 1, region := 488, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 22 37 168 81 358 326 454 326), lower := (rows 11 22 37 168 81 32 64 128 256), losses := [] }

theorem u30060 : Upper (D 6) (R 6) [10,20,33,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30060
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30061 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 22 37 168 82 357 325 453 325), lower := (rows 11 22 37 168 82 32 64 128 256), losses := [] }

theorem u30061 : Upper (D 6) (R 6) [10,20,33,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30061
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30062 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 168 84 355 323 451 323), lower := (rows 11 22 37 168 84 32 64 128 256), losses := [] }

theorem u30062 : Upper (D 6) (R 6) [10,20,33,160,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30062
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30063 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 338, targets := 32 },{ cop := 1, region := 232, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 22 37 168 273 102 70 198 326), lower := (rows 11 22 37 168 273 32 64 128 256), losses := [] }

theorem u30063 : Upper (D 6) (R 6) [10,20,33,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30063
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30064 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 22 37 168 274 101 69 197 325), lower := (rows 11 22 37 168 274 32 64 128 256), losses := [] }

theorem u30064 : Upper (D 6) (R 6) [10,20,33,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30064
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30065 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 168 276 99 67 195 323), lower := (rows 11 22 37 168 276 32 64 128 256), losses := [] }

theorem u30065 : Upper (D 6) (R 6) [10,20,33,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30065
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30066 : Route 9 := (fun mask => (mask,id))

def c30066 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30066 : Upper (D 6) (R 6) [10,20,33,160,320] 13 := by
  apply FastRouting.sound _ _ [10,20,33,160,320] 13 (by decide) (choices 1) [1,2,4,64] r30066 c30066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11611
  · exact u11612
  · exact u11613
  · exact u11614

def b30067 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 200 19 356 356 484 356), lower := (rows 11 22 37 200 19 32 64 128 256), losses := [] }

theorem u30067 : Upper (D 6) (R 6) [10,20,33,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30067
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30068 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 200 21 354 354 482 354), lower := (rows 11 22 37 200 21 32 64 128 256), losses := [] }

theorem u30068 : Upper (D 6) (R 6) [10,20,33,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30068
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30069 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 200 22 353 353 481 353), lower := (rows 11 22 37 200 22 32 64 128 256), losses := [] }

theorem u30069 : Upper (D 6) (R 6) [10,20,33,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30069
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30070 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 18, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 22 37 200 49 358 326 454 326), lower := (rows 11 22 37 200 49 32 64 128 256), losses := [] }

theorem u30070 : Upper (D 6) (R 6) [10,20,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30070
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30071 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 200 50 357 325 453 325), lower := (rows 11 22 37 200 50 32 64 128 256), losses := [] }

theorem u30071 : Upper (D 6) (R 6) [10,20,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30071
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30072 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 200 52 355 323 451 323), lower := (rows 11 22 37 200 52 32 64 128 256), losses := [] }

theorem u30072 : Upper (D 6) (R 6) [10,20,33,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30072
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30073 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 294, targets := 64 },{ cop := 1, region := 488, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 22 37 200 81 294 358 422 294), lower := (rows 11 22 37 200 81 32 64 128 256), losses := [] }

theorem u30073 : Upper (D 6) (R 6) [10,20,33,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30073
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30074 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 22 37 200 82 293 357 421 293), lower := (rows 11 22 37 200 82 32 64 128 256), losses := [] }

theorem u30074 : Upper (D 6) (R 6) [10,20,33,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30074
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30075 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 200 84 291 355 419 291), lower := (rows 11 22 37 200 84 32 64 128 256), losses := [] }

theorem u30075 : Upper (D 6) (R 6) [10,20,33,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30075
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30076 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 0, region := 292, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 22 37 200 112 295 327 391 263), lower := (rows 11 22 37 200 112 32 64 128 256), losses := [] }

theorem u30076 : Upper (D 6) (R 6) [10,20,33,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30076
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30077 : Route 9 := (fun mask => (mask,id))

def c30077 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30077 : Upper (D 6) (R 6) [10,20,33,192,257] 13 := by
  apply FastRouting.sound _ _ [10,20,33,192,257] 13 (by decide) (choices 1) [2,4,64] r30077 c30077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11615
  · exact u11616
  · exact u11617

def r30078 : Route 9 := (fun mask => (mask,id))

def c30078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30078 : Upper (D 6) (R 6) [10,20,33,192,258] 13 := by
  apply FastRouting.sound _ _ [10,20,33,192,258] 13 (by decide) (choices 1) [1,4,64] r30078 c30078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11618
  · exact u11619
  · exact u11620

def b30079 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 200 276 99 99 227 355), lower := (rows 11 22 37 200 276 32 64 128 256), losses := [] }

theorem u30079 : Upper (D 6) (R 6) [10,20,33,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30079
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30080 : Route 9 := (fun mask => (mask,id))

def c30080 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30080 : Upper (D 6) (R 6) [10,20,33,192,288] 13 := by
  apply FastRouting.sound _ _ [10,20,33,192,288] 13 (by decide) (choices 1) [1,2,4,64] r30080 c30080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11621
  · exact u11622
  · exact u11623
  · exact u11624

def r30081 : Route 9 := (fun mask => (mask,id))

def c30081 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30081 : Upper (D 6) (R 6) [10,20,33,192,320] 13 := by
  apply FastRouting.sound _ _ [10,20,33,192,320] 13 (by decide) (choices 1) [1,2,4] r30081 c30081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11625
  · exact u11626
  · exact u11627

def b30082 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 392 19 100 100 228 356), lower := (rows 11 22 37 392 19 32 64 128 256), losses := [] }

theorem u30082 : Upper (D 6) (R 6) [10,20,33,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30082
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30083 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 392 21 98 98 226 354), lower := (rows 11 22 37 392 21 32 64 128 256), losses := [] }

theorem u30083 : Upper (D 6) (R 6) [10,20,33,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30083
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30084 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 392 22 97 97 225 353), lower := (rows 11 22 37 392 22 32 64 128 256), losses := [] }

theorem u30084 : Upper (D 6) (R 6) [10,20,33,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30084
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30085 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 18, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 22 37 392 49 102 70 198 326), lower := (rows 11 22 37 392 49 32 64 128 256), losses := [] }

theorem u30085 : Upper (D 6) (R 6) [10,20,33,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30085
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30086 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 392 50 101 69 197 325), lower := (rows 11 22 37 392 50 32 64 128 256), losses := [] }

theorem u30086 : Upper (D 6) (R 6) [10,20,33,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30086
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30087 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 392 52 99 67 195 323), lower := (rows 11 22 37 392 52 32 64 128 256), losses := [] }

theorem u30087 : Upper (D 6) (R 6) [10,20,33,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30087
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30088 : Route 9 := (fun mask => (mask,id))

def c30088 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30088 : Upper (D 6) (R 6) [10,20,33,384,65] 13 := by
  apply FastRouting.sound _ _ [10,20,33,384,65] 13 (by decide) (choices 1) [2,4,64] r30088 c30088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11628
  · exact u11629
  · exact u11630

def r30089 : Route 9 := (fun mask => (mask,id))

def c30089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30089 : Upper (D 6) (R 6) [10,20,33,384,66] 13 := by
  apply FastRouting.sound _ _ [10,20,33,384,66] 13 (by decide) (choices 1) [1,4,64] r30089 c30089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11631
  · exact u11632
  · exact u11633

def b30090 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 392 84 99 99 227 355), lower := (rows 11 22 37 392 84 32 64 128 256), losses := [] }

theorem u30090 : Upper (D 6) (R 6) [10,20,33,384,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30090
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30091 : Route 9 := (fun mask => (mask,id))

def c30091 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30091 : Upper (D 6) (R 6) [10,20,33,384,96] 13 := by
  apply FastRouting.sound _ _ [10,20,33,384,96] 13 (by decide) (choices 1) [1,2,4,64] r30091 c30091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11634
  · exact u11635
  · exact u11636
  · exact u11637

def b30092 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 488, targets := 6 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 38 73 21 480 480 480 480), lower := (rows 11 22 38 73 21 32 64 128 256), losses := [] }

theorem u30092 : Upper (D 6) (R 6) [10,20,34,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30092
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30093 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 4, region := 6, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 38 73 49 484 452 452 452), lower := (rows 11 22 38 73 49 32 64 128 256), losses := [] }

theorem u30093 : Upper (D 6) (R 6) [10,20,34,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30093
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30094 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 22, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 73 52 481 449 449 449), lower := (rows 11 22 38 73 52 32 64 128 256), losses := [] }

theorem u30094 : Upper (D 6) (R 6) [10,20,34,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30094
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30095 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 22 38 73 81 420 484 420 420), lower := (rows 11 22 38 73 81 32 64 128 256), losses := [] }

theorem u30095 : Upper (D 6) (R 6) [10,20,34,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30095
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30096 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 38 73 84 417 481 417 417), lower := (rows 11 22 38 73 84 32 64 128 256), losses := [] }

theorem u30096 : Upper (D 6) (R 6) [10,20,34,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30096
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30097 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 73 112 421 453 389 389), lower := (rows 11 22 38 73 112 32 64 128 256), losses := [] }

theorem u30097 : Upper (D 6) (R 6) [10,20,34,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30097
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30098 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 38 73 145 356 356 484 356), lower := (rows 11 22 38 73 145 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 70 134 262), good := (rows 505 500 484 89 153 32 64 128 256) }] }

theorem u30098 : Upper (D 6) (R 6) [10,20,34,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30098
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30099 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 73 148 353 353 481 353), lower := (rows 11 22 38 73 148 32 64 128 256), losses := [] }

theorem u30099 : Upper (D 6) (R 6) [10,20,34,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30099
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30100 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 73 176 357 325 453 325), lower := (rows 11 22 38 73 176 32 64 128 256), losses := [] }

theorem u30100 : Upper (D 6) (R 6) [10,20,34,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30100
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30101 : Route 9 := (fun mask => (mask,id))

def c30101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30101 : Upper (D 6) (R 6) [10,20,34,65,192] 13 := by
  apply FastRouting.sound _ _ [10,20,34,65,192] 13 (by decide) (choices 1) [1,4,256] r30101 c30101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11638
  · exact u11639
  · exact u11640

def r30102 : Route 9 := (fun mask => (mask,id))

def c30102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30102 : Upper (D 6) (R 6) [10,20,34,65,384] 13 := by
  apply FastRouting.sound _ _ [10,20,34,65,384] 13 (by decide) (choices 1) [1,4,64] r30102 c30102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11641
  · exact u11642
  · exact u11643

def b30103 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 76 49 481 449 449 449), lower := (rows 11 22 38 76 49 32 64 128 256), losses := [] }

theorem u30103 : Upper (D 6) (R 6) [10,20,34,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30103
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30104 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 38 76 81 417 481 417 417), lower := (rows 11 22 38 76 81 32 64 128 256), losses := [] }

theorem u30104 : Upper (D 6) (R 6) [10,20,34,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30104
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30105 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 38 76 112 417 449 385 385), lower := (rows 11 22 38 76 112 32 64 128 256), losses := [] }

theorem u30105 : Upper (D 6) (R 6) [10,20,34,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30105
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30106 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 496, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 38 76 145 353 353 481 353), lower := (rows 11 22 38 76 145 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 49 81 145 273), good := (rows 505 508 44 76 497 32 64 128 256) }] }

theorem u30106 : Upper (D 6) (R 6) [10,20,34,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30106
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30107 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 76 176 353 321 449 321), lower := (rows 11 22 38 76 176 32 64 128 256), losses := [] }

theorem u30107 : Upper (D 6) (R 6) [10,20,34,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30107
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30108 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 496, targets := 6 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 22 38 76 208 289 353 417 289), lower := (rows 11 22 38 76 208 32 64 128 256), losses := [] }

theorem u30108 : Upper (D 6) (R 6) [10,20,34,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30108
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30109 : Route 9 := (fun mask => (mask,id))

def c30109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30109 : Upper (D 6) (R 6) [10,20,34,68,384] 13 := by
  apply FastRouting.sound _ _ [10,20,34,68,384] 13 (by decide) (choices 1) [1,64] r30109 c30109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11644
  · exact u11645

def b30110 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 38 104 21 481 449 449 449), lower := (rows 11 22 38 104 21 32 64 128 256), losses := [] }

theorem u30110 : Upper (D 6) (R 6) [10,20,34,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30110
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30111 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c30111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30111 : Upper (D 6) (R 6) [10,20,34,96,65] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,65] 13 (by decide) (choices 1) [1,4,128] r30111 c30111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11646
  · exact u11647
  · exact u11648

def b30112 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 104 84 417 449 385 385), lower := (rows 11 22 38 104 84 32 64 128 256), losses := [] }

theorem u30112 : Upper (D 6) (R 6) [10,20,34,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30112
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30113 : Route 9 := (fun mask => (mask,id))

def c30113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30113 : Upper (D 6) (R 6) [10,20,34,96,129] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,129] 13 (by decide) (choices 1) [1,4,64,256] r30113 c30113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11649
  · exact u11650
  · exact u11651
  · exact u11652

def b30114 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 104 148 353 321 449 321), lower := (rows 11 22 38 104 148 32 64 128 256), losses := [] }

theorem u30114 : Upper (D 6) (R 6) [10,20,34,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30114
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30115 : Route 9 := (fun mask => (mask,id))

def c30115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30115 : Upper (D 6) (R 6) [10,20,34,96,192] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,192] 13 (by decide) (choices 1) [1,4,256] r30115 c30115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11653
  · exact u11654
  · exact u11655

def r30116 : Route 9 := (fun mask => (mask,id))

def c30116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30116 : Upper (D 6) (R 6) [10,20,34,96,384] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,384] 13 (by decide) (choices 1) [1,4,64] r30116 c30116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11656
  · exact u11657
  · exact u11658

def b30117 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 488, targets := 6 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 38 137 21 352 352 480 352), lower := (rows 11 22 38 137 21 32 64 128 256), losses := [] }

theorem u30117 : Upper (D 6) (R 6) [10,20,34,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30117
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30118 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 4, region := 6, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 38 137 49 356 324 452 324), lower := (rows 11 22 38 137 49 32 64 128 256), losses := [] }

theorem u30118 : Upper (D 6) (R 6) [10,20,34,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30118
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30119 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 22, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 137 52 353 321 449 321), lower := (rows 11 22 38 137 52 32 64 128 256), losses := [] }

theorem u30119 : Upper (D 6) (R 6) [10,20,34,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30119
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30119
end Delivery.IrregularNine14.P06
