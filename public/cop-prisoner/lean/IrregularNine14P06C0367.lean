import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0108
import IrregularNine14P06C0109

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22020 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 25 22 288 100 228 356), lower := (rows 35 131 76 25 22 288 64 128 256), losses := [] }

theorem u22020 : Upper (D 6) (R 6) [34,129,72,17,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22020 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22021 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 25 52 34 324 452 324), lower := (rows 35 131 76 25 52 34 64 128 256), losses := [] }

theorem u22021 : Upper (D 6) (R 6) [34,129,72,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22022 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 76 25 52 36 322 450 322), lower := (rows 35 131 76 25 52 36 64 128 256), losses := [] }

theorem u22022 : Upper (D 6) (R 6) [34,129,72,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22023 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 25 52 96 326 390 262), lower := (rows 35 131 76 25 52 96 64 128 256), losses := [] }

theorem u22023 : Upper (D 6) (R 6) [34,129,72,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22024 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 25 52 288 70 198 326), lower := (rows 35 131 76 25 52 288 64 128 256), losses := [] }

theorem u22024 : Upper (D 6) (R 6) [34,129,72,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22024 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22025 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 76 25 274 36 100 228 356), lower := (rows 35 131 76 25 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 44 108 172 300), good := (rows 498 146 492 508 274 484 64 128 256) }] }

theorem u22025 : Upper (D 6) (R 6) [34,129,72,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22026 : Route 9 := (fun mask => (mask,id))

def c22026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22026 : Upper (D 6) (R 6) [34,129,72,17,258,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,258,64] 13 (by decide) (choices 1) [4,32] r22026 c22026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6530
  · exact u6531

def b22027 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 25 276 34 100 228 356), lower := (rows 35 131 76 25 276 34 64 128 256), losses := [] }

theorem u22027 : Upper (D 6) (R 6) [34,129,72,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22028 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 25 276 36 98 226 354), lower := (rows 35 131 76 25 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 65 129 257), good := (rows 482 450 124 508 308 36 64 128 256) }] }

theorem u22028 : Upper (D 6) (R 6) [34,129,72,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22029 : Route 9 := (fun mask => (mask,id))

def c22029 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22029 : Upper (D 6) (R 6) [34,129,72,17,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,260,64] 13 (by decide) (choices 1) [2,4,32] r22029 c22029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6532
  · exact u6533
  · exact u6534

def b22030 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 25 304 34 68 196 324), lower := (rows 35 131 76 25 304 34 64 128 256), losses := [] }

theorem u22030 : Upper (D 6) (R 6) [34,129,72,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22031 : Route 9 := (fun mask => (mask,id))

def c22031 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22031 : Upper (D 6) (R 6) [34,129,72,17,288,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,288,4] 13 (by decide) (choices 1) [2,4] r22031 c22031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6535
  · exact u6536

def r22032 : Route 9 := (fun mask => (mask,id))

def c22032 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22032 : Upper (D 6) (R 6) [34,129,72,17,288,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,288,64] 13 (by decide) (choices 1) [2,4] r22032 c22032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6537
  · exact u6538

def b22033 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 25 336 34 100 164 292), lower := (rows 35 131 76 25 336 34 64 128 256), losses := [] }

theorem u22033 : Upper (D 6) (R 6) [34,129,72,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22034 : Route 9 := (fun mask => (mask,id))

def c22034 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22034 : Upper (D 6) (R 6) [34,129,72,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,320,4] 13 (by decide) (choices 1) [2,4,32] r22034 c22034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6539
  · exact u6540
  · exact u6541

def b22035 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 5, region := 451, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 26 21 36 352 480 352), lower := (rows 35 131 76 26 21 36 64 128 256), losses := [] }

theorem u22035 : Upper (D 6) (R 6) [34,129,72,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22036 : Route 9 := (fun mask => (mask,id))

def c22036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u22036 : Upper (D 6) (R 6) [34,129,72,18,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,5,64] 13 (by decide) (choices 1) [4,32,256] r22036 c22036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6542
  · exact u6543
  · exact u6544

def b22037 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 26 21 288 100 228 356), lower := (rows 35 131 76 26 21 288 64 128 256), losses := [] }

theorem u22037 : Upper (D 6) (R 6) [34,129,72,18,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22037 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22038 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 52 33 324 452 324), lower := (rows 35 131 76 26 52 33 64 128 256), losses := [] }

theorem u22038 : Upper (D 6) (R 6) [34,129,72,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22039 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 76 26 52 36 321 449 321), lower := (rows 35 131 76 26 52 36 64 128 256), losses := [] }

theorem u22039 : Upper (D 6) (R 6) [34,129,72,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22040 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 26 52 96 325 389 261), lower := (rows 35 131 76 26 52 96 64 128 256), losses := [] }

theorem u22040 : Upper (D 6) (R 6) [34,129,72,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22041 : Route 9 := (fun mask => (mask,id))

def c22041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22041 : Upper (D 6) (R 6) [34,129,72,18,36,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,36,256] 13 (by decide) (choices 1) [1,4] r22041 c22041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6545
  · exact u6546

def b22042 : PairBound 9 := { available := 260, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 112 33 324 388 260), lower := (rows 35 131 76 26 112 33 64 128 256), losses := [] }

theorem u22042 : Upper (D 6) (R 6) [34,129,72,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22043 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 76 26 112 36 325 389 261), lower := (rows 35 131 76 26 112 36 64 128 256), losses := [] }

theorem u22043 : Upper (D 6) (R 6) [34,129,72,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22044 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 76 26 112 288 69 133 261), lower := (rows 35 131 76 26 112 288 64 128 256), losses := [] }

theorem u22044 : Upper (D 6) (R 6) [34,129,72,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22044 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22045 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 131 76 26 273 36 100 228 356), lower := (rows 35 131 76 26 273 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 44 108 172 300), good := (rows 497 145 492 508 273 484 64 128 256) }] }

theorem u22045 : Upper (D 6) (R 6) [34,129,72,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22046 : Route 9 := (fun mask => (mask,id))

def c22046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22046 : Upper (D 6) (R 6) [34,129,72,18,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,257,64] 13 (by decide) (choices 1) [4,32] r22046 c22046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6547
  · exact u6548

def b22047 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 276 33 100 228 356), lower := (rows 35 131 76 26 276 33 64 128 256), losses := [] }

theorem u22047 : Upper (D 6) (R 6) [34,129,72,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22048 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 276 36 97 225 353), lower := (rows 35 131 76 26 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 131 45 59 308 36 0 128 256) }] }

theorem u22048 : Upper (D 6) (R 6) [34,129,72,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22049 : Route 9 := (fun mask => (mask,id))

def c22049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22049 : Upper (D 6) (R 6) [34,129,72,18,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,260,64] 13 (by decide) (choices 1) [1,4,32] r22049 c22049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6549
  · exact u6550
  · exact u6551

def b22050 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 304 33 68 196 324), lower := (rows 35 131 76 26 304 33 64 128 256), losses := [] }

theorem u22050 : Upper (D 6) (R 6) [34,129,72,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22051 : Route 9 := (fun mask => (mask,id))

def c22051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22051 : Upper (D 6) (R 6) [34,129,72,18,288,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,288,4] 13 (by decide) (choices 1) [1,4] r22051 c22051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6552
  · exact u6553

def r22052 : Route 9 := (fun mask => (mask,id))

def c22052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22052 : Upper (D 6) (R 6) [34,129,72,18,288,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,288,64] 13 (by decide) (choices 1) [1,4] r22052 c22052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6554
  · exact u6555

def b22053 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 336 33 100 164 292), lower := (rows 35 131 76 26 336 33 64 128 256), losses := [] }

theorem u22053 : Upper (D 6) (R 6) [34,129,72,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22054 : Route 9 := (fun mask => (mask,id))

def c22054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22054 : Upper (D 6) (R 6) [34,129,72,18,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,320,4] 13 (by decide) (choices 1) [1,4,32] r22054 c22054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6556
  · exact u6557
  · exact u6558

def b22055 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 273 34 100 228 356), lower := (rows 35 131 76 28 273 34 64 128 256), losses := [] }

theorem u22055 : Upper (D 6) (R 6) [34,129,72,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22056 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 28 273 36 98 226 354), lower := (rows 35 131 76 28 273 36 64 128 256), losses := [] }

theorem u22056 : Upper (D 6) (R 6) [34,129,72,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22057 : Route 9 := (fun mask => (mask,id))

def c22057 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22057 : Upper (D 6) (R 6) [34,129,72,20,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,257,64] 13 (by decide) (choices 1) [2,4,32] r22057 c22057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6559
  · exact u6560
  · exact u6561

def b22058 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 274 33 100 228 356), lower := (rows 35 131 76 28 274 33 64 128 256), losses := [] }

theorem u22058 : Upper (D 6) (R 6) [34,129,72,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22059 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 28 274 36 97 225 353), lower := (rows 35 131 76 28 274 36 64 128 256), losses := [] }

theorem u22059 : Upper (D 6) (R 6) [34,129,72,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22060 : Route 9 := (fun mask => (mask,id))

def c22060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22060 : Upper (D 6) (R 6) [34,129,72,20,258,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,258,64] 13 (by decide) (choices 1) [1,4,32] r22060 c22060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6562
  · exact u6563
  · exact u6564

def b22061 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 304 33 70 198 326), lower := (rows 35 131 76 28 304 33 64 128 256), losses := [] }

theorem u22061 : Upper (D 6) (R 6) [34,129,72,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22062 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 304 34 69 197 325), lower := (rows 35 131 76 28 304 34 64 128 256), losses := [] }

theorem u22062 : Upper (D 6) (R 6) [34,129,72,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22063 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 28 304 36 67 195 323), lower := (rows 35 131 76 28 304 36 64 128 256), losses := [] }

theorem u22063 : Upper (D 6) (R 6) [34,129,72,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22064 : Route 9 := (fun mask => (mask,id))

def c22064 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22064 : Upper (D 6) (R 6) [34,129,72,20,288,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,288,64] 13 (by decide) (choices 1) [1,2,4] r22064 c22064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6565
  · exact u6566
  · exact u6567

def b22065 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 22 33 336 464 336), lower := (rows 35 131 76 44 22 33 64 128 256), losses := [] }

theorem u22065 : Upper (D 6) (R 6) [34,129,72,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22066 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 44 22 48 321 449 321), lower := (rows 35 131 76 44 22 48 64 128 256), losses := [] }

theorem u22066 : Upper (D 6) (R 6) [34,129,72,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22066 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22067 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 44 22 96 337 401 273), lower := (rows 35 131 76 44 22 96 64 128 256), losses := [] }

theorem u22067 : Upper (D 6) (R 6) [34,129,72,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22068 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 44 22 288 81 209 337), lower := (rows 35 131 76 44 22 288 64 128 256), losses := [] }

theorem u22068 : Upper (D 6) (R 6) [34,129,72,36,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22068 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22069 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 81 34 340 404 276), lower := (rows 35 131 76 44 81 34 64 128 256), losses := [] }

theorem u22069 : Upper (D 6) (R 6) [34,129,72,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22070 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 76 44 81 36 338 402 274), lower := (rows 35 131 76 44 81 36 64 128 256), losses := [] }

theorem u22070 : Upper (D 6) (R 6) [34,129,72,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22071 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 44 81 48 326 390 262), lower := (rows 35 131 76 44 81 48 64 128 256), losses := [] }

theorem u22071 : Upper (D 6) (R 6) [34,129,72,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22071 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22072 : Route 9 := (fun mask => (mask,id))

def c22072 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22072 : Upper (D 6) (R 6) [34,129,72,36,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,65,256] 13 (by decide) (choices 1) [2,4,16] r22072 c22072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6568
  · exact u6569
  · exact u6570

def b22073 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 82 33 340 404 276), lower := (rows 35 131 76 44 82 33 64 128 256), losses := [] }

theorem u22073 : Upper (D 6) (R 6) [34,129,72,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22074 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 76 44 82 36 337 401 273), lower := (rows 35 131 76 44 82 36 64 128 256), losses := [] }

theorem u22074 : Upper (D 6) (R 6) [34,129,72,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22075 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 44 82 48 325 389 261), lower := (rows 35 131 76 44 82 48 64 128 256), losses := [] }

theorem u22075 : Upper (D 6) (R 6) [34,129,72,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22075 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22076 : Route 9 := (fun mask => (mask,id))

def c22076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22076 : Upper (D 6) (R 6) [34,129,72,36,66,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,66,256] 13 (by decide) (choices 1) [1,4,16] r22076 c22076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6571
  · exact u6572
  · exact u6573

def b22077 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 273 34 84 212 340), lower := (rows 35 131 76 44 273 34 64 128 256), losses := [] }

theorem u22077 : Upper (D 6) (R 6) [34,129,72,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22078 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 76 44 273 36 82 210 338), lower := (rows 35 131 76 44 273 36 64 128 256), losses := [] }

theorem u22078 : Upper (D 6) (R 6) [34,129,72,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22079 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 44 273 48 70 198 326), lower := (rows 35 131 76 44 273 48 64 128 256), losses := [] }

theorem u22079 : Upper (D 6) (R 6) [34,129,72,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22079 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22079
end Delivery.IrregularNine14.P06
