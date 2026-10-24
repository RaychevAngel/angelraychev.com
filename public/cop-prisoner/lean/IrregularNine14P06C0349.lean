import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0103

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20940 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 100 26 145 288 69 133 261), lower := (rows 35 74 100 26 145 288 64 128 256), losses := [] }

theorem u20940 : Upper (D 6) (R 6) [34,72,96,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20940 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20941 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 100 26 148 33 325 389 261), lower := (rows 35 74 100 26 148 33 64 128 256), losses := [] }

theorem u20941 : Upper (D 6) (R 6) [34,72,96,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20942 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 100 26 148 36 321 385 257), lower := (rows 35 74 100 26 148 36 64 128 256), losses := [] }

theorem u20942 : Upper (D 6) (R 6) [34,72,96,18,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20943 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 100 26 148 288 69 133 261), lower := (rows 35 74 100 26 148 288 64 128 256), losses := [] }

theorem u20943 : Upper (D 6) (R 6) [34,72,96,18,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20943 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20944 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 100 26 400 33 69 133 261), lower := (rows 35 74 100 26 400 33 64 128 256), losses := [] }

theorem u20944 : Upper (D 6) (R 6) [34,72,96,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20945 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 100 26 400 36 69 133 261), lower := (rows 35 74 100 26 400 36 64 128 256), losses := [] }

theorem u20945 : Upper (D 6) (R 6) [34,72,96,18,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20946 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 322, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 74 100 28 145 33 326 390 262), lower := (rows 35 74 100 28 145 33 64 128 256), losses := [] }

theorem u20946 : Upper (D 6) (R 6) [34,72,96,20,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20947 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 28 145 34 325 389 261), lower := (rows 35 74 100 28 145 34 64 128 256), losses := [] }

theorem u20947 : Upper (D 6) (R 6) [34,72,96,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20948 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 400, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 74 100 28 145 36 323 387 259), lower := (rows 35 74 100 28 145 36 64 128 256), losses := [] }

theorem u20948 : Upper (D 6) (R 6) [34,72,96,20,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20949 : Route 9 := (fun mask => (mask,id))

def c20949 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20949 : Upper (D 6) (R 6) [34,72,96,20,129,256] 13 := by
  apply FastRouting.sound _ _ [34,72,96,20,129,256] 13 (by decide) (choices 1) [1,2,4] r20949 c20949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6184
  · exact u6185
  · exact u6186

def b20950 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 100 28 146 33 325 389 261), lower := (rows 35 74 100 28 146 33 64 128 256), losses := [] }

theorem u20950 : Upper (D 6) (R 6) [34,72,96,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20951 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 74 100 28 146 36 321 385 257), lower := (rows 35 74 100 28 146 36 64 128 256), losses := [] }

theorem u20951 : Upper (D 6) (R 6) [34,72,96,20,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20952 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(0,6),(2,1)], upper := (rows 35 74 100 28 146 288 69 133 261), lower := (rows 35 74 100 28 146 288 64 128 256), losses := [{ target := 6, region := (rows 19 2 4 8 18 298 0 136 264), good := (rows 51 443 36 445 179 288 0 128 288) }] }

theorem u20952 : Upper (D 6) (R 6) [34,72,96,20,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20952 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20953 : Route 9 := (fun mask => (mask,id))

def c20953 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20953 : Upper (D 6) (R 6) [34,72,96,20,384,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,20,384,1] 13 (by decide) (choices 1) [1,2,4] r20953 c20953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6187
  · exact u6188
  · exact u6189

def b20954 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 28 400 34 69 133 261), lower := (rows 35 74 100 28 400 34 64 128 256), losses := [] }

theorem u20954 : Upper (D 6) (R 6) [34,72,96,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20955 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 400, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 74 100 28 400 36 67 131 259), lower := (rows 35 74 100 28 400 36 64 128 256), losses := [] }

theorem u20955 : Upper (D 6) (R 6) [34,72,96,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20956 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 137 21 34 340 404 276), lower := (rows 35 74 100 137 21 34 64 128 256), losses := [] }

theorem u20956 : Upper (D 6) (R 6) [34,72,96,129,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20957 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 100 137 21 36 338 402 274), lower := (rows 35 74 100 137 21 36 64 128 256), losses := [] }

theorem u20957 : Upper (D 6) (R 6) [34,72,96,129,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20958 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 100 137 21 48 326 390 262), lower := (rows 35 74 100 137 21 48 64 128 256), losses := [] }

theorem u20958 : Upper (D 6) (R 6) [34,72,96,129,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20958 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20959 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 100 137 21 288 86 150 278), lower := (rows 35 74 100 137 21 288 64 128 256), losses := [] }

theorem u20959 : Upper (D 6) (R 6) [34,72,96,129,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20959 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20960 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 100 137 22 33 340 404 276), lower := (rows 35 74 100 137 22 33 64 128 256), losses := [] }

theorem u20960 : Upper (D 6) (R 6) [34,72,96,129,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20961 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 52, targets := 1 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 74 100 137 22 36 337 401 273), lower := (rows 35 74 100 137 22 36 64 128 256), losses := [] }

theorem u20961 : Upper (D 6) (R 6) [34,72,96,129,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20962 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 100 137 22 48 325 389 261), lower := (rows 35 74 100 137 22 48 64 128 256), losses := [] }

theorem u20962 : Upper (D 6) (R 6) [34,72,96,129,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20962 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20963 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 74 100 137 22 288 85 149 277), lower := (rows 35 74 100 137 22 288 64 128 256), losses := [] }

theorem u20963 : Upper (D 6) (R 6) [34,72,96,129,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20963 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20964 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 137 273 34 84 148 276), lower := (rows 35 74 100 137 273 34 64 128 256), losses := [] }

theorem u20964 : Upper (D 6) (R 6) [34,72,96,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20965 : Route 9 := (fun mask => (mask,id))

def c20965 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20965 : Upper (D 6) (R 6) [34,72,96,129,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,257,4] 13 (by decide) (choices 1) [2,4,16] r20965 c20965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6190
  · exact u6191
  · exact u6192

def b20966 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 74 100 137 273 48 70 134 262), lower := (rows 35 74 100 137 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 21 8 16 48 73 137 265), good := (rows 486 458 100 462 500 52 64 128 256) }] }

theorem u20966 : Upper (D 6) (R 6) [34,72,96,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20966 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20967 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 100 137 274 33 84 148 276), lower := (rows 35 74 100 137 274 33 64 128 256), losses := [] }

theorem u20967 : Upper (D 6) (R 6) [34,72,96,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20968 : Route 9 := (fun mask => (mask,id))

def c20968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20968 : Upper (D 6) (R 6) [34,72,96,129,258,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,258,4] 13 (by decide) (choices 1) [1,4,16] r20968 c20968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6193
  · exact u6194
  · exact u6195

def b20969 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 100 137 274 48 69 133 261), lower := (rows 35 74 100 137 274 48 64 128 256), losses := [] }

theorem u20969 : Upper (D 6) (R 6) [34,72,96,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20969 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20970 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 100 137 276 33 86 150 278), lower := (rows 35 74 100 137 276 33 64 128 256), losses := [] }

theorem u20970 : Upper (D 6) (R 6) [34,72,96,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20971 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 137 276 34 85 149 277), lower := (rows 35 74 100 137 276 34 64 128 256), losses := [] }

theorem u20971 : Upper (D 6) (R 6) [34,72,96,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20972 : Route 9 := (fun mask => (mask,id))

def c20972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20972 : Upper (D 6) (R 6) [34,72,96,129,260,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,260,4] 13 (by decide) (choices 1) [1,2,16] r20972 c20972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6196
  · exact u6197
  · exact u6198

def r20973 : Route 9 := (fun mask => (mask,id))

def c20973 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20973 : Upper (D 6) (R 6) [34,72,96,129,260,16] 13 := by
  apply FastRouting.sound _ _ [34,72,96,129,260,16] 13 (by decide) (choices 1) [1,2,4] r20973 c20973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6199
  · exact u6200
  · exact u6201

def b20974 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 100 138 273 33 84 148 276), lower := (rows 35 74 100 138 273 33 64 128 256), losses := [] }

theorem u20974 : Upper (D 6) (R 6) [34,72,96,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20975 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 100 138 273 36 85 149 277), lower := (rows 35 74 100 138 273 36 64 128 256), losses := [] }

theorem u20975 : Upper (D 6) (R 6) [34,72,96,130,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20976 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 100 138 273 48 69 133 261), lower := (rows 35 74 100 138 273 48 64 128 256), losses := [] }

theorem u20976 : Upper (D 6) (R 6) [34,72,96,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20976 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20977 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 100 138 276 33 85 149 277), lower := (rows 35 74 100 138 276 33 64 128 256), losses := [] }

theorem u20977 : Upper (D 6) (R 6) [34,72,96,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20978 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 100 138 276 36 81 145 273), lower := (rows 35 74 100 138 276 36 64 128 256), losses := [] }

theorem u20978 : Upper (D 6) (R 6) [34,72,96,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20979 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 100 138 276 48 69 133 261), lower := (rows 35 74 100 138 276 48 64 128 256), losses := [] }

theorem u20979 : Upper (D 6) (R 6) [34,72,96,130,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20979 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20980 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 140 21 33 338 402 274), lower := (rows 35 74 100 140 21 33 64 128 256), losses := [] }

theorem u20980 : Upper (D 6) (R 6) [34,72,96,132,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20981 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 140 21 34 337 401 273), lower := (rows 35 74 100 140 21 34 64 128 256), losses := [] }

theorem u20981 : Upper (D 6) (R 6) [34,72,96,132,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20982 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 100 140 21 48 323 387 259), lower := (rows 35 74 100 140 21 48 64 128 256), losses := [] }

theorem u20982 : Upper (D 6) (R 6) [34,72,96,132,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20982 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20983 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 100 140 21 288 83 147 275), lower := (rows 35 74 100 140 21 288 64 128 256), losses := [] }

theorem u20983 : Upper (D 6) (R 6) [34,72,96,132,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20983 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20984 : Route 9 := (fun mask => (mask,id))

def c20984 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20984 : Upper (D 6) (R 6) [34,72,96,132,257,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,257,1] 13 (by decide) (choices 1) [2,4,16] r20984 c20984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6202
  · exact u6203
  · exact u6204

def b20985 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 140 273 34 85 149 277), lower := (rows 35 74 100 140 273 34 64 128 256), losses := [] }

theorem u20985 : Upper (D 6) (R 6) [34,72,96,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20986 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 272, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 74 100 140 273 36 83 147 275), lower := (rows 35 74 100 140 273 36 64 128 256), losses := [] }

theorem u20986 : Upper (D 6) (R 6) [34,72,96,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20987 : Route 9 := (fun mask => (mask,id))

def c20987 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20987 : Upper (D 6) (R 6) [34,72,96,132,257,16] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,257,16] 13 (by decide) (choices 1) [1,2,4] r20987 c20987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6205
  · exact u6206
  · exact u6207

def r20988 : Route 9 := (fun mask => (mask,id))

def c20988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20988 : Upper (D 6) (R 6) [34,72,96,132,258,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,258,1] 13 (by decide) (choices 1) [1,4,16] r20988 c20988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6208
  · exact u6209
  · exact u6210

def b20989 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 74 100 140 274 36 81 145 273), lower := (rows 35 74 100 140 274 36 64 128 256), losses := [] }

theorem u20989 : Upper (D 6) (R 6) [34,72,96,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20990 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 100 140 274 48 69 133 261), lower := (rows 35 74 100 140 274 48 64 128 256), losses := [] }

theorem u20990 : Upper (D 6) (R 6) [34,72,96,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20990 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20991 : Route 9 := (fun mask => (mask,id))

def c20991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20991 : Upper (D 6) (R 6) [34,72,96,132,260,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,260,1] 13 (by decide) (choices 1) [1,2,16] r20991 c20991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6211
  · exact u6212
  · exact u6213

def b20992 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 140 276 34 81 145 273), lower := (rows 35 74 100 140 276 34 64 128 256), losses := [] }

theorem u20992 : Upper (D 6) (R 6) [34,72,96,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20993 : Route 9 := (fun mask => (mask,id))

def c20993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20993 : Upper (D 6) (R 6) [34,72,96,132,260,16] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,260,16] 13 (by decide) (choices 1) [1,2] r20993 c20993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6214
  · exact u6215

def b20994 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 152 21 33 326 390 262), lower := (rows 35 74 100 152 21 33 64 128 256), losses := [] }

theorem u20994 : Upper (D 6) (R 6) [34,72,96,144,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20995 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 152 21 34 325 389 261), lower := (rows 35 74 100 152 21 34 64 128 256), losses := [] }

theorem u20995 : Upper (D 6) (R 6) [34,72,96,144,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20996 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 100 152 21 36 323 387 259), lower := (rows 35 74 100 152 21 36 64 128 256), losses := [] }

theorem u20996 : Upper (D 6) (R 6) [34,72,96,144,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20997 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 100 152 21 288 71 135 263), lower := (rows 35 74 100 152 21 288 64 128 256), losses := [] }

theorem u20997 : Upper (D 6) (R 6) [34,72,96,144,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20997 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20998 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 74 100 152 273 33 70 134 262), lower := (rows 35 74 100 152 273 33 64 128 256), losses := [] }

theorem u20998 : Upper (D 6) (R 6) [34,72,96,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20999 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 152 273 34 69 133 261), lower := (rows 35 74 100 152 273 34 64 128 256), losses := [] }

theorem u20999 : Upper (D 6) (R 6) [34,72,96,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20999
end Delivery.IrregularNine14.P06
