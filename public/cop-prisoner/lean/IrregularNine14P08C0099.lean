import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0012

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5940 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 152 49 33 224 224 480), lower := (rows 259 38 76 152 49 33 64 128 256), losses := [] }

theorem u5940 : Upper (D 8) (R 8) [258,36,72,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5941 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 152 49 96 225 161 417), lower := (rows 259 38 76 152 49 96 64 128 256), losses := [] }

theorem u5941 : Upper (D 8) (R 8) [258,36,72,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5942 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 152 49 160 97 225 353), lower := (rows 259 38 76 152 49 160 64 128 256), losses := [] }

theorem u5942 : Upper (D 8) (R 8) [258,36,72,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5943 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 168 49 33 208 208 464), lower := (rows 259 38 76 168 49 33 64 128 256), losses := [] }

theorem u5943 : Upper (D 8) (R 8) [258,36,72,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5944 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 38 76 168 49 48 193 193 449), lower := (rows 259 38 76 168 49 48 64 128 256), losses := [] }

theorem u5944 : Upper (D 8) (R 8) [258,36,72,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5944 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5945 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 168 49 96 209 145 401), lower := (rows 259 38 76 168 49 96 64 128 256), losses := [] }

theorem u5945 : Upper (D 8) (R 8) [258,36,72,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5946 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 168 49 160 81 209 337), lower := (rows 259 38 76 168 49 160 64 128 256), losses := [] }

theorem u5946 : Upper (D 8) (R 8) [258,36,72,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5947 : Route 9 := (fun mask => (mask,id))

def c5947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5947 : Upper (D 8) (R 8) [258,36,72,160,96,1] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160,96,1] 13 (by decide) (choices 1) [1,16,128] r5947 c5947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u727
  · exact u728
  · exact u729

def b5948 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 76 168 112 48 193 129 385), lower := (rows 259 38 76 168 112 48 64 128 256), losses := [] }

theorem u5948 : Upper (D 8) (R 8) [258,36,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5948 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5949 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 168 112 160 81 145 273), lower := (rows 259 38 76 168 112 160 64 128 256), losses := [] }

theorem u5949 : Upper (D 8) (R 8) [258,36,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5950 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 76 168 145 33 112 240 368), lower := (rows 259 38 76 168 145 33 64 128 256), losses := [] }

theorem u5950 : Upper (D 8) (R 8) [258,36,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5951 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 259 38 76 168 145 48 97 225 353), lower := (rows 259 38 76 168 145 48 64 128 256), losses := [] }

theorem u5951 : Upper (D 8) (R 8) [258,36,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5951 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5952 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 168 145 96 113 177 305), lower := (rows 259 38 76 168 145 96 64 128 256), losses := [] }

theorem u5952 : Upper (D 8) (R 8) [258,36,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5953 : Route 9 := (fun mask => (mask,id))

def c5953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5953 : Upper (D 8) (R 8) [258,36,72,160,192,1] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160,192,1] 13 (by decide) (choices 1) [1,16,32] r5953 c5953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u730
  · exact u731
  · exact u732

def b5954 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 76 168 208 48 97 161 289), lower := (rows 259 38 76 168 208 48 64 128 256), losses := [] }

theorem u5954 : Upper (D 8) (R 8) [258,36,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5954 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5955 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 196 25 56 33 224 224 480), lower := (rows 259 38 196 25 56 33 64 128 256), losses := [] }

theorem u5955 : Upper (D 8) (R 8) [258,36,192,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5956 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 196 25 56 96 225 161 417), lower := (rows 259 38 196 25 56 96 64 128 256), losses := [] }

theorem u5956 : Upper (D 8) (R 8) [258,36,192,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5957 : Route 9 := (fun mask => (mask,id))

def c5957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5957 : Upper (D 8) (R 8) [258,36,192,17,96,1] 13 := by
  apply FastRouting.sound _ _ [258,36,192,17,96,1] 13 (by decide) (choices 1) [8,32,128] r5957 c5957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u733
  · exact u734
  · exact u735

def b5958 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 196 25 112 40 225 161 417), lower := (rows 259 38 196 25 112 40 64 128 256), losses := [] }

theorem u5958 : Upper (D 8) (R 8) [258,36,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5958 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5959 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 196 25 112 160 105 169 297), lower := (rows 259 38 196 25 112 160 64 128 256), losses := [] }

theorem u5959 : Upper (D 8) (R 8) [258,36,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5960 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 196 41 88 33 240 176 432), lower := (rows 259 38 196 41 88 33 64 128 256), losses := [] }

theorem u5960 : Upper (D 8) (R 8) [258,36,192,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5961 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 196 41 88 48 225 161 417), lower := (rows 259 38 196 41 88 48 64 128 256), losses := [] }

theorem u5961 : Upper (D 8) (R 8) [258,36,192,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5961 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5962 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 196 41 88 160 113 177 305), lower := (rows 259 38 196 41 88 160 64 128 256), losses := [] }

theorem u5962 : Upper (D 8) (R 8) [258,36,192,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5963 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 196 41 112 33 216 152 408), lower := (rows 259 38 196 41 112 33 64 128 256), losses := [] }

theorem u5963 : Upper (D 8) (R 8) [258,36,192,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5964 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 38 196 41 112 40 209 145 401), lower := (rows 259 38 196 41 112 40 64 128 256), losses := [] }

theorem u5964 : Upper (D 8) (R 8) [258,36,192,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5964 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5965 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 38 196 41 112 48 201 137 393), lower := (rows 259 38 196 41 112 48 64 128 256), losses := [] }

theorem u5965 : Upper (D 8) (R 8) [258,36,192,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5965 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5966 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 196 41 112 160 89 153 281), lower := (rows 259 38 196 41 112 160 64 128 256), losses := [] }

theorem u5966 : Upper (D 8) (R 8) [258,36,192,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5967 : Route 9 := (fun mask => (mask,id))

def c5967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5967 : Upper (D 8) (R 8) [258,36,192,80,160,1] 13 := by
  apply FastRouting.sound _ _ [258,36,192,80,160,1] 13 (by decide) (choices 1) [1,8,32] r5967 c5967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u736
  · exact u737
  · exact u738

def b5968 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 196 88 176 40 97 161 289), lower := (rows 259 38 196 88 176 40 64 128 256), losses := [] }

theorem u5968 : Upper (D 8) (R 8) [258,36,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5968 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5969 : Route 9 := (fun mask => (mask,id))

def c5969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5969 : Upper (D 8) (R 8) [258,36,192,96,160,1] 13 := by
  apply FastRouting.sound _ _ [258,36,192,96,160,1] 13 (by decide) (choices 1) [1,8,16] r5969 c5969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u739
  · exact u740
  · exact u741

def b5970 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 38 196 104 176 40 81 145 273), lower := (rows 259 38 196 104 176 40 64 128 256), losses := [] }

theorem u5970 : Upper (D 8) (R 8) [258,36,192,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5970 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5971 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 104 176 33 228 164 420), lower := (rows 259 67 28 104 176 33 64 128 256), losses := [] }

theorem u5971 : Upper (D 8) (R 8) [258,65,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5972 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 67 28 104 176 36 225 161 417), lower := (rows 259 67 28 104 176 36 64 128 256), losses := [] }

theorem u5972 : Upper (D 8) (R 8) [258,65,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5972 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5973 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 28 104 176 160 101 165 293), lower := (rows 259 67 28 104 176 160 64 128 256), losses := [] }

theorem u5973 : Upper (D 8) (R 8) [258,65,24,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5974 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 88 176 33 228 164 420), lower := (rows 259 67 44 88 176 33 64 128 256), losses := [] }

theorem u5974 : Upper (D 8) (R 8) [258,65,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5975 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 67 44 88 176 36 225 161 417), lower := (rows 259 67 44 88 176 36 64 128 256), losses := [] }

theorem u5975 : Upper (D 8) (R 8) [258,65,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5975 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5976 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 88 176 160 101 165 293), lower := (rows 259 67 44 88 176 160 64 128 256), losses := [] }

theorem u5976 : Upper (D 8) (R 8) [258,65,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5977 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 140 112 33 240 176 432), lower := (rows 259 67 44 140 112 33 64 128 256), losses := [] }

theorem u5977 : Upper (D 8) (R 8) [258,65,40,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5978 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 67 44 140 112 48 225 161 417), lower := (rows 259 67 44 140 112 48 64 128 256), losses := [] }

theorem u5978 : Upper (D 8) (R 8) [258,65,40,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5978 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5979 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 140 112 160 113 177 305), lower := (rows 259 67 44 140 112 160 64 128 256), losses := [] }

theorem u5979 : Upper (D 8) (R 8) [258,65,40,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5980 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 152 112 33 228 164 420), lower := (rows 259 67 44 152 112 33 64 128 256), losses := [] }

theorem u5980 : Upper (D 8) (R 8) [258,65,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5981 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 67 44 152 112 36 225 161 417), lower := (rows 259 67 44 152 112 36 64 128 256), losses := [] }

theorem u5981 : Upper (D 8) (R 8) [258,65,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5981 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5982 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 152 112 160 101 165 293), lower := (rows 259 67 44 152 112 160 64 128 256), losses := [] }

theorem u5982 : Upper (D 8) (R 8) [258,65,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5983 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 200 176 33 116 180 308), lower := (rows 259 67 44 200 176 33 64 128 256), losses := [] }

theorem u5983 : Upper (D 8) (R 8) [258,65,40,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5984 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 67 44 200 176 36 113 177 305), lower := (rows 259 67 44 200 176 36 64 128 256), losses := [] }

theorem u5984 : Upper (D 8) (R 8) [258,65,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5984 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5985 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 67 44 200 176 48 101 165 293), lower := (rows 259 67 44 200 176 48 64 128 256), losses := [] }

theorem u5985 : Upper (D 8) (R 8) [258,65,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5985 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5986 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 100 140 176 33 120 184 312), lower := (rows 259 67 100 140 176 33 64 128 256), losses := [] }

theorem u5986 : Upper (D 8) (R 8) [258,65,96,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5987 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 67 100 140 176 40 113 177 305), lower := (rows 259 67 100 140 176 40 64 128 256), losses := [] }

theorem u5987 : Upper (D 8) (R 8) [258,65,96,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5987 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5988 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 67 100 140 176 48 105 169 297), lower := (rows 259 67 100 140 176 48 64 128 256), losses := [] }

theorem u5988 : Upper (D 8) (R 8) [258,65,96,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5988 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5989 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 13 168 112 33 240 176 432), lower := (rows 259 70 13 168 112 33 64 128 256), losses := [] }

theorem u5989 : Upper (D 8) (R 8) [258,68,9,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5990 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 13 168 112 48 225 161 417), lower := (rows 259 70 13 168 112 48 64 128 256), losses := [] }

theorem u5990 : Upper (D 8) (R 8) [258,68,9,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5990 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5991 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 13 168 112 160 113 177 305), lower := (rows 259 70 13 168 112 160 64 128 256), losses := [] }

theorem u5991 : Upper (D 8) (R 8) [258,68,9,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5992 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 13 168 208 33 112 176 304), lower := (rows 259 70 13 168 208 33 64 128 256), losses := [] }

theorem u5992 : Upper (D 8) (R 8) [258,68,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5993 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 13 168 208 48 97 161 289), lower := (rows 259 70 13 168 208 48 64 128 256), losses := [] }

theorem u5993 : Upper (D 8) (R 8) [258,68,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5993 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5994 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 28 41 176 33 224 224 480), lower := (rows 259 70 28 41 176 33 64 128 256), losses := [] }

theorem u5994 : Upper (D 8) (R 8) [258,68,24,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5995 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 148, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 28 41 176 96 225 161 417), lower := (rows 259 70 28 41 176 96 64 128 256), losses := [] }

theorem u5995 : Upper (D 8) (R 8) [258,68,24,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5996 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 28 41 176 160 97 225 353), lower := (rows 259 70 28 41 176 160 64 128 256), losses := [] }

theorem u5996 : Upper (D 8) (R 8) [258,68,24,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5997 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 56 152 33 224 224 480), lower := (rows 259 70 37 56 152 33 64 128 256), losses := [] }

theorem u5997 : Upper (D 8) (R 8) [258,68,33,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5998 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 56 152 96 225 161 417), lower := (rows 259 70 37 56 152 96 64 128 256), losses := [] }

theorem u5998 : Upper (D 8) (R 8) [258,68,33,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5999 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 56 152 160 97 225 353), lower := (rows 259 70 37 56 152 160 64 128 256), losses := [] }

theorem u5999 : Upper (D 8) (R 8) [258,68,33,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5999
end Delivery.IrregularNine14.P08
