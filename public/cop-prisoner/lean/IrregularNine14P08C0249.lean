import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0087
import IrregularNine14P08C0088

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14940 : Route 9 := (fun mask => (mask,id))

def c14940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14940 : Upper (D 8) (R 8) [96,68,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,68,129,144,257] 13 (by decide) (choices 1) [2,8] r14940 c14940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5256
  · exact u5257

def b14941 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 152 274 41 105 169 297), lower := (rows 97 70 133 152 274 32 64 128 256), losses := [] }

theorem u14941 : Upper (D 8) (R 8) [96,68,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14942 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 152 280 35 99 163 291), lower := (rows 97 70 133 152 280 32 64 128 256), losses := [] }

theorem u14942 : Upper (D 8) (R 8) [96,68,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14943 : Route 9 := (fun mask => (mask,id))

def c14943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14943 : Upper (D 8) (R 8) [96,68,129,144,288] 13 := by
  apply FastRouting.sound _ _ [96,68,129,144,288] 13 (by decide) (choices 1) [1,2,8] r14943 c14943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5258
  · exact u5259
  · exact u5260

def r14944 : Route 9 := (fun mask => (mask,id))

def c14944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14944 : Upper (D 8) (R 8) [96,68,129,160,257] 13 := by
  apply FastRouting.sound _ _ [96,68,129,160,257] 13 (by decide) (choices 1) [2,8,16] r14944 c14944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5261
  · exact u5262
  · exact u5263

def r14945 : Route 9 := (fun mask => (mask,id))

def c14945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14945 : Upper (D 8) (R 8) [96,68,129,160,258] 13 := by
  apply FastRouting.sound _ _ [96,68,129,160,258] 13 (by decide) (choices 1) [1,8,16] r14945 c14945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5264
  · exact u5265
  · exact u5266

def r14946 : Route 9 := (fun mask => (mask,id))

def c14946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14946 : Upper (D 8) (R 8) [96,68,129,160,264] 13 := by
  apply FastRouting.sound _ _ [96,68,129,160,264] 13 (by decide) (choices 1) [1,2,16] r14946 c14946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5267
  · exact u5268
  · exact u5269

def r14947 : Route 9 := (fun mask => (mask,id))

def c14947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14947 : Upper (D 8) (R 8) [96,68,129,160,288] 13 := by
  apply FastRouting.sound _ _ [96,68,129,160,288] 13 (by decide) (choices 1) [1,2,8,16] r14947 c14947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5270
  · exact u5271
  · exact u5272
  · exact u5273

def b14948 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 137 273 56 120 184 312), lower := (rows 97 70 134 137 273 32 64 128 256), losses := [] }

theorem u14948 : Upper (D 8) (R 8) [96,68,130,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14949 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 137 280 49 113 177 305), lower := (rows 97 70 134 137 280 32 64 128 256), losses := [] }

theorem u14949 : Upper (D 8) (R 8) [96,68,130,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14950 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 137 304 57 121 185 313), lower := (rows 97 70 134 137 304 32 64 128 256), losses := [] }

theorem u14950 : Upper (D 8) (R 8) [96,68,130,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14951 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 152 273 41 105 169 297), lower := (rows 97 70 134 152 273 32 64 128 256), losses := [] }

theorem u14951 : Upper (D 8) (R 8) [96,68,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14952 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 152 280 33 97 161 289), lower := (rows 97 70 134 152 280 32 64 128 256), losses := [] }

theorem u14952 : Upper (D 8) (R 8) [96,68,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14953 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 152 304 41 105 169 297), lower := (rows 97 70 134 152 304 32 64 128 256), losses := [] }

theorem u14953 : Upper (D 8) (R 8) [96,68,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14954 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 168 273 57 121 185 313), lower := (rows 97 70 134 168 273 32 64 128 256), losses := [] }

theorem u14954 : Upper (D 8) (R 8) [96,68,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14955 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 168 280 49 113 177 305), lower := (rows 97 70 134 168 280 32 64 128 256), losses := [] }

theorem u14955 : Upper (D 8) (R 8) [96,68,130,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14956 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 134 168 304 57 89 153 281), lower := (rows 97 70 134 168 304 32 64 128 256), losses := [] }

theorem u14956 : Upper (D 8) (R 8) [96,68,130,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14957 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 137 273 50 114 178 306), lower := (rows 97 70 140 137 273 32 64 128 256), losses := [] }

theorem u14957 : Upper (D 8) (R 8) [96,68,136,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14958 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 137 274 49 113 177 305), lower := (rows 97 70 140 137 274 32 64 128 256), losses := [] }

theorem u14958 : Upper (D 8) (R 8) [96,68,136,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14959 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 137 304 51 115 179 307), lower := (rows 97 70 140 137 304 32 64 128 256), losses := [] }

theorem u14959 : Upper (D 8) (R 8) [96,68,136,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14960 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 138 273 49 113 177 305), lower := (rows 97 70 140 138 273 32 64 128 256), losses := [] }

theorem u14960 : Upper (D 8) (R 8) [96,68,136,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14961 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 138 304 49 113 177 305), lower := (rows 97 70 140 138 304 32 64 128 256), losses := [] }

theorem u14961 : Upper (D 8) (R 8) [96,68,136,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14962 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 152 273 35 99 163 291), lower := (rows 97 70 140 152 273 32 64 128 256), losses := [] }

theorem u14962 : Upper (D 8) (R 8) [96,68,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14963 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 152 274 33 97 161 289), lower := (rows 97 70 140 152 274 32 64 128 256), losses := [] }

theorem u14963 : Upper (D 8) (R 8) [96,68,136,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14964 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 152 304 35 99 163 291), lower := (rows 97 70 140 152 304 32 64 128 256), losses := [] }

theorem u14964 : Upper (D 8) (R 8) [96,68,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14965 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 168 273 51 115 179 307), lower := (rows 97 70 140 168 273 32 64 128 256), losses := [] }

theorem u14965 : Upper (D 8) (R 8) [96,68,136,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14966 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 168 274 49 113 177 305), lower := (rows 97 70 140 168 274 32 64 128 256), losses := [] }

theorem u14966 : Upper (D 8) (R 8) [96,68,136,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14967 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 168 304 51 83 147 275), lower := (rows 97 70 140 168 304 32 64 128 256), losses := [] }

theorem u14967 : Upper (D 8) (R 8) [96,68,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14968 : Route 9 := (fun mask => (mask,id))

def c14968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14968 : Upper (D 8) (R 8) [96,68,136,257,129] 13 := by
  apply FastRouting.sound _ _ [96,68,136,257,129] 13 (by decide) (choices 1) [2,16] r14968 c14968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5274
  · exact u5275

def b14969 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 265 146 49 113 177 305), lower := (rows 97 70 140 265 146 32 64 128 256), losses := [] }

theorem u14969 : Upper (D 8) (R 8) [96,68,136,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14970 : Route 9 := (fun mask => (mask,id))

def c14970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14970 : Upper (D 8) (R 8) [96,68,136,257,160] 13 := by
  apply FastRouting.sound _ _ [96,68,136,257,160] 13 (by decide) (choices 1) [1,2,16] r14970 c14970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5276
  · exact u5277
  · exact u5278

def b14971 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 70 140 266 145 49 113 177 305), lower := (rows 97 70 140 266 145 32 64 128 256), losses := [] }

theorem u14971 : Upper (D 8) (R 8) [96,68,136,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14972 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 70 140 266 176 49 113 177 305), lower := (rows 97 70 140 266 176 32 64 128 256), losses := [] }

theorem u14972 : Upper (D 8) (R 8) [96,68,136,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14973 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 280 145 35 99 163 291), lower := (rows 97 70 140 280 145 32 64 128 256), losses := [] }

theorem u14973 : Upper (D 8) (R 8) [96,68,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14974 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 280 146 33 97 161 289), lower := (rows 97 70 140 280 146 32 64 128 256), losses := [] }

theorem u14974 : Upper (D 8) (R 8) [96,68,136,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14975 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 280 176 35 99 163 291), lower := (rows 97 70 140 280 176 32 64 128 256), losses := [] }

theorem u14975 : Upper (D 8) (R 8) [96,68,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14976 : Route 9 := (fun mask => (mask,id))

def c14976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14976 : Upper (D 8) (R 8) [96,68,136,288,129] 13 := by
  apply FastRouting.sound _ _ [96,68,136,288,129] 13 (by decide) (choices 1) [1,2,16] r14976 c14976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5279
  · exact u5280
  · exact u5281

def b14977 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 296 146 49 113 177 305), lower := (rows 97 70 140 296 146 32 64 128 256), losses := [] }

theorem u14977 : Upper (D 8) (R 8) [96,68,136,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14978 : Route 9 := (fun mask => (mask,id))

def c14978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14978 : Upper (D 8) (R 8) [96,68,136,288,160] 13 := by
  apply FastRouting.sound _ _ [96,68,136,288,160] 13 (by decide) (choices 1) [1,2,16] r14978 c14978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5282
  · exact u5283
  · exact u5284

def r14979 : Route 9 := (fun mask => (mask,id))

def c14979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14979 : Upper (D 8) (R 8) [96,68,160,129,257] 13 := by
  apply FastRouting.sound _ _ [96,68,160,129,257] 13 (by decide) (choices 1) [2,8,16] r14979 c14979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5285
  · exact u5286
  · exact u5287

def r14980 : Route 9 := (fun mask => (mask,id))

def c14980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14980 : Upper (D 8) (R 8) [96,68,160,129,258] 13 := by
  apply FastRouting.sound _ _ [96,68,160,129,258] 13 (by decide) (choices 1) [1,8,16] r14980 c14980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5288
  · exact u5289
  · exact u5290

def r14981 : Route 9 := (fun mask => (mask,id))

def c14981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14981 : Upper (D 8) (R 8) [96,68,160,129,264] 13 := by
  apply FastRouting.sound _ _ [96,68,160,129,264] 13 (by decide) (choices 1) [1,2,16] r14981 c14981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5291
  · exact u5292
  · exact u5293

def r14982 : Route 9 := (fun mask => (mask,id))

def c14982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14982 : Upper (D 8) (R 8) [96,68,160,129,288] 13 := by
  apply FastRouting.sound _ _ [96,68,160,129,288] 13 (by decide) (choices 1) [1,2,8,16] r14982 c14982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5294
  · exact u5295
  · exact u5296
  · exact u5297

def b14983 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 138 273 57 121 185 313), lower := (rows 97 70 164 138 273 32 64 128 256), losses := [] }

theorem u14983 : Upper (D 8) (R 8) [96,68,160,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14984 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 138 280 49 113 177 305), lower := (rows 97 70 164 138 280 32 64 128 256), losses := [] }

theorem u14984 : Upper (D 8) (R 8) [96,68,160,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14985 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 138 304 57 89 153 281), lower := (rows 97 70 164 138 304 32 64 128 256), losses := [] }

theorem u14985 : Upper (D 8) (R 8) [96,68,160,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14986 : Route 9 := (fun mask => (mask,id))

def c14986 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14986 : Upper (D 8) (R 8) [96,68,160,144,257] 13 := by
  apply FastRouting.sound _ _ [96,68,160,144,257] 13 (by decide) (choices 1) [1,2,8] r14986 c14986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5298
  · exact u5299
  · exact u5300

def b14987 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 152 274 41 105 169 297), lower := (rows 97 70 164 152 274 32 64 128 256), losses := [] }

theorem u14987 : Upper (D 8) (R 8) [96,68,160,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14988 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 152 280 35 99 163 291), lower := (rows 97 70 164 152 280 32 64 128 256), losses := [] }

theorem u14988 : Upper (D 8) (R 8) [96,68,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14989 : Route 9 := (fun mask => (mask,id))

def c14989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14989 : Upper (D 8) (R 8) [96,68,160,144,288] 13 := by
  apply FastRouting.sound _ _ [96,68,160,144,288] 13 (by decide) (choices 1) [1,2,8] r14989 c14989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5301
  · exact u5302
  · exact u5303

def b14990 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 70 164 168 273 59 91 155 283), lower := (rows 97 70 164 168 273 32 64 128 256), losses := [] }

theorem u14990 : Upper (D 8) (R 8) [96,68,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14991 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 70 164 168 274 57 89 153 281), lower := (rows 97 70 164 168 274 32 64 128 256), losses := [] }

theorem u14991 : Upper (D 8) (R 8) [96,68,160,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14992 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 70 164 168 280 51 83 147 275), lower := (rows 97 70 164 168 280 32 64 128 256), losses := [] }

theorem u14992 : Upper (D 8) (R 8) [96,68,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14993 : Route 9 := (fun mask => (mask,id))

def c14993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14993 : Upper (D 8) (R 8) [96,68,257,129,130] 13 := by
  apply FastRouting.sound _ _ [96,68,257,129,130] 13 (by decide) (choices 1) [8,16] r14993 c14993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5304
  · exact u5305

def b14994 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 70 261 137 152 50 114 178 306), lower := (rows 97 70 261 137 152 32 64 128 256), losses := [] }

theorem u14994 : Upper (D 8) (R 8) [96,68,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14995 : Route 9 := (fun mask => (mask,id))

def c14995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14995 : Upper (D 8) (R 8) [96,68,257,129,160] 13 := by
  apply FastRouting.sound _ _ [96,68,257,129,160] 13 (by decide) (choices 1) [2,8,16] r14995 c14995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5306
  · exact u5307
  · exact u5308

def b14996 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 70 261 138 152 49 113 177 305), lower := (rows 97 70 261 138 152 32 64 128 256), losses := [] }

theorem u14996 : Upper (D 8) (R 8) [96,68,257,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14997 : Route 9 := (fun mask => (mask,id))

def c14997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14997 : Upper (D 8) (R 8) [96,68,257,130,160] 13 := by
  apply FastRouting.sound _ _ [96,68,257,130,160] 13 (by decide) (choices 1) [1,8,16] r14997 c14997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5309
  · exact u5310
  · exact u5311

def b14998 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 70 261 152 152 35 99 163 291), lower := (rows 97 70 261 152 152 32 64 128 256), losses := [] }

theorem u14998 : Upper (D 8) (R 8) [96,68,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14999 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 261 152 176 43 107 171 299), lower := (rows 97 70 261 152 176 32 64 128 256), losses := [] }

theorem u14999 : Upper (D 8) (R 8) [96,68,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14999
end Delivery.IrregularNine14.P08
