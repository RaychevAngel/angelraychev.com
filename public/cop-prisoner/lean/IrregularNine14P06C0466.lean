import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0152
import IrregularNine14P06C0153

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27960 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 266 81 116 116 244 372), lower := (rows 7 11 164 266 81 32 64 128 256), losses := [] }

theorem u27960 : Upper (D 6) (R 6) [6,9,160,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27961 : Route 9 := (fun mask => (mask,id))

def c27961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27961 : Upper (D 6) (R 6) [6,9,160,258,68] 13 := by
  apply FastRouting.sound _ _ [6,9,160,258,68] 13 (by decide) (choices 1) [1,16,64] r27961 c27961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9137
  · exact u9138
  · exact u9139

def r27962 : Route 9 := (fun mask => (mask,id))

def c27962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27962 : Upper (D 6) (R 6) [6,9,160,258,96] 13 := by
  apply FastRouting.sound _ _ [6,9,160,258,96] 13 (by decide) (choices 1) [1,4,16,64] r27962 c27962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9140
  · exact u9141
  · exact u9142
  · exact u9143

def b27963 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 19 100 100 228 356), lower := (rows 7 11 164 280 19 32 64 128 256), losses := [] }

theorem u27963 : Upper (D 6) (R 6) [6,9,160,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27964 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 164 280 21 98 98 226 354), lower := (rows 7 11 164 280 21 32 64 128 256), losses := [] }

theorem u27964 : Upper (D 6) (R 6) [6,9,160,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27965 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 164 280 22 97 97 225 353), lower := (rows 7 11 164 280 22 32 64 128 256), losses := [] }

theorem u27965 : Upper (D 6) (R 6) [6,9,160,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27966 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 7 11 164 280 49 102 70 198 326), lower := (rows 7 11 164 280 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 164 284 508 32 64 128 256) },{ target := 5, region := (rows 1 18 4 24 16 0 65 129 257), good := (rows 455 459 132 282 475 0 64 128 256) }] }

theorem u27966 : Upper (D 6) (R 6) [6,9,160,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27967 : Route 9 := (fun mask => (mask,id))

def c27967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27967 : Upper (D 6) (R 6) [6,9,160,272,34] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,34] 13 (by decide) (choices 1) [1,4,64] r27967 c27967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9144
  · exact u9145
  · exact u9146

def b27968 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 164 280 52 99 67 195 323), lower := (rows 7 11 164 280 52 32 64 128 256), losses := [] }

theorem u27968 : Upper (D 6) (R 6) [6,9,160,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27969 : Route 9 := (fun mask => (mask,id))

def c27969 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27969 : Upper (D 6) (R 6) [6,9,160,272,65] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,65] 13 (by decide) (choices 1) [2,4,64] r27969 c27969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9147
  · exact u9148
  · exact u9149

def r27970 : Route 9 := (fun mask => (mask,id))

def c27970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27970 : Upper (D 6) (R 6) [6,9,160,272,66] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,66] 13 (by decide) (choices 1) [1,4,64] r27970 c27970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9150
  · exact u9151
  · exact u9152

def r27971 : Route 9 := (fun mask => (mask,id))

def c27971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27971 : Upper (D 6) (R 6) [6,9,160,272,68] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,68] 13 (by decide) (choices 1) [1,2,64] r27971 c27971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9153
  · exact u9154
  · exact u9155

def r27972 : Route 9 := (fun mask => (mask,id))

def c27972 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27972 : Upper (D 6) (R 6) [6,9,160,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,96] 13 (by decide) (choices 1) [1,2,4,64] r27972 c27972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9156
  · exact u9157
  · exact u9158
  · exact u9159

def b27973 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 296 19 116 84 212 340), lower := (rows 7 11 164 296 19 32 64 128 256), losses := [] }

theorem u27973 : Upper (D 6) (R 6) [6,9,160,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27974 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 11 164 296 21 114 82 210 338), lower := (rows 7 11 164 296 21 32 64 128 256), losses := [] }

theorem u27974 : Upper (D 6) (R 6) [6,9,160,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27975 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 11 164 296 22 113 81 209 337), lower := (rows 7 11 164 296 22 32 64 128 256), losses := [] }

theorem u27975 : Upper (D 6) (R 6) [6,9,160,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27976 : Route 9 := (fun mask => (mask,id))

def c27976 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27976 : Upper (D 6) (R 6) [6,9,160,288,65] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,65] 13 (by decide) (choices 1) [2,4,16,64] r27976 c27976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9160
  · exact u9161
  · exact u9162
  · exact u9163

def r27977 : Route 9 := (fun mask => (mask,id))

def c27977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27977 : Upper (D 6) (R 6) [6,9,160,288,66] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,66] 13 (by decide) (choices 1) [1,4,16,64] r27977 c27977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9164
  · exact u9165
  · exact u9166
  · exact u9167

def r27978 : Route 9 := (fun mask => (mask,id))

def c27978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27978 : Upper (D 6) (R 6) [6,9,160,288,68] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,68] 13 (by decide) (choices 1) [1,2,16,64] r27978 c27978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9168
  · exact u9169
  · exact u9170
  · exact u9171

def b27979 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 328 19 116 116 244 372), lower := (rows 7 11 164 328 19 32 64 128 256), losses := [] }

theorem u27979 : Upper (D 6) (R 6) [6,9,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27980 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 164 328 21 114 114 242 370), lower := (rows 7 11 164 328 21 32 64 128 256), losses := [] }

theorem u27980 : Upper (D 6) (R 6) [6,9,160,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27981 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 164 328 22 113 113 241 369), lower := (rows 7 11 164 328 22 32 64 128 256), losses := [] }

theorem u27981 : Upper (D 6) (R 6) [6,9,160,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27982 : Route 9 := (fun mask => (mask,id))

def c27982 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27982 : Upper (D 6) (R 6) [6,9,160,320,33] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,33] 13 (by decide) (choices 1) [2,4,16,64] r27982 c27982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9172
  · exact u9173
  · exact u9174
  · exact u9175

def r27983 : Route 9 := (fun mask => (mask,id))

def c27983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27983 : Upper (D 6) (R 6) [6,9,160,320,34] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,34] 13 (by decide) (choices 1) [1,4,16,64] r27983 c27983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9176
  · exact u9177
  · exact u9178
  · exact u9179

def b27984 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 164 328 52 115 83 211 339), lower := (rows 7 11 164 328 52 32 64 128 256), losses := [] }

theorem u27984 : Upper (D 6) (R 6) [6,9,160,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27985 : Route 9 := (fun mask => (mask,id))

def c27985 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27985 : Upper (D 6) (R 6) [6,9,160,320,65] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,65] 13 (by decide) (choices 1) [2,4,16] r27985 c27985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9180
  · exact u9181
  · exact u9182

def r27986 : Route 9 := (fun mask => (mask,id))

def c27986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27986 : Upper (D 6) (R 6) [6,9,160,320,66] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,66] 13 (by decide) (choices 1) [1,4,16] r27986 c27986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9183
  · exact u9184
  · exact u9185

def r27987 : Route 9 := (fun mask => (mask,id))

def c27987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27987 : Upper (D 6) (R 6) [6,9,160,320,68] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,68] 13 (by decide) (choices 1) [1,2,16] r27987 c27987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9186
  · exact u9187
  · exact u9188

def r27988 : Route 9 := (fun mask => (mask,id))

def c27988 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27988 : Upper (D 6) (R 6) [6,9,160,320,96] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,96] 13 (by decide) (choices 1) [1,2,4,16] r27988 c27988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9189
  · exact u9190
  · exact u9191
  · exact u9192

def b27989 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 27, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 388 26 21 96 96 224 352), lower := (rows 7 11 388 26 21 32 64 128 256), losses := [] }

theorem u27989 : Upper (D 6) (R 6) [6,9,384,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27990 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 388 26 49 100 100 228 356), lower := (rows 7 11 388 26 49 32 64 128 256), losses := [] }

theorem u27990 : Upper (D 6) (R 6) [6,9,384,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27991 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 388 26 52 97 97 225 353), lower := (rows 7 11 388 26 52 32 64 128 256), losses := [] }

theorem u27991 : Upper (D 6) (R 6) [6,9,384,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27992 : Route 9 := (fun mask => (mask,id))

def c27992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27992 : Upper (D 6) (R 6) [6,9,384,18,96] 13 := by
  apply FastRouting.sound _ _ [6,9,384,18,96] 13 (by decide) (choices 1) [1,4,64] r27992 c27992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9193
  · exact u9194
  · exact u9195

def b27993 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 388 42 21 112 112 240 368), lower := (rows 7 11 388 42 21 32 64 128 256), losses := [] }

theorem u27993 : Upper (D 6) (R 6) [6,9,384,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27994 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 10, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 388 42 49 116 84 212 340), lower := (rows 7 11 388 42 49 32 64 128 256), losses := [] }

theorem u27994 : Upper (D 6) (R 6) [6,9,384,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27995 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 388 42 52 113 81 209 337), lower := (rows 7 11 388 42 52 32 64 128 256), losses := [] }

theorem u27995 : Upper (D 6) (R 6) [6,9,384,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27996 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 388 42 81 116 116 244 372), lower := (rows 7 11 388 42 81 32 64 128 256), losses := [] }

theorem u27996 : Upper (D 6) (R 6) [6,9,384,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27997 : Route 9 := (fun mask => (mask,id))

def c27997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27997 : Upper (D 6) (R 6) [6,9,384,34,68] 13 := by
  apply FastRouting.sound _ _ [6,9,384,34,68] 13 (by decide) (choices 1) [1,16,64] r27997 c27997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9196
  · exact u9197
  · exact u9198

def r27998 : Route 9 := (fun mask => (mask,id))

def c27998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27998 : Upper (D 6) (R 6) [6,9,384,34,96] 13 := by
  apply FastRouting.sound _ _ [6,9,384,34,96] 13 (by decide) (choices 1) [1,4,16,64] r27998 c27998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9199
  · exact u9200
  · exact u9201
  · exact u9202

def b27999 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 388 56 19 100 100 228 356), lower := (rows 7 11 388 56 19 32 64 128 256), losses := [] }

theorem u27999 : Upper (D 6) (R 6) [6,9,384,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28000 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 388 56 21 98 98 226 354), lower := (rows 7 11 388 56 21 32 64 128 256), losses := [] }

theorem u28000 : Upper (D 6) (R 6) [6,9,384,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28001 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 388 56 22 97 97 225 353), lower := (rows 7 11 388 56 22 32 64 128 256), losses := [] }

theorem u28001 : Upper (D 6) (R 6) [6,9,384,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28002 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 10, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 388 56 49 102 70 198 326), lower := (rows 7 11 388 56 49 32 64 128 256), losses := [] }

theorem u28002 : Upper (D 6) (R 6) [6,9,384,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28003 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 388 56 50 101 69 197 325), lower := (rows 7 11 388 56 50 32 64 128 256), losses := [] }

theorem u28003 : Upper (D 6) (R 6) [6,9,384,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28004 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 388 56 52 99 67 195 323), lower := (rows 7 11 388 56 52 32 64 128 256), losses := [] }

theorem u28004 : Upper (D 6) (R 6) [6,9,384,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28005 : Route 9 := (fun mask => (mask,id))

def c28005 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28005 : Upper (D 6) (R 6) [6,9,384,48,65] 13 := by
  apply FastRouting.sound _ _ [6,9,384,48,65] 13 (by decide) (choices 1) [2,4,64] r28005 c28005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9203
  · exact u9204
  · exact u9205

def r28006 : Route 9 := (fun mask => (mask,id))

def c28006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28006 : Upper (D 6) (R 6) [6,9,384,48,66] 13 := by
  apply FastRouting.sound _ _ [6,9,384,48,66] 13 (by decide) (choices 1) [1,4,64] r28006 c28006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9206
  · exact u9207
  · exact u9208

def r28007 : Route 9 := (fun mask => (mask,id))

def c28007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28007 : Upper (D 6) (R 6) [6,9,384,48,68] 13 := by
  apply FastRouting.sound _ _ [6,9,384,48,68] 13 (by decide) (choices 1) [1,2,64] r28007 c28007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9209
  · exact u9210
  · exact u9211

def b28008 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 388 56 112 103 71 199 327), lower := (rows 7 11 388 56 112 32 64 128 256), losses := [] }

theorem u28008 : Upper (D 6) (R 6) [6,9,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28009 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 388 104 19 116 116 244 372), lower := (rows 7 11 388 104 19 32 64 128 256), losses := [] }

theorem u28009 : Upper (D 6) (R 6) [6,9,384,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28010 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 388 104 21 114 114 242 370), lower := (rows 7 11 388 104 21 32 64 128 256), losses := [] }

theorem u28010 : Upper (D 6) (R 6) [6,9,384,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28011 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 388 104 22 113 113 241 369), lower := (rows 7 11 388 104 22 32 64 128 256), losses := [] }

theorem u28011 : Upper (D 6) (R 6) [6,9,384,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28012 : Route 9 := (fun mask => (mask,id))

def c28012 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28012 : Upper (D 6) (R 6) [6,9,384,96,33] 13 := by
  apply FastRouting.sound _ _ [6,9,384,96,33] 13 (by decide) (choices 1) [2,4,16,64] r28012 c28012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9212
  · exact u9213
  · exact u9214
  · exact u9215

def r28013 : Route 9 := (fun mask => (mask,id))

def c28013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28013 : Upper (D 6) (R 6) [6,9,384,96,34] 13 := by
  apply FastRouting.sound _ _ [6,9,384,96,34] 13 (by decide) (choices 1) [1,4,16,64] r28013 c28013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9216
  · exact u9217
  · exact u9218
  · exact u9219

def r28014 : Route 9 := (fun mask => (mask,id))

def c28014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28014 : Upper (D 6) (R 6) [6,9,384,96,36] 13 := by
  apply FastRouting.sound _ _ [6,9,384,96,36] 13 (by decide) (choices 1) [1,2,16,64] r28014 c28014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9220
  · exact u9221
  · exact u9222
  · exact u9223

def b28015 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 388 104 112 55 87 151 279), lower := (rows 7 11 388 104 112 32 64 128 256), losses := [] }

theorem u28015 : Upper (D 6) (R 6) [6,9,384,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28016 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 37 11 84 480 480 480 480), lower := (rows 7 26 37 11 84 32 64 128 256), losses := [] }

theorem u28016 : Upper (D 6) (R 6) [6,24,33,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28017 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 37 11 112 484 452 452 452), lower := (rows 7 26 37 11 112 32 64 128 256), losses := [] }

theorem u28017 : Upper (D 6) (R 6) [6,24,33,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28018 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 37 11 148 352 352 480 352), lower := (rows 7 26 37 11 148 32 64 128 256), losses := [] }

theorem u28018 : Upper (D 6) (R 6) [6,24,33,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28019 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 37 11 176 356 324 452 324), lower := (rows 7 26 37 11 176 32 64 128 256), losses := [] }

theorem u28019 : Upper (D 6) (R 6) [6,24,33,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28019
end Delivery.IrregularNine14.P06
