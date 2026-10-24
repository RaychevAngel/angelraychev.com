import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0172
import IrregularNine14P07C0173

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r27960 : Route 9 := (fun mask => (mask,id))

def c27960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27960 : Upper (D 7) (R 7) [36,320,192,18,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,129,2] 13 (by decide) (choices 1) [1,8,32] r27960 c27960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10364
  · exact u10365
  · exact u10366

def r27961 : Route 9 := (fun mask => (mask,id))

def c27961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27961 : Upper (D 7) (R 7) [36,320,192,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,129,8] 13 (by decide) (choices 1) [1,2,32] r27961 c27961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10367
  · exact u10368
  · exact u10369

def b27962 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 196 26 152 33 99 163 291), lower := (rows 37 322 196 26 152 33 64 128 256), losses := [] }

theorem u27962 : Upper (D 7) (R 7) [36,320,192,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27963 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 37 322 196 26 152 34 97 161 289), lower := (rows 37 322 196 26 152 34 64 128 256), losses := [] }

theorem u27963 : Upper (D 7) (R 7) [36,320,192,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27964 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 196 26 176 33 75 139 267), lower := (rows 37 322 196 26 176 33 64 128 256), losses := [] }

theorem u27964 : Upper (D 7) (R 7) [36,320,192,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27965 : Route 9 := (fun mask => (mask,id))

def c27965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27965 : Upper (D 7) (R 7) [36,320,192,18,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,160,2] 13 (by decide) (choices 1) [1,8] r27965 c27965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10370
  · exact u10371

def b27966 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 322 196 26 176 40 67 131 259), lower := (rows 37 322 196 26 176 40 64 128 256), losses := [] }

theorem u27966 : Upper (D 7) (R 7) [36,320,192,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27966 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27967 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 196 42 145 33 90 154 282), lower := (rows 37 322 196 42 145 33 64 128 256), losses := [] }

theorem u27967 : Upper (D 7) (R 7) [36,320,192,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27968 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 196 42 145 34 89 153 281), lower := (rows 37 322 196 42 145 34 64 128 256), losses := [] }

theorem u27968 : Upper (D 7) (R 7) [36,320,192,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27969 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 196 42 145 40 83 147 275), lower := (rows 37 322 196 42 145 40 64 128 256), losses := [] }

theorem u27969 : Upper (D 7) (R 7) [36,320,192,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27969 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27970 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 196 42 145 48 75 139 267), lower := (rows 37 322 196 42 145 48 64 128 256), losses := [] }

theorem u27970 : Upper (D 7) (R 7) [36,320,192,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27970 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27971 : Route 9 := (fun mask => (mask,id))

def c27971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27971 : Upper (D 7) (R 7) [36,320,192,34,130,1] 13 := by
  apply FastRouting.sound _ _ [36,320,192,34,130,1] 13 (by decide) (choices 1) [1,8,16] r27971 c27971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10372
  · exact u10373
  · exact u10374

def b27972 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 196 42 146 40 81 145 273), lower := (rows 37 322 196 42 146 40 64 128 256), losses := [] }

theorem u27972 : Upper (D 7) (R 7) [36,320,192,34,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27972 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27973 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 322 196 42 146 48 73 137 265), lower := (rows 37 322 196 42 146 48 64 128 256), losses := [] }

theorem u27973 : Upper (D 7) (R 7) [36,320,192,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27973 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27974 : Route 9 := (fun mask => (mask,id))

def c27974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27974 : Upper (D 7) (R 7) [36,320,192,34,136,1] 13 := by
  apply FastRouting.sound _ _ [36,320,192,34,136,1] 13 (by decide) (choices 1) [1,2,16] r27974 c27974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10375
  · exact u10376
  · exact u10377

def b27975 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 196 42 152 34 81 145 273), lower := (rows 37 322 196 42 152 34 64 128 256), losses := [] }

theorem u27975 : Upper (D 7) (R 7) [36,320,192,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27976 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 322 196 42 152 48 67 131 259), lower := (rows 37 322 196 42 152 48 64 128 256), losses := [] }

theorem u27976 : Upper (D 7) (R 7) [36,320,192,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27976 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27977 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 322 196 56 145 33 74 138 266), lower := (rows 37 322 196 56 145 33 64 128 256), losses := [] }

theorem u27977 : Upper (D 7) (R 7) [36,320,192,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27978 : Route 9 := (fun mask => (mask,id))

def c27978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27978 : Upper (D 7) (R 7) [36,320,192,48,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,48,129,2] 13 (by decide) (choices 1) [1,2,8] r27978 c27978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10378
  · exact u10379
  · exact u10380

def b27979 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 322 196 56 145 40 67 131 259), lower := (rows 37 322 196 56 145 40 64 128 256), losses := [] }

theorem u27979 : Upper (D 7) (R 7) [36,320,192,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27979 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27980 : Route 9 := (fun mask => (mask,id))

def c27980 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27980 : Upper (D 7) (R 7) [36,320,192,48,130,1] 13 := by
  apply FastRouting.sound _ _ [36,320,192,48,130,1] 13 (by decide) (choices 1) [1,2,8] r27980 c27980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10381
  · exact u10382
  · exact u10383

def b27981 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 3, region := 197, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 196 56 146 34 73 137 265), lower := (rows 37 322 196 56 146 34 64 128 256), losses := [] }

theorem u27981 : Upper (D 7) (R 7) [36,320,192,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27982 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 322 196 56 146 40 67 131 259), lower := (rows 37 322 196 56 146 40 64 128 256), losses := [] }

theorem u27982 : Upper (D 7) (R 7) [36,320,192,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27982 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27983 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 25 148 34 328 456 328), lower := (rows 97 162 7 25 148 34 64 128 256), losses := [] }

theorem u27983 : Upper (D 7) (R 7) [96,160,3,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27984 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 2, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 162 7 25 148 40 322 450 322), lower := (rows 97 162 7 25 148 40 64 128 256), losses := [] }

theorem u27984 : Upper (D 7) (R 7) [96,160,3,17,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27984 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27985 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 25 148 96 330 394 266), lower := (rows 97 162 7 25 148 96 64 128 256), losses := [] }

theorem u27985 : Upper (D 7) (R 7) [96,160,3,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27986 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 162 7 25 148 288 74 202 330), lower := (rows 97 162 7 25 148 288 64 128 256), losses := [] }

theorem u27986 : Upper (D 7) (R 7) [96,160,3,17,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27986 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27987 : Route 9 := (fun mask => (mask,id))

def c27987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27987 : Upper (D 7) (R 7) [96,160,3,17,258,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,258,4] 13 (by decide) (choices 1) [8,128] r27987 c27987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10384
  · exact u10385

def b27988 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 464, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 97 162 7 25 274 40 196 196 452), lower := (rows 97 162 7 25 274 40 64 128 256), losses := [] }

theorem u27988 : Upper (D 7) (R 7) [96,160,3,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27988 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27989 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 25 274 96 204 140 396), lower := (rows 97 162 7 25 274 96 64 128 256), losses := [] }

theorem u27989 : Upper (D 7) (R 7) [96,160,3,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27990 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 25 274 160 76 204 332), lower := (rows 97 162 7 25 274 160 64 128 256), losses := [] }

theorem u27990 : Upper (D 7) (R 7) [96,160,3,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27991 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 25 276 34 200 200 456), lower := (rows 97 162 7 25 276 34 64 128 256), losses := [] }

theorem u27991 : Upper (D 7) (R 7) [96,160,3,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27992 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 0, region := 130, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 162 7 25 276 40 194 194 450), lower := (rows 97 162 7 25 276 40 64 128 256), losses := [] }

theorem u27992 : Upper (D 7) (R 7) [96,160,3,17,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27992 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27993 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 25 276 96 202 138 394), lower := (rows 97 162 7 25 276 96 64 128 256), losses := [] }

theorem u27993 : Upper (D 7) (R 7) [96,160,3,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27994 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 25 276 160 74 202 330), lower := (rows 97 162 7 25 276 160 64 128 256), losses := [] }

theorem u27994 : Upper (D 7) (R 7) [96,160,3,17,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27995 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 25 280 34 196 196 452), lower := (rows 97 162 7 25 280 34 64 128 256), losses := [] }

theorem u27995 : Upper (D 7) (R 7) [96,160,3,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27996 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 0, region := 130, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 162 7 25 280 36 194 194 450), lower := (rows 97 162 7 25 280 36 64 128 256), losses := [] }

theorem u27996 : Upper (D 7) (R 7) [96,160,3,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27996 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27997 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 25 280 96 198 134 390), lower := (rows 97 162 7 25 280 96 64 128 256), losses := [] }

theorem u27997 : Upper (D 7) (R 7) [96,160,3,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27998 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 25 280 160 70 198 326), lower := (rows 97 162 7 25 280 160 64 128 256), losses := [] }

theorem u27998 : Upper (D 7) (R 7) [96,160,3,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27999 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 25 400 34 76 204 332), lower := (rows 97 162 7 25 400 34 64 128 256), losses := [] }

theorem u27999 : Upper (D 7) (R 7) [96,160,3,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28000 : Route 9 := (fun mask => (mask,id))

def c28000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28000 : Upper (D 7) (R 7) [96,160,3,17,384,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,384,4] 13 (by decide) (choices 1) [2,8] r28000 c28000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10386
  · exact u10387

def b28001 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 162 7 25 400 40 70 198 326), lower := (rows 97 162 7 25 400 40 64 128 256), losses := [] }

theorem u28001 : Upper (D 7) (R 7) [96,160,3,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28001 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28002 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 25 400 96 78 142 270), lower := (rows 97 162 7 25 400 96 64 128 256), losses := [] }

theorem u28002 : Upper (D 7) (R 7) [96,160,3,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28003 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 28 82 33 456 392 392), lower := (rows 97 162 7 28 82 33 64 128 256), losses := [] }

theorem u28003 : Upper (D 7) (R 7) [96,160,3,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28004 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 28 82 40 449 385 385), lower := (rows 97 162 7 28 82 40 64 128 256), losses := [] }

theorem u28004 : Upper (D 7) (R 7) [96,160,3,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28004 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28005 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 28 82 160 329 393 265), lower := (rows 97 162 7 28 82 160 64 128 256), losses := [] }

theorem u28005 : Upper (D 7) (R 7) [96,160,3,20,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28006 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 481, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 162 7 28 82 288 201 137 393), lower := (rows 97 162 7 28 82 288 64 128 256), losses := [] }

theorem u28006 : Upper (D 7) (R 7) [96,160,3,20,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28006 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28007 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 28 208 33 330 394 266), lower := (rows 97 162 7 28 208 33 64 128 256), losses := [] }

theorem u28007 : Upper (D 7) (R 7) [96,160,3,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28008 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(2,6)], upper := (rows 97 162 7 28 208 40 323 387 259), lower := (rows 97 162 7 28 208 40 64 128 256), losses := [] }

theorem u28008 : Upper (D 7) (R 7) [96,160,3,20,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28008 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28009 : Route 9 := (fun mask => (mask,id))

def c28009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28009 : Upper (D 7) (R 7) [96,160,3,20,192,256] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20,192,256] 13 (by decide) (choices 1) [1,2,8] r28009 c28009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10388
  · exact u10389
  · exact u10390

def b28010 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 28 273 34 200 200 456), lower := (rows 97 162 7 28 273 34 64 128 256), losses := [] }

theorem u28010 : Upper (D 7) (R 7) [96,160,3,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28011 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 0, region := 130, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 162 7 28 273 40 194 194 450), lower := (rows 97 162 7 28 273 40 64 128 256), losses := [] }

theorem u28011 : Upper (D 7) (R 7) [96,160,3,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28011 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28012 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 28 273 96 202 138 394), lower := (rows 97 162 7 28 273 96 64 128 256), losses := [] }

theorem u28012 : Upper (D 7) (R 7) [96,160,3,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28013 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 28 273 160 74 202 330), lower := (rows 97 162 7 28 273 160 64 128 256), losses := [] }

theorem u28013 : Upper (D 7) (R 7) [96,160,3,20,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28014 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 28 280 33 194 194 450), lower := (rows 97 162 7 28 280 33 64 128 256), losses := [] }

theorem u28014 : Upper (D 7) (R 7) [96,160,3,20,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28015 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 7 28 280 96 195 131 387), lower := (rows 97 162 7 28 280 96 64 128 256), losses := [] }

theorem u28015 : Upper (D 7) (R 7) [96,160,3,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28016 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 28 336 33 202 138 394), lower := (rows 97 162 7 28 336 33 64 128 256), losses := [] }

theorem u28016 : Upper (D 7) (R 7) [96,160,3,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28017 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 28 336 34 201 137 393), lower := (rows 97 162 7 28 336 34 64 128 256), losses := [] }

theorem u28017 : Upper (D 7) (R 7) [96,160,3,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28018 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 2, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 162 7 28 336 40 195 131 387), lower := (rows 97 162 7 28 336 40 64 128 256), losses := [] }

theorem u28018 : Upper (D 7) (R 7) [96,160,3,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28018 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28019 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 28 336 160 75 139 267), lower := (rows 97 162 7 28 336 160 64 128 256), losses := [] }

theorem u28019 : Upper (D 7) (R 7) [96,160,3,20,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28019
end Delivery.IrregularNine14.P07
