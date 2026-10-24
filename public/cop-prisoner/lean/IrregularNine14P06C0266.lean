import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0064

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15960 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 134 37 104 82 288 85 149 277), lower := (rows 11 134 37 104 82 288 64 128 256), losses := [] }

theorem u15960 : Upper (D 6) (R 6) [10,132,33,96,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15960 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15961 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 104 84 33 338 402 274), lower := (rows 11 134 37 104 84 33 64 128 256), losses := [] }

theorem u15961 : Upper (D 6) (R 6) [10,132,33,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15962 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 104 84 34 337 401 273), lower := (rows 11 134 37 104 84 34 64 128 256), losses := [] }

theorem u15962 : Upper (D 6) (R 6) [10,132,33,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15963 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 104 84 48 323 387 259), lower := (rows 11 134 37 104 84 48 64 128 256), losses := [] }

theorem u15963 : Upper (D 6) (R 6) [10,132,33,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15963 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15964 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 134 37 104 84 288 83 147 275), lower := (rows 11 134 37 104 84 288 64 128 256), losses := [] }

theorem u15964 : Upper (D 6) (R 6) [10,132,33,96,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15964 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15965 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 104 273 34 84 212 340), lower := (rows 11 134 37 104 273 34 64 128 256), losses := [] }

theorem u15965 : Upper (D 6) (R 6) [10,132,33,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15966 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 104 273 36 82 210 338), lower := (rows 11 134 37 104 273 36 64 128 256), losses := [] }

theorem u15966 : Upper (D 6) (R 6) [10,132,33,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15967 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 134 37 104 273 48 70 198 326), lower := (rows 11 134 37 104 273 48 64 128 256), losses := [] }

theorem u15967 : Upper (D 6) (R 6) [10,132,33,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15967 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15968 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 104 273 96 86 150 278), lower := (rows 11 134 37 104 273 96 64 128 256), losses := [] }

theorem u15968 : Upper (D 6) (R 6) [10,132,33,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15969 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 104 274 33 84 212 340), lower := (rows 11 134 37 104 274 33 64 128 256), losses := [] }

theorem u15969 : Upper (D 6) (R 6) [10,132,33,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15970 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 104 274 36 81 209 337), lower := (rows 11 134 37 104 274 36 64 128 256), losses := [] }

theorem u15970 : Upper (D 6) (R 6) [10,132,33,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15971 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 134 37 104 274 48 69 197 325), lower := (rows 11 134 37 104 274 48 64 128 256), losses := [] }

theorem u15971 : Upper (D 6) (R 6) [10,132,33,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15971 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15972 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 104 274 96 85 149 277), lower := (rows 11 134 37 104 274 96 64 128 256), losses := [] }

theorem u15972 : Upper (D 6) (R 6) [10,132,33,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15973 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 104 276 33 82 210 338), lower := (rows 11 134 37 104 276 33 64 128 256), losses := [] }

theorem u15973 : Upper (D 6) (R 6) [10,132,33,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15974 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 104 276 34 81 209 337), lower := (rows 11 134 37 104 276 34 64 128 256), losses := [] }

theorem u15974 : Upper (D 6) (R 6) [10,132,33,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15975 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 134 37 104 276 48 67 195 323), lower := (rows 11 134 37 104 276 48 64 128 256), losses := [] }

theorem u15975 : Upper (D 6) (R 6) [10,132,33,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15975 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15976 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 104 276 96 83 147 275), lower := (rows 11 134 37 104 276 96 64 128 256), losses := [] }

theorem u15976 : Upper (D 6) (R 6) [10,132,33,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15977 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 104 336 33 86 150 278), lower := (rows 11 134 37 104 336 33 64 128 256), losses := [] }

theorem u15977 : Upper (D 6) (R 6) [10,132,33,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15978 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 104 336 34 85 149 277), lower := (rows 11 134 37 104 336 34 64 128 256), losses := [] }

theorem u15978 : Upper (D 6) (R 6) [10,132,33,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15979 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 104 336 36 83 147 275), lower := (rows 11 134 37 104 336 36 64 128 256), losses := [] }

theorem u15979 : Upper (D 6) (R 6) [10,132,33,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15980 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 104 336 48 71 135 263), lower := (rows 11 134 37 104 336 48 64 128 256), losses := [] }

theorem u15980 : Upper (D 6) (R 6) [10,132,33,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15980 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15981 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 265 50 36 80 208 336), lower := (rows 11 134 37 265 50 36 64 128 256), losses := [] }

theorem u15981 : Upper (D 6) (R 6) [10,132,33,257,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15982 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 265 50 48 68 196 324), lower := (rows 11 134 37 265 50 48 64 128 256), losses := [] }

theorem u15982 : Upper (D 6) (R 6) [10,132,33,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15982 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15983 : Route 9 := (fun mask => (mask,id))

def c15983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15983 : Upper (D 6) (R 6) [10,132,33,257,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,34,64] 13 (by decide) (choices 1) [4,16] r15983 c15983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3866
  · exact u3867

def b15984 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 265 82 36 112 240 368), lower := (rows 11 134 37 265 82 36 64 128 256), losses := [] }

theorem u15984 : Upper (D 6) (R 6) [10,132,33,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15985 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 265 82 48 100 228 356), lower := (rows 11 134 37 265 82 48 64 128 256), losses := [] }

theorem u15985 : Upper (D 6) (R 6) [10,132,33,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15985 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15986 : Route 9 := (fun mask => (mask,id))

def c15986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15986 : Upper (D 6) (R 6) [10,132,33,257,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,66,64] 13 (by decide) (choices 1) [4,16,32] r15986 c15986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3868
  · exact u3869
  · exact u3870

def b15987 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 265 84 34 112 240 368), lower := (rows 11 134 37 265 84 34 64 128 256), losses := [] }

theorem u15987 : Upper (D 6) (R 6) [10,132,33,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15988 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 265 84 48 98 226 354), lower := (rows 11 134 37 265 84 48 64 128 256), losses := [] }

theorem u15988 : Upper (D 6) (R 6) [10,132,33,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15988 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15989 : Route 9 := (fun mask => (mask,id))

def c15989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15989 : Upper (D 6) (R 6) [10,132,33,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,68,64] 13 (by decide) (choices 1) [2,16,32] r15989 c15989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3871
  · exact u3872
  · exact u3873

def b15990 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 265 112 34 84 212 340), lower := (rows 11 134 37 265 112 34 64 128 256), losses := [] }

theorem u15990 : Upper (D 6) (R 6) [10,132,33,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15991 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 265 112 36 82 210 338), lower := (rows 11 134 37 265 112 36 64 128 256), losses := [] }

theorem u15991 : Upper (D 6) (R 6) [10,132,33,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15992 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 265 112 48 70 198 326), lower := (rows 11 134 37 265 112 48 64 128 256), losses := [] }

theorem u15992 : Upper (D 6) (R 6) [10,132,33,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15992 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15993 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 265 112 96 86 150 278), lower := (rows 11 134 37 265 112 96 64 128 256), losses := [] }

theorem u15993 : Upper (D 6) (R 6) [10,132,33,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15994 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 268 50 33 80 208 336), lower := (rows 11 134 37 268 50 33 64 128 256), losses := [] }

theorem u15994 : Upper (D 6) (R 6) [10,132,33,260,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15995 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 37 268 50 48 65 193 321), lower := (rows 11 134 37 268 50 48 64 128 256), losses := [] }

theorem u15995 : Upper (D 6) (R 6) [10,132,33,260,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15995 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15996 : Route 9 := (fun mask => (mask,id))

def c15996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15996 : Upper (D 6) (R 6) [10,132,33,260,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,34,64] 13 (by decide) (choices 1) [1,16] r15996 c15996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3874
  · exact u3875

def b15997 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 268 81 34 112 240 368), lower := (rows 11 134 37 268 81 34 64 128 256), losses := [] }

theorem u15997 : Upper (D 6) (R 6) [10,132,33,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15998 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 134 37 268 81 48 98 226 354), lower := (rows 11 134 37 268 81 48 64 128 256), losses := [] }

theorem u15998 : Upper (D 6) (R 6) [10,132,33,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15998 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15999 : Route 9 := (fun mask => (mask,id))

def c15999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15999 : Upper (D 6) (R 6) [10,132,33,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,65,64] 13 (by decide) (choices 1) [2,16,32] r15999 c15999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3876
  · exact u3877
  · exact u3878

def b16000 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 268 82 33 112 240 368), lower := (rows 11 134 37 268 82 33 64 128 256), losses := [] }

theorem u16000 : Upper (D 6) (R 6) [10,132,33,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16001 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 2, region := 328, targets := 2 }], pairs := [(3,1),(4,2)], upper := (rows 11 134 37 268 82 48 97 225 353), lower := (rows 11 134 37 268 82 48 64 128 256), losses := [] }

theorem u16001 : Upper (D 6) (R 6) [10,132,33,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16001 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16002 : Route 9 := (fun mask => (mask,id))

def c16002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16002 : Upper (D 6) (R 6) [10,132,33,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,66,64] 13 (by decide) (choices 1) [1,16,32] r16002 c16002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3879
  · exact u3880
  · exact u3881

def b16003 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 268 112 33 82 210 338), lower := (rows 11 134 37 268 112 33 64 128 256), losses := [] }

theorem u16003 : Upper (D 6) (R 6) [10,132,33,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16004 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 268 112 34 81 209 337), lower := (rows 11 134 37 268 112 34 64 128 256), losses := [] }

theorem u16004 : Upper (D 6) (R 6) [10,132,33,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16005 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 268 112 48 67 195 323), lower := (rows 11 134 37 268 112 48 64 128 256), losses := [] }

theorem u16005 : Upper (D 6) (R 6) [10,132,33,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16005 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16006 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 268 112 96 83 147 275), lower := (rows 11 134 37 268 112 96 64 128 256), losses := [] }

theorem u16006 : Upper (D 6) (R 6) [10,132,33,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16007 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 280 50 33 68 196 324), lower := (rows 11 134 37 280 50 33 64 128 256), losses := [] }

theorem u16007 : Upper (D 6) (R 6) [10,132,33,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16008 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 280 50 36 65 193 321), lower := (rows 11 134 37 280 50 36 64 128 256), losses := [] }

theorem u16008 : Upper (D 6) (R 6) [10,132,33,272,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16009 : Route 9 := (fun mask => (mask,id))

def c16009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16009 : Upper (D 6) (R 6) [10,132,33,272,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,34,64] 13 (by decide) (choices 1) [1,4] r16009 c16009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3882
  · exact u3883

def b16010 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 280 81 34 100 228 356), lower := (rows 11 134 37 280 81 34 64 128 256), losses := [] }

theorem u16010 : Upper (D 6) (R 6) [10,132,33,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16011 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 280 81 36 98 226 354), lower := (rows 11 134 37 280 81 36 64 128 256), losses := [] }

theorem u16011 : Upper (D 6) (R 6) [10,132,33,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16012 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 130, targets := 1 },{ cop := 2, region := 130, targets := 64 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 134 37 280 81 96 102 166 294), lower := (rows 11 134 37 280 81 96 64 128 256), losses := [] }

theorem u16012 : Upper (D 6) (R 6) [10,132,33,272,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16013 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 280 82 33 100 228 356), lower := (rows 11 134 37 280 82 33 64 128 256), losses := [] }

theorem u16013 : Upper (D 6) (R 6) [10,132,33,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16014 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 134 37 280 82 36 97 225 353), lower := (rows 11 134 37 280 82 36 64 128 256), losses := [{ target := 2, region := (rows 19 2 0 10 18 32 68 132 260), good := (rows 27 475 481 281 91 480 64 128 256) }] }

theorem u16014 : Upper (D 6) (R 6) [10,132,33,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16015 : Route 9 := (fun mask => (mask,id))

def c16015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16015 : Upper (D 6) (R 6) [10,132,33,272,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,66,64] 13 (by decide) (choices 1) [1,4,32] r16015 c16015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3884
  · exact u3885
  · exact u3886

def b16016 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 280 84 33 98 226 354), lower := (rows 11 134 37 280 84 33 64 128 256), losses := [] }

theorem u16016 : Upper (D 6) (R 6) [10,132,33,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16017 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 280 84 34 97 225 353), lower := (rows 11 134 37 280 84 34 64 128 256), losses := [] }

theorem u16017 : Upper (D 6) (R 6) [10,132,33,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16018 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 37 280 84 96 99 163 291), lower := (rows 11 134 37 280 84 96 64 128 256), losses := [{ target := 6, region := (rows 25 22 4 24 16 32 0 132 260), good := (rows 11 390 423 283 415 32 0 128 256) }] }

theorem u16018 : Upper (D 6) (R 6) [10,132,33,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16019 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 280 112 33 70 198 326), lower := (rows 11 134 37 280 112 33 64 128 256), losses := [] }

theorem u16019 : Upper (D 6) (R 6) [10,132,33,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16019
end Delivery.IrregularNine14.P06
