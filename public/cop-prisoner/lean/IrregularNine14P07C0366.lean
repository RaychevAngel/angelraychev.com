import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0109

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r21960 : Route 9 := (fun mask => (mask,id))

def c21960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21960 : Upper (D 7) (R 7) [34,320,40,65,132,128] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,132,128] 13 (by decide) (choices 1) [1,2,16] r21960 c21960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6587
  · exact u6588
  · exact u6589

def b21961 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 322 44 88 145 33 198 134 390), lower := (rows 35 322 44 88 145 33 64 128 256), losses := [] }

theorem u21961 : Upper (D 7) (R 7) [34,320,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21962 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 88 145 34 197 133 389), lower := (rows 35 322 44 88 145 34 64 128 256), losses := [] }

theorem u21962 : Upper (D 7) (R 7) [34,320,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21963 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 88 145 36 195 131 387), lower := (rows 35 322 44 88 145 36 64 128 256), losses := [] }

theorem u21963 : Upper (D 7) (R 7) [34,320,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21963 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21964 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 35 322 44 88 145 160 71 135 263), lower := (rows 35 322 44 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 322 44 124 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 320 44 124 177 160 64 160 256) }] }

theorem u21964 : Upper (D 7) (R 7) [34,320,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21965 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 44 88 146 33 197 133 389), lower := (rows 35 322 44 88 146 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 136 264), good := (rows 35 291 428 445 179 33 0 128 256) },{ target := 7, region := (rows 19 2 12 8 16 59 64 0 256), good := (rows 35 355 44 125 51 33 64 0 256) }] }

theorem u21965 : Upper (D 7) (R 7) [34,320,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21966 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 88 146 36 193 129 385), lower := (rows 35 322 44 88 146 36 64 128 256), losses := [] }

theorem u21966 : Upper (D 7) (R 7) [34,320,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21966 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21967 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,0)], upper := (rows 35 322 44 88 146 160 69 133 261), lower := (rows 35 322 44 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 322 44 124 178 160 64 160 256) }] }

theorem u21967 : Upper (D 7) (R 7) [34,320,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21968 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(3,5)], upper := (rows 35 322 44 88 148 33 195 131 387), lower := (rows 35 322 44 88 148 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 322 478 88 158 451 64 128 256) }] }

theorem u21968 : Upper (D 7) (R 7) [34,320,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21969 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 88 148 34 193 129 385), lower := (rows 35 322 44 88 148 34 64 128 256), losses := [] }

theorem u21969 : Upper (D 7) (R 7) [34,320,40,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21970 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7)], upper := (rows 35 322 44 88 148 160 67 131 259), lower := (rows 35 322 44 88 148 160 64 128 256), losses := [] }

theorem u21970 : Upper (D 7) (R 7) [34,320,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21971 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 137 81 34 212 148 404), lower := (rows 35 322 44 137 81 34 64 128 256), losses := [] }

theorem u21971 : Upper (D 7) (R 7) [34,320,40,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21972 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 137 81 36 210 146 402), lower := (rows 35 322 44 137 81 36 64 128 256), losses := [] }

theorem u21972 : Upper (D 7) (R 7) [34,320,40,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21972 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21973 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 44 137 81 48 198 134 390), lower := (rows 35 322 44 137 81 48 64 128 256), losses := [] }

theorem u21973 : Upper (D 7) (R 7) [34,320,40,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21973 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21974 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 322 44 137 81 160 86 150 278), lower := (rows 35 322 44 137 81 160 64 128 256), losses := [] }

theorem u21974 : Upper (D 7) (R 7) [34,320,40,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21975 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 44 137 84 33 210 146 402), lower := (rows 35 322 44 137 84 33 64 128 256), losses := [] }

theorem u21975 : Upper (D 7) (R 7) [34,320,40,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21976 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 137 84 34 209 145 401), lower := (rows 35 322 44 137 84 34 64 128 256), losses := [] }

theorem u21976 : Upper (D 7) (R 7) [34,320,40,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21977 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(1,5),(2,6),(3,5)], upper := (rows 35 322 44 137 84 48 195 131 387), lower := (rows 35 322 44 137 84 48 64 128 256), losses := [] }

theorem u21977 : Upper (D 7) (R 7) [34,320,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21977 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21978 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 322 44 137 84 160 83 147 275), lower := (rows 35 322 44 137 84 160 64 128 256), losses := [] }

theorem u21978 : Upper (D 7) (R 7) [34,320,40,129,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21979 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 44 137 146 33 84 212 340), lower := (rows 35 322 44 137 146 33 64 128 256), losses := [] }

theorem u21979 : Upper (D 7) (R 7) [34,320,40,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21980 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 137 146 36 81 209 337), lower := (rows 35 322 44 137 146 36 64 128 256), losses := [] }

theorem u21980 : Upper (D 7) (R 7) [34,320,40,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21980 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21981 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 44 137 146 48 69 197 325), lower := (rows 35 322 44 137 146 48 64 128 256), losses := [] }

theorem u21981 : Upper (D 7) (R 7) [34,320,40,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21981 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21982 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 44 137 146 96 85 149 277), lower := (rows 35 322 44 137 146 96 64 128 256), losses := [] }

theorem u21982 : Upper (D 7) (R 7) [34,320,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21983 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 44 137 148 33 82 210 338), lower := (rows 35 322 44 137 148 33 64 128 256), losses := [] }

theorem u21983 : Upper (D 7) (R 7) [34,320,40,129,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21984 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 137 148 34 81 209 337), lower := (rows 35 322 44 137 148 34 64 128 256), losses := [] }

theorem u21984 : Upper (D 7) (R 7) [34,320,40,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21985 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 137 148 48 67 195 323), lower := (rows 35 322 44 137 148 48 64 128 256), losses := [] }

theorem u21985 : Upper (D 7) (R 7) [34,320,40,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21985 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21986 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 44 137 148 96 83 147 275), lower := (rows 35 322 44 137 148 96 64 128 256), losses := [] }

theorem u21986 : Upper (D 7) (R 7) [34,320,40,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21987 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 44 137 208 33 86 150 278), lower := (rows 35 322 44 137 208 33 64 128 256), losses := [] }

theorem u21987 : Upper (D 7) (R 7) [34,320,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21988 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 137 208 34 85 149 277), lower := (rows 35 322 44 137 208 34 64 128 256), losses := [] }

theorem u21988 : Upper (D 7) (R 7) [34,320,40,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21989 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 137 208 36 83 147 275), lower := (rows 35 322 44 137 208 36 64 128 256), losses := [] }

theorem u21989 : Upper (D 7) (R 7) [34,320,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21989 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21990 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 44 137 208 48 71 135 263), lower := (rows 35 322 44 137 208 48 64 128 256), losses := [] }

theorem u21990 : Upper (D 7) (R 7) [34,320,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21990 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21991 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 44 138 81 33 212 148 404), lower := (rows 35 322 44 138 81 33 64 128 256), losses := [] }

theorem u21991 : Upper (D 7) (R 7) [34,320,40,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21992 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 44 138 81 36 209 145 401), lower := (rows 35 322 44 138 81 36 64 128 256), losses := [] }

theorem u21992 : Upper (D 7) (R 7) [34,320,40,130,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21992 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21993 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 44 138 81 48 197 133 389), lower := (rows 35 322 44 138 81 48 64 128 256), losses := [] }

theorem u21993 : Upper (D 7) (R 7) [34,320,40,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21993 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21994 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 322 44 138 81 160 85 149 277), lower := (rows 35 322 44 138 81 160 64 128 256), losses := [] }

theorem u21994 : Upper (D 7) (R 7) [34,320,40,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21995 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 44 138 84 33 209 145 401), lower := (rows 35 322 44 138 84 33 64 128 256), losses := [] }

theorem u21995 : Upper (D 7) (R 7) [34,320,40,130,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21996 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(1,5),(2,6),(3,5)], upper := (rows 35 322 44 138 84 48 193 129 385), lower := (rows 35 322 44 138 84 48 64 128 256), losses := [] }

theorem u21996 : Upper (D 7) (R 7) [34,320,40,130,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21996 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21997 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 322 44 138 84 160 81 145 273), lower := (rows 35 322 44 138 84 160 64 128 256), losses := [] }

theorem u21997 : Upper (D 7) (R 7) [34,320,40,130,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21998 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 322 44 138 145 33 84 212 340), lower := (rows 35 322 44 138 145 33 64 128 256), losses := [] }

theorem u21998 : Upper (D 7) (R 7) [34,320,40,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21999 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 44 138 145 36 81 209 337), lower := (rows 35 322 44 138 145 36 64 128 256), losses := [] }

theorem u21999 : Upper (D 7) (R 7) [34,320,40,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21999 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22000 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 44 138 145 48 69 197 325), lower := (rows 35 322 44 138 145 48 64 128 256), losses := [] }

theorem u22000 : Upper (D 7) (R 7) [34,320,40,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22000 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22001 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 44 138 145 96 85 149 277), lower := (rows 35 322 44 138 145 96 64 128 256), losses := [] }

theorem u22001 : Upper (D 7) (R 7) [34,320,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22002 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 322 44 138 148 33 81 209 337), lower := (rows 35 322 44 138 148 33 64 128 256), losses := [] }

theorem u22002 : Upper (D 7) (R 7) [34,320,40,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22003 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 322 44 138 148 48 65 193 321), lower := (rows 35 322 44 138 148 48 64 128 256), losses := [] }

theorem u22003 : Upper (D 7) (R 7) [34,320,40,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22003 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22004 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 44 138 148 96 81 145 273), lower := (rows 35 322 44 138 148 96 64 128 256), losses := [] }

theorem u22004 : Upper (D 7) (R 7) [34,320,40,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22005 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 44 138 208 33 85 149 277), lower := (rows 35 322 44 138 208 33 64 128 256), losses := [] }

theorem u22005 : Upper (D 7) (R 7) [34,320,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22006 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 44 138 208 36 81 145 273), lower := (rows 35 322 44 138 208 36 64 128 256), losses := [] }

theorem u22006 : Upper (D 7) (R 7) [34,320,40,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22006 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22007 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 44 138 208 48 69 133 261), lower := (rows 35 322 44 138 208 48 64 128 256), losses := [] }

theorem u22007 : Upper (D 7) (R 7) [34,320,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22007 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22008 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(1,5),(4,5),(4,7)], upper := (rows 35 322 44 140 81 33 210 146 402), lower := (rows 35 322 44 140 81 33 64 128 256), losses := [] }

theorem u22008 : Upper (D 7) (R 7) [34,320,40,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22009 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 140 81 34 209 145 401), lower := (rows 35 322 44 140 81 34 64 128 256), losses := [] }

theorem u22009 : Upper (D 7) (R 7) [34,320,40,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22010 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 35 322 44 140 81 48 195 131 387), lower := (rows 35 322 44 140 81 48 64 128 256), losses := [] }

theorem u22010 : Upper (D 7) (R 7) [34,320,40,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22010 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22011 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 12, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 322 44 140 81 160 83 147 275), lower := (rows 35 322 44 140 81 160 64 128 256), losses := [] }

theorem u22011 : Upper (D 7) (R 7) [34,320,40,132,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22012 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 322 44 152 81 33 198 134 390), lower := (rows 35 322 44 152 81 33 64 128 256), losses := [] }

theorem u22012 : Upper (D 7) (R 7) [34,320,40,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22013 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 152 81 34 197 133 389), lower := (rows 35 322 44 152 81 34 64 128 256), losses := [] }

theorem u22013 : Upper (D 7) (R 7) [34,320,40,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22014 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 152 81 36 195 131 387), lower := (rows 35 322 44 152 81 36 64 128 256), losses := [] }

theorem u22014 : Upper (D 7) (R 7) [34,320,40,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22014 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22015 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 322 44 152 81 160 71 135 263), lower := (rows 35 322 44 152 81 160 64 128 256), losses := [] }

theorem u22015 : Upper (D 7) (R 7) [34,320,40,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22016 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(3,5)], upper := (rows 35 322 44 152 84 33 195 131 387), lower := (rows 35 322 44 152 84 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 322 478 152 94 451 64 128 256) }] }

theorem u22016 : Upper (D 7) (R 7) [34,320,40,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22017 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 152 84 34 193 129 385), lower := (rows 35 322 44 152 84 34 64 128 256), losses := [] }

theorem u22017 : Upper (D 7) (R 7) [34,320,40,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22018 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 322 44 152 84 160 67 131 259), lower := (rows 35 322 44 152 84 160 64 128 256), losses := [] }

theorem u22018 : Upper (D 7) (R 7) [34,320,40,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22019 : Route 9 := (fun mask => (mask,id))

def c22019 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22019 : Upper (D 7) (R 7) [34,320,40,192,129,1] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,129,1] 13 (by decide) (choices 1) [2,4,16] r22019 c22019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6590
  · exact u6591
  · exact u6592

#print axioms u22019
end Delivery.IrregularNine14.P07
