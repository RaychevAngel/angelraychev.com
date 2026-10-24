import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0050

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13980 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 73 148 34 324 452 324), lower := (rows 11 50 37 73 148 34 64 128 256), losses := [] }

theorem u13980 : Upper (D 6) (R 6) [10,48,33,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13981 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 73 148 36 322 450 322), lower := (rows 11 50 37 73 148 36 64 128 256), losses := [] }

theorem u13981 : Upper (D 6) (R 6) [10,48,33,65,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13982 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 37 73 148 96 326 390 262), lower := (rows 11 50 37 73 148 96 64 128 256), losses := [] }

theorem u13982 : Upper (D 6) (R 6) [10,48,33,65,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13983 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 50 37 73 148 288 70 198 326), lower := (rows 11 50 37 73 148 288 64 128 256), losses := [] }

theorem u13983 : Upper (D 6) (R 6) [10,48,33,65,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13983 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13984 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 73 400 34 68 196 324), lower := (rows 11 50 37 73 400 34 64 128 256), losses := [] }

theorem u13984 : Upper (D 6) (R 6) [10,48,33,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13985 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 50 37 73 400 36 70 198 326), lower := (rows 11 50 37 73 400 36 64 128 256), losses := [] }

theorem u13985 : Upper (D 6) (R 6) [10,48,33,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13986 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 37 73 400 96 70 134 262), lower := (rows 11 50 37 73 400 96 64 128 256), losses := [] }

theorem u13986 : Upper (D 6) (R 6) [10,48,33,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13987 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 76 81 34 452 388 388), lower := (rows 11 50 37 76 81 34 64 128 256), losses := [] }

theorem u13987 : Upper (D 6) (R 6) [10,48,33,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13988 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 50 37 76 81 36 450 386 386), lower := (rows 11 50 37 76 81 36 64 128 256), losses := [] }

theorem u13988 : Upper (D 6) (R 6) [10,48,33,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13989 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 50 37 76 81 160 326 390 262), lower := (rows 11 50 37 76 81 160 64 128 256), losses := [] }

theorem u13989 : Upper (D 6) (R 6) [10,48,33,68,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13989 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13990 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 76 145 34 324 452 324), lower := (rows 11 50 37 76 145 34 64 128 256), losses := [] }

theorem u13990 : Upper (D 6) (R 6) [10,48,33,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13991 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 464, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 37 76 145 36 322 450 322), lower := (rows 11 50 37 76 145 36 64 128 256), losses := [] }

theorem u13991 : Upper (D 6) (R 6) [10,48,33,68,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13992 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 37 76 145 96 326 390 262), lower := (rows 11 50 37 76 145 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 48 37 108 149 96 96 128 256) }] }

theorem u13992 : Upper (D 6) (R 6) [10,48,33,68,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13993 : Route 9 := (fun mask => (mask,id))

def c13993 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13993 : Upper (D 6) (R 6) [10,48,33,68,129,256] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,129,256] 13 (by decide) (choices 1) [2,4] r13993 c13993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3007
  · exact u3008

def b13994 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 76 148 33 322 450 322), lower := (rows 11 50 37 76 148 33 64 128 256), losses := [] }

theorem u13994 : Upper (D 6) (R 6) [10,48,33,68,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13995 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 76 148 34 321 449 321), lower := (rows 11 50 37 76 148 34 64 128 256), losses := [] }

theorem u13995 : Upper (D 6) (R 6) [10,48,33,68,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13996 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 37 76 148 96 323 387 259), lower := (rows 11 50 37 76 148 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 48 37 108 148 96 96 128 256) }] }

theorem u13996 : Upper (D 6) (R 6) [10,48,33,68,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13997 : PairBound 9 := { available := 67, camps := [], pairs := [(1,2),(3,5)], upper := (rows 11 50 37 76 148 288 67 195 323), lower := (rows 11 50 37 76 148 288 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 293 65 129 257), good := (rows 491 50 481 104 178 288 64 128 288) },{ target := 5, region := (rows 1 2 4 12 20 0 65 129 257), good := (rows 459 18 477 92 156 256 64 128 256) }] }

theorem u13997 : Upper (D 6) (R 6) [10,48,33,68,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13997 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13998 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 76 208 33 326 390 262), lower := (rows 11 50 37 76 208 33 64 128 256), losses := [] }

theorem u13998 : Upper (D 6) (R 6) [10,48,33,68,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13999 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 76 208 34 325 389 261), lower := (rows 11 50 37 76 208 34 64 128 256), losses := [] }

theorem u13999 : Upper (D 6) (R 6) [10,48,33,68,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14000 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 50 37 76 208 36 323 387 259), lower := (rows 11 50 37 76 208 36 64 128 256), losses := [] }

theorem u14000 : Upper (D 6) (R 6) [10,48,33,68,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14001 : Route 9 := (fun mask => (mask,id))

def c14001 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14001 : Upper (D 6) (R 6) [10,48,33,68,192,256] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,192,256] 13 (by decide) (choices 1) [1,2,4] r14001 c14001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3009
  · exact u3010
  · exact u3011

def b14002 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 76 400 33 70 198 326), lower := (rows 11 50 37 76 400 33 64 128 256), losses := [] }

theorem u14002 : Upper (D 6) (R 6) [10,48,33,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14003 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 76 400 34 69 197 325), lower := (rows 11 50 37 76 400 34 64 128 256), losses := [] }

theorem u14003 : Upper (D 6) (R 6) [10,48,33,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14004 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 464, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 37 76 400 36 67 195 323), lower := (rows 11 50 37 76 400 36 64 128 256), losses := [] }

theorem u14004 : Upper (D 6) (R 6) [10,48,33,68,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14005 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 37 76 400 96 71 135 263), lower := (rows 11 50 37 76 400 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 48 37 108 400 96 96 128 256) }] }

theorem u14005 : Upper (D 6) (R 6) [10,48,33,68,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14006 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 137 84 34 324 452 324), lower := (rows 11 50 37 137 84 34 64 128 256), losses := [] }

theorem u14006 : Upper (D 6) (R 6) [10,48,33,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14007 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 137 84 36 322 450 322), lower := (rows 11 50 37 137 84 36 64 128 256), losses := [] }

theorem u14007 : Upper (D 6) (R 6) [10,48,33,129,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14008 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 137 84 96 326 390 262), lower := (rows 11 50 37 137 84 96 64 128 256), losses := [] }

theorem u14008 : Upper (D 6) (R 6) [10,48,33,129,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14009 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 50 37 137 84 288 70 198 326), lower := (rows 11 50 37 137 84 288 64 128 256), losses := [] }

theorem u14009 : Upper (D 6) (R 6) [10,48,33,129,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14009 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14010 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 137 276 34 68 196 324), lower := (rows 11 50 37 137 276 34 64 128 256), losses := [] }

theorem u14010 : Upper (D 6) (R 6) [10,48,33,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14011 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 137 276 36 66 194 322), lower := (rows 11 50 37 137 276 36 64 128 256), losses := [] }

theorem u14011 : Upper (D 6) (R 6) [10,48,33,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14012 : Route 9 := (fun mask => (mask,id))

def c14012 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14012 : Upper (D 6) (R 6) [10,48,33,129,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,33,129,260,64] 13 (by decide) (choices 1) [2,4] r14012 c14012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3012
  · exact u3013

def b14013 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 137 336 34 68 196 324), lower := (rows 11 50 37 137 336 34 64 128 256), losses := [] }

theorem u14013 : Upper (D 6) (R 6) [10,48,33,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14014 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 50 37 137 336 36 70 198 326), lower := (rows 11 50 37 137 336 36 64 128 256), losses := [] }

theorem u14014 : Upper (D 6) (R 6) [10,48,33,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14015 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 137 336 96 70 134 262), lower := (rows 11 50 37 137 336 96 64 128 256), losses := [] }

theorem u14015 : Upper (D 6) (R 6) [10,48,33,129,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14016 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 140 81 34 324 452 324), lower := (rows 11 50 37 140 81 34 64 128 256), losses := [] }

theorem u14016 : Upper (D 6) (R 6) [10,48,33,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14017 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 37 140 81 36 322 450 322), lower := (rows 11 50 37 140 81 36 64 128 256), losses := [] }

theorem u14017 : Upper (D 6) (R 6) [10,48,33,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14018 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 140 81 96 326 390 262), lower := (rows 11 50 37 140 81 96 64 128 256), losses := [] }

theorem u14018 : Upper (D 6) (R 6) [10,48,33,132,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14019 : Route 9 := (fun mask => (mask,id))

def c14019 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14019 : Upper (D 6) (R 6) [10,48,33,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,65,256] 13 (by decide) (choices 1) [2,4] r14019 c14019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3014
  · exact u3015

def b14020 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 140 84 33 322 450 322), lower := (rows 11 50 37 140 84 33 64 128 256), losses := [] }

theorem u14020 : Upper (D 6) (R 6) [10,48,33,132,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14021 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 140 84 34 321 449 321), lower := (rows 11 50 37 140 84 34 64 128 256), losses := [] }

theorem u14021 : Upper (D 6) (R 6) [10,48,33,132,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14022 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 140 84 96 323 387 259), lower := (rows 11 50 37 140 84 96 64 128 256), losses := [] }

theorem u14022 : Upper (D 6) (R 6) [10,48,33,132,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14023 : PairBound 9 := { available := 67, camps := [], pairs := [(1,2),(3,5)], upper := (rows 11 50 37 140 84 288 67 195 323), lower := (rows 11 50 37 140 84 288 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 293 65 129 257), good := (rows 491 50 481 168 114 288 64 128 288) },{ target := 5, region := (rows 1 2 4 12 20 0 65 129 257), good := (rows 459 18 477 156 92 256 64 128 256) }] }

theorem u14023 : Upper (D 6) (R 6) [10,48,33,132,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14023 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14024 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 140 273 34 68 196 324), lower := (rows 11 50 37 140 273 34 64 128 256), losses := [] }

theorem u14024 : Upper (D 6) (R 6) [10,48,33,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14025 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 37 140 273 36 66 194 322), lower := (rows 11 50 37 140 273 36 64 128 256), losses := [] }

theorem u14025 : Upper (D 6) (R 6) [10,48,33,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14026 : Route 9 := (fun mask => (mask,id))

def c14026 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14026 : Upper (D 6) (R 6) [10,48,33,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,257,64] 13 (by decide) (choices 1) [2,4] r14026 c14026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3016
  · exact u3017

def b14027 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 140 276 33 66 194 322), lower := (rows 11 50 37 140 276 33 64 128 256), losses := [] }

theorem u14027 : Upper (D 6) (R 6) [10,48,33,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14028 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 140 276 34 65 193 321), lower := (rows 11 50 37 140 276 34 64 128 256), losses := [] }

theorem u14028 : Upper (D 6) (R 6) [10,48,33,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14029 : PairBound 9 := { available := 67, camps := [], pairs := [(1,2),(3,5),(4,5)], upper := (rows 11 50 37 140 276 96 67 195 323), lower := (rows 11 50 37 140 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 101 65 129 257), good := (rows 491 50 481 168 306 96 96 128 256) },{ target := 5, region := (rows 1 2 4 12 20 0 65 129 257), good := (rows 459 18 477 156 284 64 64 128 256) }] }

theorem u14029 : Upper (D 6) (R 6) [10,48,33,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14030 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 140 336 33 70 198 326), lower := (rows 11 50 37 140 336 33 64 128 256), losses := [] }

theorem u14030 : Upper (D 6) (R 6) [10,48,33,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14031 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 140 336 34 69 197 325), lower := (rows 11 50 37 140 336 34 64 128 256), losses := [] }

theorem u14031 : Upper (D 6) (R 6) [10,48,33,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14032 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 37 140 336 36 67 195 323), lower := (rows 11 50 37 140 336 36 64 128 256), losses := [] }

theorem u14032 : Upper (D 6) (R 6) [10,48,33,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14033 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 140 336 96 71 135 263), lower := (rows 11 50 37 140 336 96 64 128 256), losses := [] }

theorem u14033 : Upper (D 6) (R 6) [10,48,33,132,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14034 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 200 81 34 324 388 260), lower := (rows 11 50 37 200 81 34 64 128 256), losses := [] }

theorem u14034 : Upper (D 6) (R 6) [10,48,33,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14035 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 38, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 50 37 200 81 36 326 390 262), lower := (rows 11 50 37 200 81 36 64 128 256), losses := [] }

theorem u14035 : Upper (D 6) (R 6) [10,48,33,192,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14036 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 294, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 50 37 200 81 288 70 134 262), lower := (rows 11 50 37 200 81 288 64 128 256), losses := [] }

theorem u14036 : Upper (D 6) (R 6) [10,48,33,192,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14036 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14037 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 200 84 33 326 390 262), lower := (rows 11 50 37 200 84 33 64 128 256), losses := [] }

theorem u14037 : Upper (D 6) (R 6) [10,48,33,192,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14038 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 200 84 34 325 389 261), lower := (rows 11 50 37 200 84 34 64 128 256), losses := [] }

theorem u14038 : Upper (D 6) (R 6) [10,48,33,192,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14039 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 200 84 36 323 387 259), lower := (rows 11 50 37 200 84 36 64 128 256), losses := [] }

theorem u14039 : Upper (D 6) (R 6) [10,48,33,192,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14039
end Delivery.IrregularNine14.P06
