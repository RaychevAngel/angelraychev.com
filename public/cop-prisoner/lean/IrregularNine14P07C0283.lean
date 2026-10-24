import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0066
import IrregularNine14P07C0067

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16980 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 52 138 400 34 65 193 321), lower := (rows 13 98 52 138 400 34 64 128 256), losses := [] }

theorem u16980 : Upper (D 7) (R 7) [12,96,48,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16981 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 138 400 96 67 131 259), lower := (rows 13 98 52 138 400 96 64 128 256), losses := [] }

theorem u16981 : Upper (D 7) (R 7) [12,96,48,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16982 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 52 200 19 33 450 386 386), lower := (rows 13 98 52 200 19 33 64 128 256), losses := [] }

theorem u16982 : Upper (D 7) (R 7) [12,96,48,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16983 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 200 19 34 449 385 385), lower := (rows 13 98 52 200 19 34 64 128 256), losses := [] }

theorem u16983 : Upper (D 7) (R 7) [12,96,48,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16984 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 34, targets := 1 },{ cop := 4, region := 456, targets := 32 },{ cop := 4, region := 420, targets := 64 }], pairs := [(0,5),(1,0),(2,6),(3,5)], upper := (rows 13 98 52 200 19 160 323 387 259), lower := (rows 13 98 52 200 19 160 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 80 144 272), good := (rows 13 66 477 200 475 128 64 128 256) }] }

theorem u16984 : Upper (D 7) (R 7) [12,96,48,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16985 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 200, targets := 32 },{ cop := 4, region := 420, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 13 98 52 200 19 288 195 131 387), lower := (rows 13 98 52 200 19 288 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 80 144 272), good := (rows 13 66 477 200 475 256 64 128 256) }] }

theorem u16985 : Upper (D 7) (R 7) [12,96,48,192,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16985 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16986 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 200 145 33 322 386 258), lower := (rows 13 98 52 200 145 33 64 128 256), losses := [] }

theorem u16986 : Upper (D 7) (R 7) [12,96,48,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16987 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 200 145 34 323 387 259), lower := (rows 13 98 52 200 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 20 8 16 107 64 128 256), good := (rows 46 98 52 234 180 34 98 128 256) }] }

theorem u16987 : Upper (D 7) (R 7) [12,96,48,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16988 : Route 9 := (fun mask => (mask,id))

def c16988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16988 : Upper (D 7) (R 7) [12,96,48,192,129,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,129,256] 13 (by decide) (choices 1) [1,2] r16988 c16988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4017
  · exact u4018

def r16989 : Route 9 := (fun mask => (mask,id))

def c16989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16989 : Upper (D 7) (R 7) [12,96,48,192,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,130,1] 13 (by decide) (choices 1) [1,2,256] r16989 c16989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4019
  · exact u4020
  · exact u4021

def b16990 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 200 146 34 321 385 257), lower := (rows 13 98 52 200 146 34 64 128 256), losses := [] }

theorem u16990 : Upper (D 7) (R 7) [12,96,48,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16991 : Route 9 := (fun mask => (mask,id))

def c16991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16991 : Upper (D 7) (R 7) [12,96,48,192,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,130,256] 13 (by decide) (choices 1) [1,2] r16991 c16991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4022
  · exact u4023

def b16992 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 136, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 98 52 200 273 33 194 130 386), lower := (rows 13 98 52 200 273 33 64 128 256), losses := [] }

theorem u16992 : Upper (D 7) (R 7) [12,96,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16993 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 200 273 34 195 131 387), lower := (rows 13 98 52 200 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 20 8 16 107 64 128 256), good := (rows 46 98 52 234 308 34 98 128 256) },{ target := 7, region := (rows 1 74 20 8 16 107 64 0 256), good := (rows 47 98 52 106 309 34 98 0 256) }] }

theorem u16993 : Upper (D 7) (R 7) [12,96,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16994 : Route 9 := (fun mask => (mask,id))

def c16994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16994 : Upper (D 7) (R 7) [12,96,48,192,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,257,128] 13 (by decide) (choices 1) [1,2] r16994 c16994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4024
  · exact u4025

def r16995 : Route 9 := (fun mask => (mask,id))

def c16995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16995 : Upper (D 7) (R 7) [12,96,48,192,258,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,258,1] 13 (by decide) (choices 1) [1,2,128] r16995 c16995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4026
  · exact u4027
  · exact u4028

def b16996 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 200 274 34 193 129 385), lower := (rows 13 98 52 200 274 34 64 128 256), losses := [] }

theorem u16996 : Upper (D 7) (R 7) [12,96,48,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16997 : Route 9 := (fun mask => (mask,id))

def c16997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16997 : Upper (D 7) (R 7) [12,96,48,192,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,258,128] 13 (by decide) (choices 1) [1,2] r16997 c16997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4029
  · exact u4030

def r16998 : Route 9 := (fun mask => (mask,id))

def c16998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16998 : Upper (D 7) (R 7) [12,96,48,192,384,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,384,1] 13 (by decide) (choices 1) [1,2] r16998 c16998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4031
  · exact u4032

def r16999 : Route 9 := (fun mask => (mask,id))

def c16999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16999 : Upper (D 7) (R 7) [12,96,48,192,384,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,384,2] 13 (by decide) (choices 1) [1,2] r16999 c16999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4033
  · exact u4034

def b17000 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 38, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 265 81 34 194 130 386), lower := (rows 13 98 52 265 81 34 64 128 256), losses := [] }

theorem u17000 : Upper (D 7) (R 7) [12,96,48,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17001 : Route 9 := (fun mask => (mask,id))

def c17001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17001 : Upper (D 7) (R 7) [12,96,48,257,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,257,65,128] 13 (by decide) (choices 1) [2,128] r17001 c17001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4035
  · exact u4036

def b17002 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(2,0)], upper := (rows 13 98 52 265 145 34 194 194 450), lower := (rows 13 98 52 265 145 34 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 20 0 98 162 290), good := (rows 29 450 477 265 145 450 64 128 256) }] }

theorem u17002 : Upper (D 7) (R 7) [12,96,48,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17003 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 265 145 96 194 130 386), lower := (rows 13 98 52 265 145 96 64 128 256), losses := [] }

theorem u17003 : Upper (D 7) (R 7) [12,96,48,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17004 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 13 98 52 265 145 160 66 194 322), lower := (rows 13 98 52 265 145 160 64 128 256), losses := [] }

theorem u17004 : Upper (D 7) (R 7) [12,96,48,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17005 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 98 52 265 146 33 194 194 450), lower := (rows 13 98 52 265 146 33 64 128 256), losses := [] }

theorem u17005 : Upper (D 7) (R 7) [12,96,48,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17006 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 265 146 34 193 193 449), lower := (rows 13 98 52 265 146 34 64 128 256), losses := [] }

theorem u17006 : Upper (D 7) (R 7) [12,96,48,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17007 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 265 146 96 195 131 387), lower := (rows 13 98 52 265 146 96 64 128 256), losses := [] }

theorem u17007 : Upper (D 7) (R 7) [12,96,48,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17008 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 98 52 265 146 160 67 195 323), lower := (rows 13 98 52 265 146 160 64 128 256), losses := [] }

theorem u17008 : Upper (D 7) (R 7) [12,96,48,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17009 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 98 52 265 208 33 194 130 386), lower := (rows 13 98 52 265 208 33 64 128 256), losses := [] }

theorem u17009 : Upper (D 7) (R 7) [12,96,48,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17010 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 265 208 34 195 131 387), lower := (rows 13 98 52 265 208 34 64 128 256), losses := [] }

theorem u17010 : Upper (D 7) (R 7) [12,96,48,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17011 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 13 98 52 265 208 160 67 131 259), lower := (rows 13 98 52 265 208 160 64 128 256), losses := [] }

theorem u17011 : Upper (D 7) (R 7) [12,96,48,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17012 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 52 266 19 33 192 192 448), lower := (rows 13 98 52 266 19 33 64 128 256), losses := [] }

theorem u17012 : Upper (D 7) (R 7) [12,96,48,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17013 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 266 19 96 193 129 385), lower := (rows 13 98 52 266 19 96 64 128 256), losses := [] }

theorem u17013 : Upper (D 7) (R 7) [12,96,48,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17014 : Route 9 := (fun mask => (mask,id))

def c17014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17014 : Upper (D 7) (R 7) [12,96,48,258,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,3,128] 13 (by decide) (choices 1) [1,128] r17014 c17014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4037
  · exact u4038

def b17015 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 392, targets := 33 },{ cop := 4, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0),(3,5)], upper := (rows 13 98 52 266 81 33 194 130 386), lower := (rows 13 98 52 266 81 33 64 128 256), losses := [] }

theorem u17015 : Upper (D 7) (R 7) [12,96,48,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17016 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 266 81 34 193 129 385), lower := (rows 13 98 52 266 81 34 64 128 256), losses := [] }

theorem u17016 : Upper (D 7) (R 7) [12,96,48,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17017 : Route 9 := (fun mask => (mask,id))

def c17017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17017 : Upper (D 7) (R 7) [12,96,48,258,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,65,128] 13 (by decide) (choices 1) [1,2,128] r17017 c17017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4039
  · exact u4040
  · exact u4041

def b17018 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 392, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 98 52 266 145 33 194 194 450), lower := (rows 13 98 52 266 145 33 64 128 256), losses := [] }

theorem u17018 : Upper (D 7) (R 7) [12,96,48,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17019 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 52 266 145 34 193 193 449), lower := (rows 13 98 52 266 145 34 64 128 256), losses := [] }

theorem u17019 : Upper (D 7) (R 7) [12,96,48,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17020 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 266 145 96 195 131 387), lower := (rows 13 98 52 266 145 96 64 128 256), losses := [] }

theorem u17020 : Upper (D 7) (R 7) [12,96,48,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17021 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 98 52 266 145 160 67 195 323), lower := (rows 13 98 52 266 145 160 64 128 256), losses := [] }

theorem u17021 : Upper (D 7) (R 7) [12,96,48,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17022 : Route 9 := (fun mask => (mask,id))

def c17022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17022 : Upper (D 7) (R 7) [12,96,48,258,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,130,1] 13 (by decide) (choices 1) [1,128] r17022 c17022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4042
  · exact u4043

def b17023 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 266 146 96 193 129 385), lower := (rows 13 98 52 266 146 96 64 128 256), losses := [] }

theorem u17023 : Upper (D 7) (R 7) [12,96,48,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17024 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 98 52 266 146 160 65 193 321), lower := (rows 13 98 52 266 146 160 64 128 256), losses := [] }

theorem u17024 : Upper (D 7) (R 7) [12,96,48,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17025 : Route 9 := (fun mask => (mask,id))

def c17025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17025 : Upper (D 7) (R 7) [12,96,48,258,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,192,1] 13 (by decide) (choices 1) [1,2,128] r17025 c17025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4044
  · exact u4045
  · exact u4046

def b17026 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 266 208 34 193 129 385), lower := (rows 13 98 52 266 208 34 64 128 256), losses := [] }

theorem u17026 : Upper (D 7) (R 7) [12,96,48,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17027 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 13 98 52 266 208 160 67 131 259), lower := (rows 13 98 52 266 208 160 64 128 256), losses := [] }

theorem u17027 : Upper (D 7) (R 7) [12,96,48,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17028 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 52 328 19 33 194 130 386), lower := (rows 13 98 52 328 19 33 64 128 256), losses := [] }

theorem u17028 : Upper (D 7) (R 7) [12,96,48,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17029 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 328 19 34 193 129 385), lower := (rows 13 98 52 328 19 34 64 128 256), losses := [] }

theorem u17029 : Upper (D 7) (R 7) [12,96,48,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17030 : Route 9 := (fun mask => (mask,id))

def c17030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17030 : Upper (D 7) (R 7) [12,96,48,320,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320,3,128] 13 (by decide) (choices 1) [1,2,128] r17030 c17030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4047
  · exact u4048
  · exact u4049

def b17031 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 392, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 98 52 328 145 33 194 130 386), lower := (rows 13 98 52 328 145 33 64 128 256), losses := [] }

theorem u17031 : Upper (D 7) (R 7) [12,96,48,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17032 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 328 145 34 195 131 387), lower := (rows 13 98 52 328 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 20 8 16 107 64 128 256), good := (rows 46 98 52 362 180 34 98 128 256) },{ target := 7, region := (rows 1 74 20 8 16 107 64 0 256), good := (rows 47 98 52 362 53 34 98 0 256) }] }

theorem u17032 : Upper (D 7) (R 7) [12,96,48,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17033 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 98 52 328 145 160 67 131 259), lower := (rows 13 98 52 328 145 160 64 128 256), losses := [] }

theorem u17033 : Upper (D 7) (R 7) [12,96,48,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17034 : Route 9 := (fun mask => (mask,id))

def c17034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17034 : Upper (D 7) (R 7) [12,96,48,320,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320,130,1] 13 (by decide) (choices 1) [1,2,128] r17034 c17034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4050
  · exact u4051
  · exact u4052

def b17035 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 328 146 34 193 129 385), lower := (rows 13 98 52 328 146 34 64 128 256), losses := [] }

theorem u17035 : Upper (D 7) (R 7) [12,96,48,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17036 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 98 52 328 146 160 67 131 259), lower := (rows 13 98 52 328 146 160 64 128 256), losses := [] }

theorem u17036 : Upper (D 7) (R 7) [12,96,48,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17037 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 392, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 98 52 392 19 33 194 194 450), lower := (rows 13 98 52 392 19 33 64 128 256), losses := [] }

theorem u17037 : Upper (D 7) (R 7) [12,96,48,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17038 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 392 19 34 193 193 449), lower := (rows 13 98 52 392 19 34 64 128 256), losses := [] }

theorem u17038 : Upper (D 7) (R 7) [12,96,48,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17039 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 392 19 96 195 131 387), lower := (rows 13 98 52 392 19 96 64 128 256), losses := [] }

theorem u17039 : Upper (D 7) (R 7) [12,96,48,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17039
end Delivery.IrregularNine14.P07
