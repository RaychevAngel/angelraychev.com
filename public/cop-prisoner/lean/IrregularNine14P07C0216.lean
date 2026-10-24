import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0026

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12960 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 137 176 48 322 450 322), lower := (rows 7 42 69 137 176 48 64 128 256), losses := [] }

theorem u12960 : Upper (D 7) (R 7) [6,40,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12960 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12961 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 137 176 96 338 402 274), lower := (rows 7 42 69 137 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 13 18 32 0 131 259), good := (rows 415 442 397 393 176 32 0 128 256) }] }

theorem u12961 : Upper (D 7) (R 7) [6,40,65,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12962 : Route 9 := (fun mask => (mask,id))

def c12962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12962 : Upper (D 7) (R 7) [6,40,65,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,160,256] 13 (by decide) (choices 1) [2,16] r12962 c12962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1569
  · exact u1570

def b12963 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 137 208 34 368 432 304), lower := (rows 7 42 69 137 208 34 64 128 256), losses := [] }

theorem u12963 : Upper (D 7) (R 7) [6,40,65,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12964 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 42 69 137 208 48 354 418 290), lower := (rows 7 42 69 137 208 48 64 128 256), losses := [] }

theorem u12964 : Upper (D 7) (R 7) [6,40,65,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12964 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12965 : Route 9 := (fun mask => (mask,id))

def c12965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12965 : Upper (D 7) (R 7) [6,40,65,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,192,256] 13 (by decide) (choices 1) [2,16,32] r12965 c12965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1571
  · exact u1572
  · exact u1573

def b12966 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 69 137 274 48 224 224 480), lower := (rows 7 42 69 137 274 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 16 48 114 178 306), good := (rows 461 488 77 141 496 496 64 128 256) }] }

theorem u12966 : Upper (D 7) (R 7) [6,40,65,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12966 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12967 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 137 274 96 240 176 432), lower := (rows 7 42 69 137 274 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 19 32 0 130 258), good := (rows 415 442 29 153 402 32 0 128 256) }] }

theorem u12967 : Upper (D 7) (R 7) [6,40,65,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12968 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 137 274 160 112 240 368), lower := (rows 7 42 69 137 274 160 64 128 256), losses := [] }

theorem u12968 : Upper (D 7) (R 7) [6,40,65,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12969 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 137 304 34 208 208 464), lower := (rows 7 42 69 137 304 34 64 128 256), losses := [] }

theorem u12969 : Upper (D 7) (R 7) [6,40,65,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12970 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 42 69 137 304 48 194 194 450), lower := (rows 7 42 69 137 304 48 64 128 256), losses := [] }

theorem u12970 : Upper (D 7) (R 7) [6,40,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12970 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12971 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 137 304 96 210 146 402), lower := (rows 7 42 69 137 304 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 13 18 32 0 131 259), good := (rows 415 442 397 393 304 32 0 128 256) }] }

theorem u12971 : Upper (D 7) (R 7) [6,40,65,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12972 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 137 304 160 82 210 338), lower := (rows 7 42 69 137 304 160 64 128 256), losses := [] }

theorem u12972 : Upper (D 7) (R 7) [6,40,65,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12973 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 137 336 34 240 176 432), lower := (rows 7 42 69 137 336 34 64 128 256), losses := [] }

theorem u12973 : Upper (D 7) (R 7) [6,40,65,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12974 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(3,6),(4,0)], upper := (rows 7 42 69 137 336 48 226 162 418), lower := (rows 7 42 69 137 336 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 48 0 130 258), good := (rows 399 426 13 137 304 48 0 128 256) }] }

theorem u12974 : Upper (D 7) (R 7) [6,40,65,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12974 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12975 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 137 336 160 114 178 306), lower := (rows 7 42 69 137 336 160 64 128 256), losses := [] }

theorem u12975 : Upper (D 7) (R 7) [6,40,65,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12976 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 137 400 34 112 240 368), lower := (rows 7 42 69 137 400 34 64 128 256), losses := [] }

theorem u12976 : Upper (D 7) (R 7) [6,40,65,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12977 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 42 69 137 400 48 98 226 354), lower := (rows 7 42 69 137 400 48 64 128 256), losses := [] }

theorem u12977 : Upper (D 7) (R 7) [6,40,65,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12977 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12978 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 137 400 96 114 178 306), lower := (rows 7 42 69 137 400 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 19 32 0 130 258), good := (rows 415 442 29 153 400 32 0 128 256) }] }

theorem u12978 : Upper (D 7) (R 7) [6,40,65,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12979 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 138 112 33 464 400 400), lower := (rows 7 42 69 138 112 33 64 128 256), losses := [] }

theorem u12979 : Upper (D 7) (R 7) [6,40,65,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12980 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 138 112 48 449 385 385), lower := (rows 7 42 69 138 112 48 64 128 256), losses := [] }

theorem u12980 : Upper (D 7) (R 7) [6,40,65,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12980 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12981 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 138 112 160 337 401 273), lower := (rows 7 42 69 138 112 160 64 128 256), losses := [] }

theorem u12981 : Upper (D 7) (R 7) [6,40,65,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12982 : Route 9 := (fun mask => (mask,id))

def c12982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12982 : Upper (D 7) (R 7) [6,40,65,130,96,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,96,256] 13 (by decide) (choices 1) [1,16,128] r12982 c12982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1574
  · exact u1575
  · exact u1576

def b12983 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 138 208 33 368 432 304), lower := (rows 7 42 69 138 208 33 64 128 256), losses := [] }

theorem u12983 : Upper (D 7) (R 7) [6,40,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12984 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 69 138 208 48 353 417 289), lower := (rows 7 42 69 138 208 48 64 128 256), losses := [] }

theorem u12984 : Upper (D 7) (R 7) [6,40,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12984 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12985 : Route 9 := (fun mask => (mask,id))

def c12985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12985 : Upper (D 7) (R 7) [6,40,65,130,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,192,256] 13 (by decide) (choices 1) [1,16,32] r12985 c12985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1577
  · exact u1578
  · exact u1579

def b12986 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 138 304 33 208 208 464), lower := (rows 7 42 69 138 304 33 64 128 256), losses := [] }

theorem u12986 : Upper (D 7) (R 7) [6,40,65,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12987 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 42 69 138 304 48 193 193 449), lower := (rows 7 42 69 138 304 48 64 128 256), losses := [] }

theorem u12987 : Upper (D 7) (R 7) [6,40,65,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12987 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12988 : Route 9 := (fun mask => (mask,id))

def c12988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12988 : Upper (D 7) (R 7) [6,40,65,130,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,288,64] 13 (by decide) (choices 1) [1,16,128] r12988 c12988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1580
  · exact u1581
  · exact u1582

def b12989 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 138 304 160 81 209 337), lower := (rows 7 42 69 138 304 160 64 128 256), losses := [] }

theorem u12989 : Upper (D 7) (R 7) [6,40,65,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12990 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 138 336 33 240 176 432), lower := (rows 7 42 69 138 336 33 64 128 256), losses := [] }

theorem u12990 : Upper (D 7) (R 7) [6,40,65,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12991 : Route 9 := (fun mask => (mask,id))

def c12991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12991 : Upper (D 7) (R 7) [6,40,65,130,320,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,320,16] 13 (by decide) (choices 1) [1,32,128] r12991 c12991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1583
  · exact u1584
  · exact u1585

def b12992 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 138 336 160 113 177 305), lower := (rows 7 42 69 138 336 160 64 128 256), losses := [] }

theorem u12992 : Upper (D 7) (R 7) [6,40,65,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12993 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 138 400 33 112 240 368), lower := (rows 7 42 69 138 400 33 64 128 256), losses := [] }

theorem u12993 : Upper (D 7) (R 7) [6,40,65,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12994 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 69 138 400 48 97 225 353), lower := (rows 7 42 69 138 400 48 64 128 256), losses := [] }

theorem u12994 : Upper (D 7) (R 7) [6,40,65,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12994 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12995 : Route 9 := (fun mask => (mask,id))

def c12995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12995 : Upper (D 7) (R 7) [6,40,65,130,384,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,384,64] 13 (by decide) (choices 1) [1,16,32] r12995 c12995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1586
  · exact u1587
  · exact u1588

def b12996 : PairBound 9 := { available := 386, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 42 69 152 112 33 450 386 386), lower := (rows 7 42 69 152 112 33 64 128 256), losses := [] }

theorem u12996 : Upper (D 7) (R 7) [6,40,65,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12997 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 69 152 112 34 449 385 385), lower := (rows 7 42 69 152 112 34 64 128 256), losses := [] }

theorem u12997 : Upper (D 7) (R 7) [6,40,65,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12998 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 7 42 69 152 112 160 323 387 259), lower := (rows 7 42 69 152 112 160 64 128 256), losses := [] }

theorem u12998 : Upper (D 7) (R 7) [6,40,65,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12999 : Route 9 := (fun mask => (mask,id))

def c12999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12999 : Upper (D 7) (R 7) [6,40,65,144,96,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,96,256] 13 (by decide) (choices 1) [1,2,128] r12999 c12999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1589
  · exact u1590
  · exact u1591

def b13000 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 69 152 273 34 224 224 480), lower := (rows 7 42 69 152 273 34 64 128 256), losses := [] }

theorem u13000 : Upper (D 7) (R 7) [6,40,65,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13001 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(3,6),(4,6)], upper := (rows 7 42 69 152 273 96 226 162 418), lower := (rows 7 42 69 152 273 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 32 0 130 258), good := (rows 415 426 29 152 281 32 0 128 256) }] }

theorem u13001 : Upper (D 7) (R 7) [6,40,65,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13002 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 152 273 160 98 226 354), lower := (rows 7 42 69 152 273 160 64 128 256), losses := [] }

theorem u13002 : Upper (D 7) (R 7) [6,40,65,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13003 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 152 274 33 224 224 480), lower := (rows 7 42 69 152 274 33 64 128 256), losses := [] }

theorem u13003 : Upper (D 7) (R 7) [6,40,65,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13004 : Route 9 := (fun mask => (mask,id))

def c13004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13004 : Upper (D 7) (R 7) [6,40,65,144,258,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,258,64] 13 (by decide) (choices 1) [1,32,128] r13004 c13004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1592
  · exact u1593
  · exact u1594

def b13005 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 152 274 160 97 225 353), lower := (rows 7 42 69 152 274 160 64 128 256), losses := [] }

theorem u13005 : Upper (D 7) (R 7) [6,40,65,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13006 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 42 69 152 304 33 194 194 450), lower := (rows 7 42 69 152 304 33 64 128 256), losses := [] }

theorem u13006 : Upper (D 7) (R 7) [6,40,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13007 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 69 152 304 34 193 193 449), lower := (rows 7 42 69 152 304 34 64 128 256), losses := [] }

theorem u13007 : Upper (D 7) (R 7) [6,40,65,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13008 : Route 9 := (fun mask => (mask,id))

def c13008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13008 : Upper (D 7) (R 7) [6,40,65,144,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,288,64] 13 (by decide) (choices 1) [1,2,128] r13008 c13008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1595
  · exact u1596
  · exact u1597

def b13009 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 7 42 69 152 304 160 67 195 323), lower := (rows 7 42 69 152 304 160 64 128 256), losses := [] }

theorem u13009 : Upper (D 7) (R 7) [6,40,65,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13010 : Route 9 := (fun mask => (mask,id))

def c13010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13010 : Upper (D 7) (R 7) [6,40,65,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,320,1] 13 (by decide) (choices 1) [2,32,128] r13010 c13010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1598
  · exact u1599
  · exact u1600

def r13011 : Route 9 := (fun mask => (mask,id))

def c13011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13011 : Upper (D 7) (R 7) [6,40,65,144,320,2] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,320,2] 13 (by decide) (choices 1) [1,32,128] r13011 c13011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1601
  · exact u1602
  · exact u1603

def b13012 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 152 336 160 99 163 291), lower := (rows 7 42 69 152 336 160 64 128 256), losses := [] }

theorem u13012 : Upper (D 7) (R 7) [6,40,65,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13013 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 69 200 49 34 464 400 400), lower := (rows 7 42 69 200 49 34 64 128 256), losses := [] }

theorem u13013 : Upper (D 7) (R 7) [6,40,65,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13014 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 200 49 48 450 386 386), lower := (rows 7 42 69 200 49 48 64 128 256), losses := [] }

theorem u13014 : Upper (D 7) (R 7) [6,40,65,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13014 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13015 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 200 49 160 338 402 274), lower := (rows 7 42 69 200 49 160 64 128 256), losses := [] }

theorem u13015 : Upper (D 7) (R 7) [6,40,65,192,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13016 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 202, targets := 1 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 7 42 69 200 49 288 210 146 402), lower := (rows 7 42 69 200 49 288 64 128 256), losses := [] }

theorem u13016 : Upper (D 7) (R 7) [6,40,65,192,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13016 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13017 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 145 34 368 432 304), lower := (rows 7 42 69 200 145 34 64 128 256), losses := [] }

theorem u13017 : Upper (D 7) (R 7) [6,40,65,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13018 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 42 69 200 145 48 354 418 290), lower := (rows 7 42 69 200 145 48 64 128 256), losses := [] }

theorem u13018 : Upper (D 7) (R 7) [6,40,65,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13018 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13019 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 7 42 69 200 145 288 114 178 306), lower := (rows 7 42 69 200 145 288 64 128 256), losses := [] }

theorem u13019 : Upper (D 7) (R 7) [6,40,65,192,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13019 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13019
end Delivery.IrregularNine14.P07
