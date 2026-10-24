import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0004

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1980 : Route 9 := (fun mask => (mask,id))

def c1980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1980 : Upper (D 5) (R 5) [6,17,192,258,40,4] 13 := by
  apply FastRouting.sound _ _ [6,17,192,258,40,4] 13 (by decide) (choices 1) [1,8,32] r1980 c1980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u259
  · exact u260
  · exact u261

def b1981 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 266 56 40 101 165 293), lower := (rows 7 19 196 266 56 40 64 128 256), losses := [] }

theorem u1981 : Upper (D 5) (R 5) [6,17,192,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1982 : Route 9 := (fun mask => (mask,id))

def c1982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1982 : Upper (D 5) (R 5) [6,17,192,260,40,1] 13 := by
  apply FastRouting.sound _ _ [6,17,192,260,40,1] 13 (by decide) (choices 1) [2,8,32] r1982 c1982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u262
  · exact u263
  · exact u264

def r1983 : Route 9 := (fun mask => (mask,id))

def c1983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1983 : Upper (D 5) (R 5) [6,17,192,260,40,2] 13 := by
  apply FastRouting.sound _ _ [6,17,192,260,40,2] 13 (by decide) (choices 1) [1,8,32] r1983 c1983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u265
  · exact u266
  · exact u267

def b1984 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 268 56 40 99 163 291), lower := (rows 7 19 196 268 56 40 64 128 256), losses := [] }

theorem u1984 : Upper (D 5) (R 5) [6,17,192,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 37 73 176 34 332 396 268), lower := (rows 7 26 37 73 176 34 64 128 256), losses := [] }

theorem u1985 : Upper (D 5) (R 5) [6,24,33,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 73 176 36 330 394 266), lower := (rows 7 26 37 73 176 36 64 128 256), losses := [] }

theorem u1986 : Upper (D 5) (R 5) [6,24,33,65,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 328, targets := 32 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1),(3,5)], upper := (rows 7 26 37 73 176 40 326 390 262), lower := (rows 7 26 37 73 176 40 64 128 256), losses := [] }

theorem u1987 : Upper (D 5) (R 5) [6,24,33,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 37 73 176 288 78 142 270), lower := (rows 7 26 37 73 176 288 64 128 256), losses := [] }

theorem u1988 : Upper (D 5) (R 5) [6,24,33,65,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 73 400 34 108 172 300), lower := (rows 7 26 37 73 400 34 64 128 256), losses := [] }

theorem u1989 : Upper (D 5) (R 5) [6,24,33,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1990 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 73 400 36 106 170 298), lower := (rows 7 26 37 73 400 36 64 128 256), losses := [] }

theorem u1990 : Upper (D 5) (R 5) [6,24,33,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(1,0),(2,1)], upper := (rows 7 26 37 73 400 40 102 166 294), lower := (rows 7 26 37 73 400 40 64 128 256), losses := [{ target := 0, region := (rows 0 42 4 8 29 42 69 133 261), good := (rows 502 58 502 506 400 58 64 128 256) }] }

theorem u1991 : Upper (D 5) (R 5) [6,24,33,65,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 74 176 33 332 396 268), lower := (rows 7 26 37 74 176 33 64 128 256), losses := [] }

theorem u1992 : Upper (D 5) (R 5) [6,24,33,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1992
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 74 176 36 329 393 265), lower := (rows 7 26 37 74 176 36 64 128 256), losses := [] }

theorem u1993 : Upper (D 5) (R 5) [6,24,33,66,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 400, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 37 74 176 40 325 389 261), lower := (rows 7 26 37 74 176 40 64 128 256), losses := [] }

theorem u1994 : Upper (D 5) (R 5) [6,24,33,66,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1994
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 37 74 176 288 77 141 269), lower := (rows 7 26 37 74 176 288 64 128 256), losses := [] }

theorem u1995 : Upper (D 5) (R 5) [6,24,33,66,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 74 400 33 108 172 300), lower := (rows 7 26 37 74 400 33 64 128 256), losses := [] }

theorem u1996 : Upper (D 5) (R 5) [6,24,33,66,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 74 400 36 105 169 297), lower := (rows 7 26 37 74 400 36 64 128 256), losses := [] }

theorem u1997 : Upper (D 5) (R 5) [6,24,33,66,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1997
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1998 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 400, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 37 74 400 40 101 165 293), lower := (rows 7 26 37 74 400 40 64 128 256), losses := [] }

theorem u1998 : Upper (D 5) (R 5) [6,24,33,66,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1998
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 76 176 33 330 394 266), lower := (rows 7 26 37 76 176 33 64 128 256), losses := [] }

theorem u1999 : Upper (D 5) (R 5) [6,24,33,68,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1999
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 37 76 176 34 329 393 265), lower := (rows 7 26 37 76 176 34 64 128 256), losses := [] }

theorem u2000 : Upper (D 5) (R 5) [6,24,33,68,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2000
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2001 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5)], upper := (rows 7 26 37 76 176 40 323 387 259), lower := (rows 7 26 37 76 176 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 42 64 128 256), good := (rows 37 56 37 108 176 40 64 128 256) }] }

theorem u2001 : Upper (D 5) (R 5) [6,24,33,68,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2001
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2002 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 37 76 176 288 75 139 267), lower := (rows 7 26 37 76 176 288 64 128 256), losses := [] }

theorem u2002 : Upper (D 5) (R 5) [6,24,33,68,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2003 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 76 400 33 106 170 298), lower := (rows 7 26 37 76 400 33 64 128 256), losses := [] }

theorem u2003 : Upper (D 5) (R 5) [6,24,33,68,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2003
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 76 400 34 105 169 297), lower := (rows 7 26 37 76 400 34 64 128 256), losses := [] }

theorem u2004 : Upper (D 5) (R 5) [6,24,33,68,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 35, camps := [], pairs := [(1,2),(2,1)], upper := (rows 7 26 37 76 400 40 99 163 291), lower := (rows 7 26 37 76 400 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 42 64 128 256), good := (rows 37 56 37 108 400 40 64 128 256) },{ target := 2, region := (rows 1 42 0 8 29 42 69 133 261), good := (rows 499 58 499 506 400 58 64 128 256) }] }

theorem u2005 : Upper (D 5) (R 5) [6,24,33,68,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 104 400 33 78 142 270), lower := (rows 7 26 37 104 400 33 64 128 256), losses := [] }

theorem u2006 : Upper (D 5) (R 5) [6,24,33,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2007 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 37, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 104 400 34 77 141 269), lower := (rows 7 26 37 104 400 34 64 128 256), losses := [] }

theorem u2007 : Upper (D 5) (R 5) [6,24,33,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2008 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 104 400 36 75 139 267), lower := (rows 7 26 37 104 400 36 64 128 256), losses := [] }

theorem u2008 : Upper (D 5) (R 5) [6,24,33,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2008
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 26 37 104 400 40 71 135 263), lower := (rows 7 26 37 104 400 40 64 128 256), losses := [] }

theorem u2009 : Upper (D 5) (R 5) [6,24,33,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2009
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 200 304 33 78 142 270), lower := (rows 7 26 37 200 304 33 64 128 256), losses := [] }

theorem u2010 : Upper (D 5) (R 5) [6,24,33,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2011 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 37 200 304 34 77 141 269), lower := (rows 7 26 37 200 304 34 64 128 256), losses := [] }

theorem u2011 : Upper (D 5) (R 5) [6,24,33,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2012 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 200 304 36 75 139 267), lower := (rows 7 26 37 200 304 36 64 128 256), losses := [] }

theorem u2012 : Upper (D 5) (R 5) [6,24,33,192,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5)], upper := (rows 7 26 37 200 304 40 71 135 263), lower := (rows 7 26 37 200 304 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 42 64 128 256), good := (rows 37 56 37 232 304 40 64 128 256) }] }

theorem u2013 : Upper (D 5) (R 5) [6,24,33,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 26 44 73 400 33 102 166 294), lower := (rows 7 26 44 73 400 33 64 128 256), losses := [] }

theorem u2014 : Upper (D 5) (R 5) [6,24,40,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2014
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 44 73 400 34 101 165 293), lower := (rows 7 26 44 73 400 34 64 128 256), losses := [] }

theorem u2015 : Upper (D 5) (R 5) [6,24,40,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2015
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 44 73 400 36 99 163 291), lower := (rows 7 26 44 73 400 36 64 128 256), losses := [] }

theorem u2016 : Upper (D 5) (R 5) [6,24,40,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(2,1),(4,3)], upper := (rows 7 26 44 200 273 33 102 166 294), lower := (rows 7 26 44 200 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 49 64 128 256), good := (rows 37 60 44 200 305 33 64 128 256) }] }

theorem u2017 : Upper (D 5) (R 5) [6,24,40,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2018 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 44 200 273 34 101 165 293), lower := (rows 7 26 44 200 273 34 64 128 256), losses := [] }

theorem u2018 : Upper (D 5) (R 5) [6,24,40,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2019 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 44 200 273 36 99 163 291), lower := (rows 7 26 44 200 273 36 64 128 256), losses := [] }

theorem u2019 : Upper (D 5) (R 5) [6,24,40,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2019
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 69 41 400 34 108 172 300), lower := (rows 7 26 69 41 400 34 64 128 256), losses := [] }

theorem u2020 : Upper (D 5) (R 5) [6,24,65,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 41 400 36 106 170 298), lower := (rows 7 26 69 41 400 36 64 128 256), losses := [] }

theorem u2021 : Upper (D 5) (R 5) [6,24,65,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 26 69 41 400 40 102 166 294), lower := (rows 7 26 69 41 400 40 64 128 256), losses := [] }

theorem u2022 : Upper (D 5) (R 5) [6,24,65,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2022
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2023 : Route 9 := (fun mask => (mask,id))

def c2023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2023 : Upper (D 5) (R 5) [6,24,65,34,384,1] 13 := by
  apply FastRouting.sound _ _ [6,24,65,34,384,1] 13 (by decide) (choices 1) [4,8,32] r2023 c2023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u268
  · exact u269
  · exact u270

def r2024 : Route 9 := (fun mask => (mask,id))

def c2024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2024 : Upper (D 5) (R 5) [6,24,65,34,384,4] 13 := by
  apply FastRouting.sound _ _ [6,24,65,34,384,4] 13 (by decide) (choices 1) [1,8,32] r2024 c2024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u271
  · exact u272
  · exact u273

def b2025 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 400 40 101 165 293), lower := (rows 7 26 69 42 400 40 64 128 256), losses := [] }

theorem u2025 : Upper (D 5) (R 5) [6,24,65,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2025
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 44 400 33 106 170 298), lower := (rows 7 26 69 44 400 33 64 128 256), losses := [] }

theorem u2026 : Upper (D 5) (R 5) [6,24,65,36,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2026
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2027 : Route 9 := (fun mask => (mask,id))

def c2027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2027 : Upper (D 5) (R 5) [6,24,65,36,384,2] 13 := by
  apply FastRouting.sound _ _ [6,24,65,36,384,2] 13 (by decide) (choices 1) [1,8,32] r2027 c2027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u274
  · exact u275
  · exact u276

def b2028 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 26 69 44 400 40 99 163 291), lower := (rows 7 26 69 44 400 40 64 128 256), losses := [] }

theorem u2028 : Upper (D 5) (R 5) [6,24,65,36,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2029 : Route 9 := (fun mask => (mask,id))

def c2029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2029 : Upper (D 5) (R 5) [6,24,65,129,288,2] 13 := by
  apply FastRouting.sound _ _ [6,24,65,129,288,2] 13 (by decide) (choices 1) [4,8,32] r2029 c2029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u277
  · exact u278
  · exact u279

def b2030 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(4,0)], upper := (rows 7 26 69 137 304 36 106 170 298), lower := (rows 7 26 69 137 304 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 37 72 136 264), good := (rows 38 474 100 506 304 36 64 128 256) }] }

theorem u2030 : Upper (D 5) (R 5) [6,24,65,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 38, camps := [], pairs := [(1,0),(4,0)], upper := (rows 7 26 69 137 304 40 102 166 294), lower := (rows 7 26 69 137 304 40 64 128 256), losses := [{ target := 0, region := (rows 0 42 4 8 25 42 65 129 257), good := (rows 502 58 468 506 306 58 64 128 256) }] }

theorem u2031 : Upper (D 5) (R 5) [6,24,65,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2032 : Route 9 := (fun mask => (mask,id))

def c2032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2032 : Upper (D 5) (R 5) [6,24,65,130,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,65,130,288,1] 13 (by decide) (choices 1) [4,8,32] r2032 c2032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u280
  · exact u281
  · exact u282

def r2033 : Route 9 := (fun mask => (mask,id))

def c2033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2033 : Upper (D 5) (R 5) [6,24,65,130,288,4] 13 := by
  apply FastRouting.sound _ _ [6,24,65,130,288,4] 13 (by decide) (choices 1) [1,8,32] r2033 c2033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u283
  · exact u284
  · exact u285

def b2034 : PairBound 9 := { available := 37, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 26 69 138 304 40 101 165 293), lower := (rows 7 26 69 138 304 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 56 469 168 304 40 64 128 256) }] }

theorem u2034 : Upper (D 5) (R 5) [6,24,65,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 42, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 26 69 140 304 33 106 170 298), lower := (rows 7 26 69 140 304 33 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 24 37 72 136 264), good := (rows 35 474 97 506 304 33 64 128 256) }] }

theorem u2035 : Upper (D 5) (R 5) [6,24,65,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2036 : Route 9 := (fun mask => (mask,id))

def c2036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2036 : Upper (D 5) (R 5) [6,24,65,132,288,2] 13 := by
  apply FastRouting.sound _ _ [6,24,65,132,288,2] 13 (by decide) (choices 1) [1,8,32] r2036 c2036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u286
  · exact u287
  · exact u288

def r2037 : Route 9 := (fun mask => (mask,id))

def c2037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2037 : Upper (D 5) (R 5) [6,24,65,132,288,8] 13 := by
  apply FastRouting.sound _ _ [6,24,65,132,288,8] 13 (by decide) (choices 1) [1,2,32] r2037 c2037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u289
  · exact u290
  · exact u291

def b2038 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 26 76 41 400 33 102 166 294), lower := (rows 7 26 76 41 400 33 64 128 256), losses := [] }

theorem u2038 : Upper (D 5) (R 5) [6,24,72,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 76 41 400 34 101 165 293), lower := (rows 7 26 76 41 400 34 64 128 256), losses := [] }

theorem u2039 : Upper (D 5) (R 5) [6,24,72,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2039
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P05
