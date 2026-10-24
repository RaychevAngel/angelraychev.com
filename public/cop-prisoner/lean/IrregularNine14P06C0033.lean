import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 136, targets := 3 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 11 22 100 140 273 33 66 224 352), lower := (rows 11 22 100 140 273 33 66 128 256), losses := [] }

theorem u1980 : Upper (D 6) (R 6) [10,20,96,132,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 100 140 273 33 96 194 322), lower := (rows 11 22 100 140 273 33 96 128 256), losses := [] }

theorem u1981 : Upper (D 6) (R 6) [10,20,96,132,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1981
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 100 140 273 34 96 193 321), lower := (rows 11 22 100 140 273 34 96 128 256), losses := [] }

theorem u1982 : Upper (D 6) (R 6) [10,20,96,132,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1982
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1983 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 22 100 168 273 33 66 196 324), lower := (rows 11 22 100 168 273 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 16 32 67 166 294), good := (rows 458 478 492 428 336 492 450 128 256) }] }

theorem u1983 : Upper (D 6) (R 6) [10,20,96,160,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1983
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 22 100 168 273 33 68 194 322), lower := (rows 11 22 100 168 273 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 16 32 111 131 259), good := (rows 462 470 108 236 464 492 68 128 256) }] }

theorem u1984 : Upper (D 6) (R 6) [10,20,96,160,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1984
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 22 100 168 273 34 65 196 324), lower := (rows 11 22 100 168 273 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 78 16 35 64 196 324), good := (rows 42 446 492 168 304 42 492 128 256) }] }

theorem u1985 : Upper (D 6) (R 6) [10,20,96,160,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1985
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 22 100 168 273 34 68 193 321), lower := (rows 11 22 100 168 273 34 68 128 256), losses := [] }

theorem u1986 : Upper (D 6) (R 6) [10,20,96,160,257,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1986
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 100 168 274 33 65 196 324), lower := (rows 11 22 100 168 274 33 65 128 256), losses := [] }

theorem u1987 : Upper (D 6) (R 6) [10,20,96,160,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1987
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 22 100 168 274 33 68 193 321), lower := (rows 11 22 100 168 274 33 68 128 256), losses := [] }

theorem u1988 : Upper (D 6) (R 6) [10,20,96,160,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1988
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 100 168 336 33 65 134 262), lower := (rows 11 22 100 168 336 33 65 128 256), losses := [] }

theorem u1989 : Upper (D 6) (R 6) [10,20,96,160,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1989
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1990 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 169, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 22 100 168 336 33 66 133 261), lower := (rows 11 22 100 168 336 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 67 128 256), good := (rows 74 86 100 172 336 100 66 128 256) }] }

theorem u1990 : Upper (D 6) (R 6) [10,20,96,160,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1990
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 169, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 100 168 336 33 68 131 259), lower := (rows 11 22 100 168 336 33 68 128 256), losses := [] }

theorem u1991 : Upper (D 6) (R 6) [10,20,96,160,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1991
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1992 : Route 9 := (fun mask => (mask,id))

def c1992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1992 : Upper (D 6) (R 6) [10,20,129,36,257,64,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,257,64,2] 13 (by decide) (choices 1) [32,64] r1992 c1992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u112
  · exact u113

def b1993 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 11 22 133 44 273 96 96 194 322), lower := (rows 11 22 133 44 273 96 96 128 256), losses := [] }

theorem u1993 : Upper (D 6) (R 6) [10,20,129,36,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1993
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,2)], upper := (rows 11 22 133 44 304 96 65 194 322), lower := (rows 11 22 133 44 304 96 65 128 256), losses := [] }

theorem u1994 : Upper (D 6) (R 6) [10,20,129,36,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1994
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 196, targets := 32 },{ cop := 1, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,2)], upper := (rows 11 22 133 44 304 96 66 193 321), lower := (rows 11 22 133 44 304 96 66 128 256), losses := [] }

theorem u1995 : Upper (D 6) (R 6) [10,20,129,36,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1995
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 22 133 104 273 34 68 224 352), lower := (rows 11 22 133 104 273 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 5 40 17 32 87 168 296), good := (rows 477 84 213 488 341 488 68 128 256) }] }

theorem u1996 : Upper (D 6) (R 6) [10,20,129,96,257,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1996
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 104 273 34 96 196 324), lower := (rows 11 22 133 104 273 34 96 128 256), losses := [] }

theorem u1997 : Upper (D 6) (R 6) [10,20,129,96,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1997
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1998 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 104 273 36 96 194 322), lower := (rows 11 22 133 104 273 36 96 128 256), losses := [] }

theorem u1998 : Upper (D 6) (R 6) [10,20,129,96,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1998
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 133 104 274 33 68 224 352), lower := (rows 11 22 133 104 274 33 68 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 17 32 70 136 264), good := (rows 474 86 214 488 338 48 70 128 256) }] }

theorem u1999 : Upper (D 6) (R 6) [10,20,129,96,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1999
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 104 274 33 96 196 324), lower := (rows 11 22 133 104 274 33 96 128 256), losses := [] }

theorem u2000 : Upper (D 6) (R 6) [10,20,129,96,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2000
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2001 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 104 274 36 96 193 321), lower := (rows 11 22 133 104 274 36 96 128 256), losses := [] }

theorem u2001 : Upper (D 6) (R 6) [10,20,129,96,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2001
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2002 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(2,5),(3,2)], upper := (rows 11 22 133 104 304 33 66 196 324), lower := (rows 11 22 133 104 304 33 66 128 256), losses := [] }

theorem u2002 : Upper (D 6) (R 6) [10,20,129,96,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2002
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2003 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,0)], upper := (rows 11 22 133 104 304 33 68 194 322), lower := (rows 11 22 133 104 304 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 48 32 70 131 259), good := (rows 458 470 452 120 304 432 68 128 256) }] }

theorem u2003 : Upper (D 6) (R 6) [10,20,129,96,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2003
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(2,5)], upper := (rows 11 22 133 104 304 34 65 196 324), lower := (rows 11 22 133 104 304 34 65 128 256), losses := [] }

theorem u2004 : Upper (D 6) (R 6) [10,20,129,96,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2004
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 104, targets := 1 }], pairs := [(2,1),(2,5),(3,0)], upper := (rows 11 22 133 104 304 34 68 193 321), lower := (rows 11 22 133 104 304 34 68 128 256), losses := [] }

theorem u2005 : Upper (D 6) (R 6) [10,20,129,96,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2005
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(3,2)], upper := (rows 11 22 133 104 304 36 65 194 322), lower := (rows 11 22 133 104 304 36 65 128 256), losses := [{ target := 2, region := (rows 1 2 0 40 16 32 69 131 259), good := (rows 459 466 449 104 312 104 449 128 256) }] }

theorem u2006 : Upper (D 6) (R 6) [10,20,129,96,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2006
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2007 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 1, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 22 133 104 304 36 66 193 321), lower := (rows 11 22 133 104 304 36 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 16 38 64 128 256), good := (rows 41 52 165 104 304 36 104 128 256) }] }

theorem u2007 : Upper (D 6) (R 6) [10,20,129,96,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2007
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2008 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 22 133 265 112 34 68 224 352), lower := (rows 11 22 133 265 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 48 32 70 176 304), good := (rows 73 468 197 265 496 496 68 128 256) }] }

theorem u2008 : Upper (D 6) (R 6) [10,20,129,257,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2008
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 265 112 34 96 196 324), lower := (rows 11 22 133 265 112 34 96 128 256), losses := [] }

theorem u2009 : Upper (D 6) (R 6) [10,20,129,257,96,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2009
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 265 112 36 96 194 322), lower := (rows 11 22 133 265 112 36 96 128 256), losses := [] }

theorem u2010 : Upper (D 6) (R 6) [10,20,129,257,96,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2010
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2011 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 1, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 11 22 133 268 49 96 66 224 352), lower := (rows 11 22 133 268 49 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 96 64 224 352), good := (rows 9 28 133 268 445 480 480 128 256) }] }

theorem u2011 : Upper (D 6) (R 6) [10,20,129,260,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2011
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2012 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 112, targets := 4 },{ cop := 1, region := 360, targets := 1 }], pairs := [(3,0),(4,1),(4,2)], upper := (rows 11 22 133 268 49 96 96 194 322), lower := (rows 11 22 133 268 49 96 96 128 256), losses := [] }

theorem u2012 : Upper (D 6) (R 6) [10,20,129,260,33,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2012
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 11 22 133 268 112 33 66 224 352), lower := (rows 11 22 133 268 112 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 48 32 67 176 304), good := (rows 74 478 196 268 496 496 74 128 256) }] }

theorem u2013 : Upper (D 6) (R 6) [10,20,129,260,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2013
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 268 112 33 96 194 322), lower := (rows 11 22 133 268 112 33 96 128 256), losses := [] }

theorem u2014 : Upper (D 6) (R 6) [10,20,129,260,96,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2014
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 133 268 112 34 96 193 321), lower := (rows 11 22 133 268 112 34 96 128 256), losses := [] }

theorem u2015 : Upper (D 6) (R 6) [10,20,129,260,96,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2015
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 1, region := 360, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 22 133 296 81 34 68 224 352), lower := (rows 11 22 133 296 81 34 68 128 256), losses := [] }

theorem u2016 : Upper (D 6) (R 6) [10,20,129,288,65,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2016
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 134, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,5),(2,5),(4,2)], upper := (rows 11 22 133 296 81 34 96 196 324), lower := (rows 11 22 133 296 81 34 96 128 256), losses := [] }

theorem u2017 : Upper (D 6) (R 6) [10,20,129,288,65,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2017
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2018 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 22 133 296 81 36 66 224 352), lower := (rows 11 22 133 296 81 36 66 128 256), losses := [] }

theorem u2018 : Upper (D 6) (R 6) [10,20,129,288,65,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2018
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2019 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 134, targets := 32 },{ cop := 1, region := 360, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 11 22 133 296 81 36 96 194 322), lower := (rows 11 22 133 296 81 36 96 128 256), losses := [] }

theorem u2019 : Upper (D 6) (R 6) [10,20,129,288,65,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2019
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 4, region := 164, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 22 133 296 81 96 66 164 292), lower := (rows 11 22 133 296 81 96 66 128 256), losses := [] }

theorem u2020 : Upper (D 6) (R 6) [10,20,129,288,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2020
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 1, region := 360, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 22 133 296 81 96 68 162 290), lower := (rows 11 22 133 296 81 96 68 128 256), losses := [] }

theorem u2021 : Upper (D 6) (R 6) [10,20,129,288,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2021
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 134, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 22 133 296 81 96 96 134 262), lower := (rows 11 22 133 296 81 96 96 128 256), losses := [] }

theorem u2022 : Upper (D 6) (R 6) [10,20,129,288,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2022
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 133 296 82 33 68 224 352), lower := (rows 11 22 133 296 82 33 68 128 256), losses := [] }

theorem u2023 : Upper (D 6) (R 6) [10,20,129,288,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2023
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 133 296 82 33 96 196 324), lower := (rows 11 22 133 296 82 33 96 128 256), losses := [] }

theorem u2024 : Upper (D 6) (R 6) [10,20,129,288,66,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2024
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 133 296 82 36 65 224 352), lower := (rows 11 22 133 296 82 36 65 128 256), losses := [] }

theorem u2025 : Upper (D 6) (R 6) [10,20,129,288,66,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2025
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 133 296 82 36 96 193 321), lower := (rows 11 22 133 296 82 36 96 128 256), losses := [] }

theorem u2026 : Upper (D 6) (R 6) [10,20,129,288,66,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2026
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2027 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 82, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 22 133 296 82 96 65 164 292), lower := (rows 11 22 133 296 82 96 65 128 256), losses := [] }

theorem u2027 : Upper (D 6) (R 6) [10,20,129,288,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2028 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 133 296 82 96 68 161 289), lower := (rows 11 22 133 296 82 96 68 128 256), losses := [] }

theorem u2028 : Upper (D 6) (R 6) [10,20,129,288,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2029 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 22 133 296 82 96 96 133 261), lower := (rows 11 22 133 296 82 96 96 128 256), losses := [] }

theorem u2029 : Upper (D 6) (R 6) [10,20,129,288,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2029
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 22 133 296 112 33 66 196 324), lower := (rows 11 22 133 296 112 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 48 32 67 134 262), good := (rows 458 470 452 312 112 112 450 128 256) }] }

theorem u2030 : Upper (D 6) (R 6) [10,20,129,288,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2030
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 112, targets := 2 }], pairs := [(2,5),(3,0),(4,1)], upper := (rows 11 22 133 296 112 33 68 194 322), lower := (rows 11 22 133 296 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 70 131 259), good := (rows 458 470 452 296 120 424 68 128 256) }] }

theorem u2031 : Upper (D 6) (R 6) [10,20,129,288,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2031
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(2,5),(4,2)], upper := (rows 11 22 133 296 112 34 65 196 324), lower := (rows 11 22 133 296 112 34 65 128 256), losses := [] }

theorem u2032 : Upper (D 6) (R 6) [10,20,129,288,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2032
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 22 133 296 112 34 68 193 321), lower := (rows 11 22 133 296 112 34 68 128 256), losses := [] }

theorem u2033 : Upper (D 6) (R 6) [10,20,129,288,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2033
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 112, targets := 2 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 22 133 296 112 36 65 194 322), lower := (rows 11 22 133 296 112 36 65 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 48 32 69 131 259), good := (rows 459 466 449 312 112 112 449 128 256) }] }

theorem u2034 : Upper (D 6) (R 6) [10,20,129,288,96,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2034
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 22 133 296 112 36 66 193 321), lower := (rows 11 22 133 296 112 36 66 128 256), losses := [] }

theorem u2035 : Upper (D 6) (R 6) [10,20,129,288,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2035
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 22 134 41 112 288 65 196 324), lower := (rows 11 22 134 41 112 288 65 128 256), losses := [] }

theorem u2036 : Upper (D 6) (R 6) [10,20,130,33,96,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2036
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2037 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1)], upper := (rows 11 22 134 41 112 288 68 193 321), lower := (rows 11 22 134 41 112 288 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 297 70 129 257), good := (rows 505 84 196 441 112 288 68 128 288) }] }

theorem u2037 : Upper (D 6) (R 6) [10,20,130,33,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2037
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2038 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 134 41 304 96 65 196 324), lower := (rows 11 22 134 41 304 96 65 128 256), losses := [] }

theorem u2038 : Upper (D 6) (R 6) [10,20,130,33,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2038
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 22 134 41 304 96 68 193 321), lower := (rows 11 22 134 41 304 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 25 103 70 129 257), good := (rows 505 116 228 441 304 96 100 128 256) }] }

theorem u2039 : Upper (D 6) (R 6) [10,20,130,33,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b2039
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P06
