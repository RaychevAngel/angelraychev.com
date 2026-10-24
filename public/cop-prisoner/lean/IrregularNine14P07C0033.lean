import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0001

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 276 200 82 33 96 129 385), lower := (rows 7 42 276 200 82 33 96 128 256), losses := [] }

theorem u1980 : Upper (D 7) (R 7) [6,40,272,192,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 276 200 82 33 192 161 289), lower := (rows 7 42 276 200 82 33 192 128 256), losses := [] }

theorem u1981 : Upper (D 7) (R 7) [6,40,272,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 276 200 112 33 65 130 386), lower := (rows 7 42 276 200 112 33 65 128 256), losses := [] }

theorem u1982 : Upper (D 7) (R 7) [6,40,272,192,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1983 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,0),(4,7)], upper := (rows 7 42 276 200 112 33 66 129 385), lower := (rows 7 42 276 200 112 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 33 64 161 289), good := (rows 421 424 284 200 508 417 64 128 256) }] }

theorem u1983 : Upper (D 7) (R 7) [6,40,272,192,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 276 200 112 33 192 131 259), lower := (rows 7 42 276 200 112 33 192 128 256), losses := [] }

theorem u1984 : Upper (D 7) (R 7) [6,40,272,192,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 292 25 82 160 65 192 448), lower := (rows 7 42 292 25 82 160 65 128 256), losses := [] }

theorem u1985 : Upper (D 7) (R 7) [6,40,288,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,0),(4,5)], upper := (rows 7 42 292 25 82 160 192 193 321), lower := (rows 7 42 292 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 22 122 356 24 114 224 224 224 256) }] }

theorem u1986 : Upper (D 7) (R 7) [6,40,288,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 7 42 292 73 145 160 66 208 336), lower := (rows 7 42 292 73 145 160 66 128 256), losses := [] }

theorem u1987 : Upper (D 7) (R 7) [6,40,288,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 42 292 73 145 160 80 194 322), lower := (rows 7 42 292 73 145 160 80 128 256), losses := [] }

theorem u1988 : Upper (D 7) (R 7) [6,40,288,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1988 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 42 292 73 146 160 65 208 336), lower := (rows 7 42 292 73 146 160 65 128 256), losses := [] }

theorem u1989 : Upper (D 7) (R 7) [6,40,288,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1990 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 420, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 292 73 146 160 80 193 321), lower := (rows 7 42 292 73 146 160 80 128 256), losses := [] }

theorem u1990 : Upper (D 7) (R 7) [6,40,288,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1990 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 42 292 73 208 160 65 146 274), lower := (rows 7 42 292 73 208 160 65 128 256), losses := [] }

theorem u1991 : Upper (D 7) (R 7) [6,40,288,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 7 42 292 73 208 160 66 145 273), lower := (rows 7 42 292 73 208 160 66 128 256), losses := [] }

theorem u1992 : Upper (D 7) (R 7) [6,40,288,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 292 73 208 160 80 131 259), lower := (rows 7 42 292 73 208 160 80 128 256), losses := [] }

theorem u1993 : Upper (D 7) (R 7) [6,40,288,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1993 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 42 292 88 146 33 65 192 448), lower := (rows 7 42 292 88 146 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 18 32 64 200 328), good := (rows 22 446 292 472 150 32 448 128 256) }] }

theorem u1994 : Upper (D 7) (R 7) [6,40,288,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 42 292 88 146 33 192 193 321), lower := (rows 7 42 292 88 146 33 192 128 256), losses := [] }

theorem u1995 : Upper (D 7) (R 7) [6,40,288,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 428, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 42 292 200 81 33 66 144 400), lower := (rows 7 42 292 200 81 33 66 128 256), losses := [] }

theorem u1996 : Upper (D 7) (R 7) [6,40,288,192,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 292 200 81 33 80 130 386), lower := (rows 7 42 292 200 81 33 80 128 256), losses := [] }

theorem u1997 : Upper (D 7) (R 7) [6,40,288,192,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1997 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1998 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 292 200 81 33 192 146 274), lower := (rows 7 42 292 200 81 33 192 128 256), losses := [] }

theorem u1998 : Upper (D 7) (R 7) [6,40,288,192,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 42 324 25 82 160 65 160 416), lower := (rows 7 42 324 25 82 160 65 128 256), losses := [] }

theorem u1999 : Upper (D 7) (R 7) [6,40,320,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 324 25 82 160 96 129 385), lower := (rows 7 42 324 25 82 160 96 128 256), losses := [] }

theorem u2000 : Upper (D 7) (R 7) [6,40,320,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2001 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(2,1),(3,5),(4,0)], upper := (rows 7 42 324 25 82 160 192 161 289), lower := (rows 7 42 324 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 22 122 356 24 114 224 224 224 256) },{ target := 5, region := (rows 1 2 4 9 18 0 224 128 256), good := (rows 31 90 324 25 82 192 192 192 256) }] }

theorem u2001 : Upper (D 7) (R 7) [6,40,320,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2002 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 162, targets := 65 }], pairs := [(0,5),(1,0),(1,6),(2,5)], upper := (rows 7 42 324 25 112 160 65 130 386), lower := (rows 7 42 324 25 112 160 65 128 256), losses := [] }

theorem u2002 : Upper (D 7) (R 7) [6,40,320,17,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2003 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,7)], upper := (rows 7 42 324 25 112 160 66 129 385), lower := (rows 7 42 324 25 112 160 66 128 256), losses := [] }

theorem u2003 : Upper (D 7) (R 7) [6,40,320,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 25 112 160 192 131 259), lower := (rows 7 42 324 25 112 160 192 128 256), losses := [] }

theorem u2004 : Upper (D 7) (R 7) [6,40,320,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 5, region := 388, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,6)], upper := (rows 7 42 324 25 146 96 65 160 416), lower := (rows 7 42 324 25 146 96 65 128 256), losses := [] }

theorem u2005 : Upper (D 7) (R 7) [6,40,320,17,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 324 25 146 96 96 129 385), lower := (rows 7 42 324 25 146 96 96 128 256), losses := [] }

theorem u2006 : Upper (D 7) (R 7) [6,40,320,17,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2007 : Route 9 := (fun mask => (mask,id))

def c2007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2007 : Upper (D 7) (R 7) [6,40,320,17,130,64,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,130,64,128] 13 (by decide) (choices 1) [1,32] r2007 c2007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u96
  · exact u97

def b2008 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 324 25 176 96 65 130 386), lower := (rows 7 42 324 25 176 96 65 128 256), losses := [] }

theorem u2008 : Upper (D 7) (R 7) [6,40,320,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 98, targets := 129 }], pairs := [(0,5),(1,0),(1,7),(2,5)], upper := (rows 7 42 324 25 176 96 66 129 385), lower := (rows 7 42 324 25 176 96 66 128 256), losses := [] }

theorem u2009 : Upper (D 7) (R 7) [6,40,320,17,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 42 324 25 176 96 192 131 259), lower := (rows 7 42 324 25 176 96 192 128 256), losses := [] }

theorem u2010 : Upper (D 7) (R 7) [6,40,320,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2011 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 42 324 25 208 34 65 160 416), lower := (rows 7 42 324 25 208 34 65 128 256), losses := [{ target := 0, region := (rows 0 10 84 8 84 43 64 235 363), good := (rows 438 426 468 446 468 418 500 128 256) }] }

theorem u2011 : Upper (D 7) (R 7) [6,40,320,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2012 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 324 25 208 34 96 129 385), lower := (rows 7 42 324 25 208 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 7 9 19 32 98 137 265), good := (rows 477 508 324 413 208 116 96 128 256) }] }

theorem u2012 : Upper (D 7) (R 7) [6,40,320,17,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 25 208 34 192 161 289), lower := (rows 7 42 324 25 208 34 192 128 256), losses := [] }

theorem u2013 : Upper (D 7) (R 7) [6,40,320,17,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,1),(3,7),(4,1)], upper := (rows 7 42 324 26 145 96 65 160 416), lower := (rows 7 42 324 26 145 96 65 128 256), losses := [] }

theorem u2014 : Upper (D 7) (R 7) [6,40,320,18,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 324 26 145 96 96 129 385), lower := (rows 7 42 324 26 145 96 96 128 256), losses := [] }

theorem u2015 : Upper (D 7) (R 7) [6,40,320,18,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 324 26 145 96 192 161 289), lower := (rows 7 42 324 26 145 96 192 128 256), losses := [] }

theorem u2016 : Upper (D 7) (R 7) [6,40,320,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 324 26 208 33 65 160 416), lower := (rows 7 42 324 26 208 33 65 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 97 0 247 375), good := (rows 423 426 420 410 442 417 417 128 256) }] }

theorem u2017 : Upper (D 7) (R 7) [6,40,320,18,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2018 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 42 324 26 208 33 96 129 385), lower := (rows 7 42 324 26 208 33 96 128 256), losses := [{ target := 5, region := (rows 1 2 68 8 80 0 64 161 289), good := (rows 391 394 340 26 212 385 468 128 256) }] }

theorem u2018 : Upper (D 7) (R 7) [6,40,320,18,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2019 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 26 208 33 192 161 289), lower := (rows 7 42 324 26 208 33 192 128 256), losses := [] }

theorem u2019 : Upper (D 7) (R 7) [6,40,320,18,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 176, targets := 66 },{ cop := 0, region := 72, targets := 160 }], pairs := [(3,5),(3,7),(4,1),(4,6)], upper := (rows 7 42 324 73 49 160 66 144 400), lower := (rows 7 42 324 73 49 160 66 128 256), losses := [] }

theorem u2020 : Upper (D 7) (R 7) [6,40,320,65,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 7 42 324 73 49 160 80 130 386), lower := (rows 7 42 324 73 49 160 80 128 256), losses := [] }

theorem u2021 : Upper (D 7) (R 7) [6,40,320,65,33,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2021 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,0),(1,6),(3,1),(4,6)], upper := (rows 7 42 324 73 49 160 192 146 274), lower := (rows 7 42 324 73 49 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 6 106 356 106 112 224 224 224 256) },{ target := 1, region := (rows 1 0 4 24 24 224 224 128 256), good := (rows 5 120 356 121 121 224 224 224 256) }] }

theorem u2022 : Upper (D 7) (R 7) [6,40,320,65,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 176, targets := 66 },{ cop := 0, region := 72, targets := 160 }], pairs := [(3,5),(3,7),(4,1),(4,6)], upper := (rows 7 42 324 73 145 160 66 176 304), lower := (rows 7 42 324 73 145 160 66 128 256), losses := [] }

theorem u2023 : Upper (D 7) (R 7) [6,40,320,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 7 42 324 73 145 160 80 162 290), lower := (rows 7 42 324 73 145 160 80 128 256), losses := [] }

theorem u2024 : Upper (D 7) (R 7) [6,40,320,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2024 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 0, region := 144, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,6),(3,1),(4,5),(4,6)], upper := (rows 7 42 324 73 145 160 96 146 274), lower := (rows 7 42 324 73 145 160 96 128 256), losses := [] }

theorem u2025 : Upper (D 7) (R 7) [6,40,320,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 324 73 146 48 65 160 416), lower := (rows 7 42 324 73 146 48 65 128 256), losses := [] }

theorem u2026 : Upper (D 7) (R 7) [6,40,320,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2026 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2027 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 388, targets := 34 },{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 7 42 324 73 146 48 96 129 385), lower := (rows 7 42 324 73 146 48 96 128 256), losses := [] }

theorem u2027 : Upper (D 7) (R 7) [6,40,320,65,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2027 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2028 : Route 9 := (fun mask => (mask,id))

def c2028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2028 : Upper (D 7) (R 7) [6,40,320,65,130,16,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,130,16,128] 13 (by decide) (choices 1) [1,32] r2028 c2028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u98
  · exact u99

def b2029 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 324 73 146 160 65 176 304), lower := (rows 7 42 324 73 146 160 65 128 256), losses := [] }

theorem u2029 : Upper (D 7) (R 7) [6,40,320,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 3, region := 420, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 7 42 324 73 146 160 80 161 289), lower := (rows 7 42 324 73 146 160 80 128 256), losses := [] }

theorem u2030 : Upper (D 7) (R 7) [6,40,320,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2030 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,6),(3,1),(4,5),(4,6)], upper := (rows 7 42 324 73 146 160 96 145 273), lower := (rows 7 42 324 73 146 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 176 242 128 256), good := (rows 77 104 324 73 240 224 96 224 256) }] }

theorem u2031 : Upper (D 7) (R 7) [6,40,320,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 160 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 42 324 74 145 160 65 176 304), lower := (rows 7 42 324 74 145 160 65 128 256), losses := [] }

theorem u2032 : Upper (D 7) (R 7) [6,40,320,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 324 74 145 160 80 161 289), lower := (rows 7 42 324 74 145 160 80 128 256), losses := [] }

theorem u2033 : Upper (D 7) (R 7) [6,40,320,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2033 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 324 74 145 160 96 145 273), lower := (rows 7 42 324 74 145 160 96 128 256), losses := [] }

theorem u2034 : Upper (D 7) (R 7) [6,40,320,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,6)], upper := (rows 7 42 324 88 146 33 65 160 416), lower := (rows 7 42 324 88 146 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 19 32 64 162 290), good := (rows 406 442 332 88 402 432 88 128 256) }] }

theorem u2035 : Upper (D 7) (R 7) [6,40,320,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,1),(3,0),(4,5),(4,6)], upper := (rows 7 42 324 88 146 33 96 129 385), lower := (rows 7 42 324 88 146 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 98 128 256), good := (rows 70 106 324 88 218 96 96 128 256) }] }

theorem u2036 : Upper (D 7) (R 7) [6,40,320,80,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2037 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 42 324 88 146 33 192 161 289), lower := (rows 7 42 324 88 146 33 192 128 256), losses := [] }

theorem u2037 : Upper (D 7) (R 7) [6,40,320,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2038 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 324 88 176 33 65 130 386), lower := (rows 7 42 324 88 176 33 65 128 256), losses := [] }

theorem u2038 : Upper (D 7) (R 7) [6,40,320,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 324 88 176 33 66 129 385), lower := (rows 7 42 324 88 176 33 66 128 256), losses := [] }

theorem u2039 : Upper (D 7) (R 7) [6,40,320,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P07
