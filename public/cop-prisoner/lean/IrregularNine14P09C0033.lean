import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0001

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 194 76 265 400 36 96 145 273), lower := (rows 35 194 76 265 400 36 96 128 256), losses := [] }

theorem u1980 : Upper (D 9) (R 9) [34,192,72,257,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1980 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 68, targets := 416 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8)], upper := (rows 35 194 76 265 400 48 65 164 292), lower := (rows 35 194 76 265 400 48 65 128 256), losses := [] }

theorem u1981 : Upper (D 9) (R 9) [34,192,72,257,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1981 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 35 194 76 265 400 48 68 161 289), lower := (rows 35 194 76 265 400 48 68 128 256), losses := [] }

theorem u1982 : Upper (D 9) (R 9) [34,192,72,257,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1982 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1983 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 4, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(2,7),(3,7)], upper := (rows 35 194 76 265 400 48 96 133 261), lower := (rows 35 194 76 265 400 48 96 128 256), losses := [] }

theorem u1983 : Upper (D 9) (R 9) [34,192,72,257,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1983 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(3,6),(4,6)], upper := (rows 35 194 76 280 176 36 65 385 257), lower := (rows 35 194 76 280 176 36 65 128 256), losses := [] }

theorem u1984 : Upper (D 9) (R 9) [34,192,72,272,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1984 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(1,8),(3,6),(4,8)], upper := (rows 35 194 76 280 176 36 320 129 257), lower := (rows 35 194 76 280 176 36 320 128 256), losses := [] }

theorem u1985 : Upper (D 9) (R 9) [34,192,72,272,160,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1985 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1986 : Route 9 := (fun mask => (mask,id))

def c1986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1986 : Upper (D 9) (R 9) [34,192,72,272,160,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160,256,1] 13 (by decide) (choices 1) [1,4] r1986 c1986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u112
  · exact u113

def b1987 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,6)], upper := (rows 35 194 76 280 176 288 68 129 257), lower := (rows 35 194 76 280 176 288 68 128 256), losses := [] }

theorem u1987 : Upper (D 9) (R 9) [34,192,72,272,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1987 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 402, targets := 33 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 76 296 276 33 65 144 400), lower := (rows 35 194 76 296 276 33 65 128 256), losses := [] }

theorem u1988 : Upper (D 9) (R 9) [34,192,72,288,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1988 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 84, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 35 194 76 296 276 33 80 129 385), lower := (rows 35 194 76 296 276 33 80 128 256), losses := [] }

theorem u1989 : Upper (D 9) (R 9) [34,192,72,288,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1989 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1990 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 76 296 276 33 192 145 273), lower := (rows 35 194 76 296 276 33 192 128 256), losses := [] }

theorem u1990 : Upper (D 9) (R 9) [34,192,72,288,260,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1990 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 76 296 400 33 65 148 276), lower := (rows 35 194 76 296 400 33 65 128 256), losses := [] }

theorem u1991 : Upper (D 9) (R 9) [34,192,72,288,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1991 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 417 }], pairs := [(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 194 76 296 400 33 68 145 273), lower := (rows 35 194 76 296 400 33 68 128 256), losses := [] }

theorem u1992 : Upper (D 9) (R 9) [34,192,72,288,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1992 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 76 296 400 33 80 133 261), lower := (rows 35 194 76 296 400 33 80 128 256), losses := [] }

theorem u1993 : Upper (D 9) (R 9) [34,192,72,288,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1993 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 392 273 33 68 176 304), lower := (rows 35 194 76 392 273 33 68 128 256), losses := [] }

theorem u1994 : Upper (D 9) (R 9) [34,192,72,384,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1994 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 163, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8)], upper := (rows 35 194 76 392 273 33 80 164 292), lower := (rows 35 194 76 392 273 33 80 128 256), losses := [] }

theorem u1995 : Upper (D 9) (R 9) [34,192,72,384,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1995 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 392 273 33 96 148 276), lower := (rows 35 194 76 392 273 33 96 128 256), losses := [] }

theorem u1996 : Upper (D 9) (R 9) [34,192,72,384,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1996 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(1,8),(2,8),(3,6)], upper := (rows 35 194 76 392 273 36 65 176 304), lower := (rows 35 194 76 392 273 36 65 128 256), losses := [] }

theorem u1997 : Upper (D 9) (R 9) [34,192,72,384,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1997 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1998 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 2, region := 163, targets := 256 }], pairs := [(0,8),(3,6),(4,6)], upper := (rows 35 194 76 392 273 36 80 161 289), lower := (rows 35 194 76 392 273 36 80 128 256), losses := [] }

theorem u1998 : Upper (D 9) (R 9) [34,192,72,384,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1998 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 194 76 392 273 36 96 145 273), lower := (rows 35 194 76 392 273 36 96 128 256), losses := [] }

theorem u1999 : Upper (D 9) (R 9) [34,192,72,384,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1999 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2000 : Route 9 := (fun mask => (mask,id))

def c2000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2000 : Upper (D 9) (R 9) [34,192,72,384,257,16,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,16,1] 13 (by decide) (choices 1) [4,32] r2000 c2000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u114
  · exact u115

def b2001 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 289 }], pairs := [(1,0),(1,5),(1,8)], upper := (rows 35 194 76 392 273 48 68 161 289), lower := (rows 35 194 76 392 273 48 68 128 256), losses := [] }

theorem u2001 : Upper (D 9) (R 9) [34,192,72,384,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2001 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2002 : Route 9 := (fun mask => (mask,id))

def c2002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2002 : Upper (D 9) (R 9) [34,192,72,384,257,16,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,16,32] 13 (by decide) (choices 1) [1,4] r2002 c2002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u116
  · exact u117

def b2003 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 392 276 33 65 176 304), lower := (rows 35 194 76 392 276 33 65 128 256), losses := [] }

theorem u2003 : Upper (D 9) (R 9) [34,192,72,384,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2003 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 86, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 392 276 33 80 161 289), lower := (rows 35 194 76 392 276 33 80 128 256), losses := [] }

theorem u2004 : Upper (D 9) (R 9) [34,192,72,384,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2004 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 392 276 33 96 145 273), lower := (rows 35 194 76 392 276 33 96 128 256), losses := [] }

theorem u2005 : Upper (D 9) (R 9) [34,192,72,384,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2005 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2006 : Route 9 := (fun mask => (mask,id))

def c2006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2006 : Upper (D 9) (R 9) [34,192,72,384,260,16,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,260,16,1] 13 (by decide) (choices 1) [1,32] r2006 c2006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u118
  · exact u119

def b2007 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 118, targets := 1 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 35 194 76 392 276 48 96 129 257), lower := (rows 35 194 76 392 276 48 96 128 256), losses := [] }

theorem u2007 : Upper (D 9) (R 9) [34,192,72,384,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2007 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2008 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 392 304 33 65 148 276), lower := (rows 35 194 76 392 304 33 65 128 256), losses := [] }

theorem u2008 : Upper (D 9) (R 9) [34,192,72,384,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2008 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 392 304 33 68 145 273), lower := (rows 35 194 76 392 304 33 68 128 256), losses := [] }

theorem u2009 : Upper (D 9) (R 9) [34,192,72,384,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2009 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 163, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8)], upper := (rows 35 194 76 392 304 33 80 133 261), lower := (rows 35 194 76 392 304 33 80 128 256), losses := [] }

theorem u2010 : Upper (D 9) (R 9) [34,192,72,384,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2010 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2011 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 100 265 276 40 65 144 400), lower := (rows 35 194 100 265 276 40 65 128 256), losses := [] }

theorem u2011 : Upper (D 9) (R 9) [34,192,96,257,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2011 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2012 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 116, targets := 129 }], pairs := [(2,0),(2,7),(4,0)], upper := (rows 35 194 100 265 276 40 80 129 385), lower := (rows 35 194 100 265 276 40 80 128 256), losses := [] }

theorem u2012 : Upper (D 9) (R 9) [34,192,96,257,260,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2012 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 100 265 276 40 192 145 273), lower := (rows 35 194 100 265 276 40 192 128 256), losses := [] }

theorem u2013 : Upper (D 9) (R 9) [34,192,96,257,260,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2013 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 100 265 400 40 65 148 276), lower := (rows 35 194 100 265 400 40 65 128 256), losses := [] }

theorem u2014 : Upper (D 9) (R 9) [34,192,96,257,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2014 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 100 265 400 40 68 145 273), lower := (rows 35 194 100 265 400 40 68 128 256), losses := [] }

theorem u2015 : Upper (D 9) (R 9) [34,192,96,257,384,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2015 [(5,3),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 100 265 400 40 80 133 261), lower := (rows 35 194 100 265 400 40 80 128 256), losses := [] }

theorem u2016 : Upper (D 9) (R 9) [34,192,96,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2016 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 0, region := 68, targets := 128 }], pairs := [(0,8),(1,8),(2,7),(2,8)], upper := (rows 35 194 100 265 400 48 65 140 268), lower := (rows 35 194 100 265 400 48 65 128 256), losses := [] }

theorem u2017 : Upper (D 9) (R 9) [34,192,96,257,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2017 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2018 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 100 265 400 48 68 137 265), lower := (rows 35 194 100 265 400 48 68 128 256), losses := [] }

theorem u2018 : Upper (D 9) (R 9) [34,192,96,257,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2018 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2019 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 131, targets := 256 }], pairs := [(0,8),(2,7),(3,7)], upper := (rows 35 194 100 265 400 48 72 133 261), lower := (rows 35 194 100 265 400 48 72 128 256), losses := [] }

theorem u2019 : Upper (D 9) (R 9) [34,192,96,257,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2019 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(4,5)], upper := (rows 35 194 100 268 400 40 65 145 273), lower := (rows 35 194 100 268 400 40 65 128 256), losses := [] }

theorem u2020 : Upper (D 9) (R 9) [34,192,96,260,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2020 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 100 268 400 40 80 129 257), lower := (rows 35 194 100 268 400 40 80 128 256), losses := [] }

theorem u2021 : Upper (D 9) (R 9) [34,192,96,260,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2021 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 0, region := 68, targets := 128 }], pairs := [(0,8),(1,8),(2,7),(2,8)], upper := (rows 35 194 100 268 400 48 65 137 265), lower := (rows 35 194 100 268 400 48 65 128 256), losses := [] }

theorem u2022 : Upper (D 9) (R 9) [34,192,96,260,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2022 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 194 100 268 400 48 72 129 257), lower := (rows 35 194 100 268 400 48 72 128 256), losses := [] }

theorem u2023 : Upper (D 9) (R 9) [34,192,96,260,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2023 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 360, targets := 1 },{ cop := 6, region := 289, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,5)], upper := (rows 97 7 14 56 145 288 192 448 320), lower := (rows 97 7 14 56 145 288 192 128 256), losses := [{ target := 7, region := (rows 65 18 28 24 16 371 64 0 321), good := (rows 353 295 46 62 319 288 353 0 288) }] }

theorem u2024 : Upper (D 9) (R 9) [96,5,10,48,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2024 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 14 56 145 288 320 192 448), lower := (rows 97 7 14 56 145 288 320 128 256), losses := [] }

theorem u2025 : Upper (D 9) (R 9) [96,5,10,48,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2025 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 14 56 208 288 65 384 384), lower := (rows 97 7 14 56 208 288 65 128 256), losses := [] }

theorem u2026 : Upper (D 9) (R 9) [96,5,10,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2026 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2027 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 97 7 14 56 208 288 192 385 257), lower := (rows 97 7 14 56 208 288 192 128 256), losses := [] }

theorem u2027 : Upper (D 9) (R 9) [96,5,10,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2027 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2028 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 14 56 208 288 320 129 385), lower := (rows 97 7 14 56 208 288 320 128 256), losses := [] }

theorem u2028 : Upper (D 9) (R 9) [96,5,10,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2028 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2029 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 152 273 96 192 416 288), lower := (rows 97 7 14 152 273 96 192 128 256), losses := [] }

theorem u2029 : Upper (D 9) (R 9) [96,5,10,144,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2029 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 4, region := 232, targets := 1 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,0),(4,7)], upper := (rows 97 7 14 152 273 160 320 224 352), lower := (rows 97 7 14 152 273 160 320 128 256), losses := [{ target := 8, region := (rows 65 18 28 24 16 251 64 193 0), good := (rows 225 167 46 190 191 160 225 160 0) }] }

theorem u2030 : Upper (D 9) (R 9) [96,5,10,144,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2030 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 97 7 14 152 304 160 65 448 320), lower := (rows 97 7 14 152 304 160 65 128 256), losses := [] }

theorem u2031 : Upper (D 9) (R 9) [96,5,10,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2031 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,7),(4,7)], upper := (rows 97 7 14 152 304 160 320 193 321), lower := (rows 97 7 14 152 304 160 320 128 256), losses := [{ target := 7, region := (rows 49 10 12 8 49 32 383 0 315), good := (rows 369 343 334 351 369 369 320 0 320) }] }

theorem u2032 : Upper (D 9) (R 9) [96,5,10,144,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2032 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 7 14 168 145 288 80 448 320), lower := (rows 97 7 14 168 145 288 80 128 256), losses := [] }

theorem u2033 : Upper (D 9) (R 9) [96,5,10,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2033 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 14 168 145 288 320 208 336), lower := (rows 97 7 14 168 145 288 320 128 256), losses := [] }

theorem u2034 : Upper (D 9) (R 9) [96,5,10,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 7 14 168 208 288 65 400 272), lower := (rows 97 7 14 168 208 288 65 128 256), losses := [] }

theorem u2035 : Upper (D 9) (R 9) [96,5,10,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2035 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 7 14 168 208 288 80 385 257), lower := (rows 97 7 14 168 208 288 80 128 256), losses := [] }

theorem u2036 : Upper (D 9) (R 9) [96,5,10,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2036 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2037 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 14 168 208 288 320 145 273), lower := (rows 97 7 14 168 208 288 320 128 256), losses := [] }

theorem u2037 : Upper (D 9) (R 9) [96,5,10,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2037 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2038 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 7 14 168 273 48 192 448 320), lower := (rows 97 7 14 168 273 48 192 128 256), losses := [] }

theorem u2038 : Upper (D 9) (R 9) [96,5,10,160,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2038 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 6, region := 49, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 7 14 168 273 48 320 192 448), lower := (rows 97 7 14 168 273 48 320 128 256), losses := [] }

theorem u2039 : Upper (D 9) (R 9) [96,5,10,160,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2039 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P09
