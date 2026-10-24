import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0012

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 140 400 312 376 440 312), lower := (rows 35 67 100 140 400 32 64 128 256), losses := [] }

theorem u1980 : Upper (D 10) (R 10) [34,65,96,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1980 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 152 280 420 484 420 420), lower := (rows 35 67 100 152 280 32 64 128 256), losses := [] }

theorem u1981 : Upper (D 10) (R 10) [34,65,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1981 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 152 304 428 460 396 396), lower := (rows 35 67 100 152 304 32 64 128 256), losses := [] }

theorem u1982 : Upper (D 10) (R 10) [34,65,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1982 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1983 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 168 400 316 348 412 284), lower := (rows 35 67 100 168 400 32 64 128 256), losses := [] }

theorem u1983 : Upper (D 10) (R 10) [34,65,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1983 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 368, camps := [{ cop := 7, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 67 140 140 304 368 368 496 368), lower := (rows 35 67 140 140 304 32 64 128 256), losses := [] }

theorem u1984 : Upper (D 10) (R 10) [34,65,136,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1984 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 152 276 352 352 480 352), lower := (rows 35 67 140 152 276 32 64 128 256), losses := [] }

theorem u1985 : Upper (D 10) (R 10) [34,65,136,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1985 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 152 304 356 356 484 356), lower := (rows 35 67 140 152 304 32 64 128 256), losses := [] }

theorem u1986 : Upper (D 10) (R 10) [34,65,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1986 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 168 276 368 368 496 368), lower := (rows 35 67 140 168 276 32 64 128 256), losses := [] }

theorem u1987 : Upper (D 10) (R 10) [34,65,136,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1987 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 340, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 168 304 372 340 468 340), lower := (rows 35 67 140 168 304 32 64 128 256), losses := [] }

theorem u1988 : Upper (D 10) (R 10) [34,65,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1988 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 200 276 304 368 432 304), lower := (rows 35 67 140 200 276 32 64 128 256), losses := [] }

theorem u1989 : Upper (D 10) (R 10) [34,65,136,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1989 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1990 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 200 304 308 372 436 308), lower := (rows 35 67 140 200 304 32 64 128 256), losses := [] }

theorem u1990 : Upper (D 10) (R 10) [34,65,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1990 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 268 176 368 368 496 368), lower := (rows 35 67 140 268 176 32 64 128 256), losses := [] }

theorem u1991 : Upper (D 10) (R 10) [34,65,136,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1991 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 268 208 304 368 432 304), lower := (rows 35 67 140 268 208 32 64 128 256), losses := [] }

theorem u1992 : Upper (D 10) (R 10) [34,65,136,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1992 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 67 140 268 400 112 112 240 368), lower := (rows 35 67 140 268 400 32 64 128 256), losses := [] }

theorem u1993 : Upper (D 10) (R 10) [34,65,136,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1993 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 280 176 356 356 484 356), lower := (rows 35 67 140 280 176 32 64 128 256), losses := [] }

theorem u1994 : Upper (D 10) (R 10) [34,65,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1994 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 280 208 292 356 420 292), lower := (rows 35 67 140 280 208 32 64 128 256), losses := [] }

theorem u1995 : Upper (D 10) (R 10) [34,65,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1995 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 67 140 280 400 100 100 228 356), lower := (rows 35 67 140 280 400 32 64 128 256), losses := [] }

theorem u1996 : Upper (D 10) (R 10) [34,65,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1996 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1997 : Route 9 := (fun mask => (mask,id))

def c1997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1997 : Upper (D 10) (R 10) [34,65,136,288,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,160] 13 (by decide) (choices 1) [4,16,64,256] r1997 c1997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u724
  · exact u725
  · exact u726
  · exact u727

def b1998 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 296 208 308 372 436 308), lower := (rows 35 67 140 296 208 32 64 128 256), losses := [] }

theorem u1998 : Upper (D 10) (R 10) [34,65,136,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1998 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 35 67 140 296 304 244 212 212 468), lower := (rows 35 67 140 296 304 32 64 128 256), losses := [] }

theorem u1999 : Upper (D 10) (R 10) [34,65,136,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1999 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 296 336 180 244 180 436), lower := (rows 35 67 140 296 336 32 64 128 256), losses := [] }

theorem u2000 : Upper (D 10) (R 10) [34,65,136,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2000 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2001 : Route 9 := (fun mask => (mask,id))

def c2001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2001 : Upper (D 10) (R 10) [34,65,136,288,384] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,384] 13 (by decide) (choices 1) [4,16,64] r2001 c2001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u728
  · exact u729
  · exact u730

def b2002 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 140 328 176 308 372 436 308), lower := (rows 35 67 140 328 176 32 64 128 256), losses := [] }

theorem u2002 : Upper (D 10) (R 10) [34,65,136,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2002 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2003 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 140 328 304 180 244 180 436), lower := (rows 35 67 140 328 304 32 64 128 256), losses := [] }

theorem u2003 : Upper (D 10) (R 10) [34,65,136,320,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2003 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 140 328 400 52 116 180 308), lower := (rows 35 67 140 328 400 32 64 128 256), losses := [] }

theorem u2004 : Upper (D 10) (R 10) [34,65,136,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2004 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 392 304 116 116 244 372), lower := (rows 35 67 140 392 304 32 64 128 256), losses := [] }

theorem u2005 : Upper (D 10) (R 10) [34,65,136,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2005 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 284, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 200 304 316 348 412 284), lower := (rows 35 67 164 200 304 32 64 128 256), losses := [] }

theorem u2006 : Upper (D 10) (R 10) [34,65,160,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2006 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2007_8 : Upper (D 10) (R 10) [34,65,160,288,384,8] 13 :=
  permutation_upper _ _ _ [34,65,160,288,384,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u731

def r2007 : Route 9 := (fun mask => (mask,id))

def c2007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2007 : Upper (D 10) (R 10) [34,65,160,288,384] 13 := by
  apply FastRouting.sound _ _ [34,65,160,288,384] 13 (by decide) (choices 1) [4,8,16,64] r2007 c2007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u731
  · exact m2007_8
  · exact u732
  · exact u733

def b2008 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 328 400 60 124 188 316), lower := (rows 35 67 164 328 400 32 64 128 256), losses := [] }

theorem u2008 : Upper (D 10) (R 10) [34,65,160,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2008 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 73 176 432 464 400 400), lower := (rows 35 70 44 73 176 32 64 128 256), losses := [] }

theorem u2009 : Upper (D 10) (R 10) [34,68,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2009 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 73 400 432 496 432 432), lower := (rows 35 70 44 73 400 32 64 128 256), losses := [] }

theorem u2010 : Upper (D 10) (R 10) [34,68,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2010 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2011 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 88 145 416 480 416 416), lower := (rows 35 70 44 88 145 32 64 128 256), losses := [] }

theorem u2011 : Upper (D 10) (R 10) [34,68,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2011 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2012 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 88 176 417 449 385 385), lower := (rows 35 70 44 88 176 32 64 128 256), losses := [] }

theorem u2012 : Upper (D 10) (R 10) [34,68,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2012 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 88 400 417 481 417 417), lower := (rows 35 70 44 88 400 32 64 128 256), losses := [] }

theorem u2013 : Upper (D 10) (R 10) [34,68,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2013 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 44 104 145 432 464 400 400), lower := (rows 35 70 44 104 145 32 64 128 256), losses := [] }

theorem u2014 : Upper (D 10) (R 10) [34,68,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2014 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 44 104 400 433 465 401 401), lower := (rows 35 70 44 104 400 32 64 128 256), losses := [] }

theorem u2015 : Upper (D 10) (R 10) [34,68,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2015 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2016 : Route 9 := (fun mask => (mask,id))

def c2016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2016 : Upper (D 10) (R 10) [34,68,40,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,96] 13 (by decide) (choices 1) [16,128,256] r2016 c2016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u734
  · exact u735
  · exact u736

def r2017 : Route 9 := (fun mask => (mask,id))

def c2017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2017 : Upper (D 10) (R 10) [34,68,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192] 13 (by decide) (choices 1) [16,256] r2017 c2017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u737
  · exact u738

theorem m2018_128 : Upper (D 10) (R 10) [34,68,40,129,288,128] 13 :=
  permutation_upper _ _ _ [34,68,40,129,288,64] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u740

def r2018 : Route 9 := (fun mask => (mask,id))

def c2018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u2018 : Upper (D 10) (R 10) [34,68,40,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,288] 13 (by decide) (choices 1) [16,64,128,256] r2018 c2018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u739
  · exact u740
  · exact m2018_128
  · exact u741

def r2019 : Route 9 := (fun mask => (mask,id))

def c2019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2019 : Upper (D 10) (R 10) [34,68,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320] 13 (by decide) (choices 1) [16,128,256] r2019 c2019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u742
  · exact u743
  · exact u744

def b2020 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 152 81 416 480 416 416), lower := (rows 35 70 44 152 81 32 64 128 256), losses := [] }

theorem u2020 : Upper (D 10) (R 10) [34,68,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2020 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2021 : Route 9 := (fun mask => (mask,id))

def c2021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2021 : Upper (D 10) (R 10) [34,68,40,144,96] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,96] 13 (by decide) (choices 1) [1,128,256] r2021 c2021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u745
  · exact u746
  · exact u747

def b2022 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 145 352 352 480 352), lower := (rows 35 70 44 152 145 32 64 128 256), losses := [] }

theorem u2022 : Upper (D 10) (R 10) [34,68,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2022 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 35 70 44 152 176 353 321 449 321), lower := (rows 35 70 44 152 176 32 64 128 256), losses := [] }

theorem u2023 : Upper (D 10) (R 10) [34,68,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2023 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 208 289 353 417 289), lower := (rows 35 70 44 152 208 32 64 128 256), losses := [] }

theorem u2024 : Upper (D 10) (R 10) [34,68,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2024 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2025 : Route 9 := (fun mask => (mask,id))

def c2025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2025 : Upper (D 10) (R 10) [34,68,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,257] 13 (by decide) (choices 1) [64,128,256] r2025 c2025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u748
  · exact u749
  · exact u750

def r2026 : Route 9 := (fun mask => (mask,id))

def c2026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2026 : Upper (D 10) (R 10) [34,68,40,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,288] 13 (by decide) (choices 1) [1,64,128,256] r2026 c2026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u751
  · exact u752
  · exact u753
  · exact u754

def r2027 : Route 9 := (fun mask => (mask,id))

def c2027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2027 : Upper (D 10) (R 10) [34,68,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,320] 13 (by decide) (choices 1) [1,128,256] r2027 c2027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u755
  · exact u756
  · exact u757

def b2028 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 400 353 353 481 353), lower := (rows 35 70 44 152 400 32 64 128 256), losses := [] }

theorem u2028 : Upper (D 10) (R 10) [34,68,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2028 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2029 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 70 44 168 145 368 336 464 336), lower := (rows 35 70 44 168 145 32 64 128 256), losses := [] }

theorem u2029 : Upper (D 10) (R 10) [34,68,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2029 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 70 44 168 208 305 337 401 273), lower := (rows 35 70 44 168 208 32 64 128 256), losses := [] }

theorem u2030 : Upper (D 10) (R 10) [34,68,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2030 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 70 44 168 273 496 464 464 464), lower := (rows 35 70 44 168 273 32 64 128 256), losses := [] }

theorem u2031 : Upper (D 10) (R 10) [34,68,40,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2031 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 70 44 168 336 433 465 401 401), lower := (rows 35 70 44 168 336 32 64 128 256), losses := [] }

theorem u2032 : Upper (D 10) (R 10) [34,68,40,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2032 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 70 44 168 400 369 337 465 337), lower := (rows 35 70 44 168 400 32 64 128 256), losses := [] }

theorem u2033 : Upper (D 10) (R 10) [34,68,40,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2033 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 145 304 368 432 304), lower := (rows 35 70 44 200 145 32 64 128 256), losses := [] }

theorem u2034 : Upper (D 10) (R 10) [34,68,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2034 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 176 305 337 401 273), lower := (rows 35 70 44 200 176 32 64 128 256), losses := [] }

theorem u2035 : Upper (D 10) (R 10) [34,68,40,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2035 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 273 432 496 432 432), lower := (rows 35 70 44 200 273 32 64 128 256), losses := [] }

theorem u2036 : Upper (D 10) (R 10) [34,68,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2036 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2037 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 304 433 465 401 401), lower := (rows 35 70 44 200 304 32 64 128 256), losses := [] }

theorem u2037 : Upper (D 10) (R 10) [34,68,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2037 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2038 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 400 305 369 433 305), lower := (rows 35 70 44 200 400 32 64 128 256), losses := [] }

theorem u2038 : Upper (D 10) (R 10) [34,68,40,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2038 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 392 81 432 496 432 432), lower := (rows 35 70 44 392 81 32 64 128 256), losses := [] }

theorem u2039 : Upper (D 10) (R 10) [34,68,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2039 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P10
