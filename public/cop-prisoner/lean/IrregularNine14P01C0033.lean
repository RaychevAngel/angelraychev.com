import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0005
import IrregularNine14P01C0006

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 42 80 160 75 139 267), lower := (rows 305 70 148 42 80 160 64 128 256), losses := [] }

theorem u1980 : Upper (D 1) (R 1) [304,68,144,34,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 73 18 34 232 168 424), lower := (rows 305 70 148 73 18 34 64 128 256), losses := [] }

theorem u1981 : Upper (D 1) (R 1) [304,68,144,65,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1981
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 148 73 18 40 226 162 418), lower := (rows 305 70 148 73 18 40 64 128 256), losses := [] }

theorem u1982 : Upper (D 1) (R 1) [304,68,144,65,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1983 : Route 9 := (fun mask => (mask,id))

def c1983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1983 : Upper (D 1) (R 1) [304,68,144,65,2,128] 13 := by
  apply FastRouting.sound _ _ [304,68,144,65,2,128] 13 (by decide) (choices 1) [2,8,32] r1983 c1983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u326
  · exact u327
  · exact u328

def b1984 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 70 148 104 18 33 202 138 394), lower := (rows 305 70 148 104 18 33 64 128 256), losses := [] }

theorem u1984 : Upper (D 1) (R 1) [304,68,144,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 104 18 34 201 137 393), lower := (rows 305 70 148 104 18 34 64 128 256), losses := [] }

theorem u1985 : Upper (D 1) (R 1) [304,68,144,96,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 148 104 18 40 195 131 387), lower := (rows 305 70 148 104 18 40 64 128 256), losses := [] }

theorem u1986 : Upper (D 1) (R 1) [304,68,144,96,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 11, camps := [], pairs := [(3,1)], upper := (rows 305 70 148 104 18 160 75 139 267), lower := (rows 305 70 148 104 18 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 164 64 128 256), good := (rows 305 108 180 104 24 160 64 160 256) }] }

theorem u1987 : Upper (D 1) (R 1) [304,68,144,96,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1987
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 137 18 34 104 232 360), lower := (rows 305 70 148 137 18 34 64 128 256), losses := [] }

theorem u1988 : Upper (D 1) (R 1) [304,68,144,129,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1988
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 70 148 137 18 40 98 226 354), lower := (rows 305 70 148 137 18 40 64 128 256), losses := [] }

theorem u1989 : Upper (D 1) (R 1) [304,68,144,129,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1989
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1990 : Route 9 := (fun mask => (mask,id))

def c1990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1990 : Upper (D 1) (R 1) [304,68,144,129,2,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,129,2,64] 13 (by decide) (choices 1) [2,8,32] r1990 c1990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u329
  · exact u330
  · exact u331

def r1991 : Route 9 := (fun mask => (mask,id))

def c1991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1991 : Upper (D 1) (R 1) [304,68,144,129,64,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,129,64,2] 13 (by decide) (choices 1) [2,8,32] r1991 c1991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u332
  · exact u333
  · exact u334

def b1992 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 148 137 80 40 98 162 290), lower := (rows 305 70 148 137 80 40 64 128 256), losses := [] }

theorem u1992 : Upper (D 1) (R 1) [304,68,144,129,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1992
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 70 148 168 18 33 74 202 330), lower := (rows 305 70 148 168 18 33 64 128 256), losses := [] }

theorem u1993 : Upper (D 1) (R 1) [304,68,144,160,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1993
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 168 18 34 73 201 329), lower := (rows 305 70 148 168 18 34 64 128 256), losses := [] }

theorem u1994 : Upper (D 1) (R 1) [304,68,144,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1994
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 70 148 168 18 40 67 195 323), lower := (rows 305 70 148 168 18 40 64 128 256), losses := [] }

theorem u1995 : Upper (D 1) (R 1) [304,68,144,160,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1995
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1996 : Route 9 := (fun mask => (mask,id))

def c1996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1996 : Upper (D 1) (R 1) [304,68,144,160,2,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,2,64] 13 (by decide) (choices 1) [1,2,8] r1996 c1996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u335
  · exact u336
  · exact u337

def b1997 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 70 148 168 80 33 74 138 266), lower := (rows 305 70 148 168 80 33 64 128 256), losses := [] }

theorem u1997 : Upper (D 1) (R 1) [304,68,144,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1998 : Route 9 := (fun mask => (mask,id))

def c1998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1998 : Upper (D 1) (R 1) [304,68,144,160,64,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,64,2] 13 (by decide) (choices 1) [1,2,8] r1998 c1998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u338
  · exact u339
  · exact u340

def b1999 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 148 168 80 40 67 131 259), lower := (rows 305 70 148 168 80 40 64 128 256), losses := [] }

theorem u1999 : Upper (D 1) (R 1) [304,68,144,160,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1999
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 82 13 14 144 34 224 224 480), lower := (rows 305 82 13 14 144 34 64 128 256), losses := [] }

theorem u2000 : Upper (D 1) (R 1) [304,80,9,6,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2000
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2001 : Route 9 := (fun mask => (mask,id))

def c2001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2001 : Upper (D 1) (R 1) [304,80,9,6,128,64] 13 := by
  apply FastRouting.sound _ _ [304,80,9,6,128,64] 13 (by decide) (choices 1) [2,32,128] r2001 c2001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u341
  · exact u342
  · exact u343

def b2002 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 13 14 144 160 98 226 354), lower := (rows 305 82 13 14 144 160 64 128 256), losses := [] }

theorem u2002 : Upper (D 1) (R 1) [304,80,9,6,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2002
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2003 : Route 9 := (fun mask => (mask,id))

def c2003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2003 : Upper (D 1) (R 1) [304,80,9,130,128,2] 13 := by
  apply FastRouting.sound _ _ [304,80,9,130,128,2] 13 (by decide) (choices 1) [4,32] r2003 c2003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u344
  · exact u345

def b2004 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 82 13 138 144 36 98 226 354), lower := (rows 305 82 13 138 144 36 64 128 256), losses := [] }

theorem u2004 : Upper (D 1) (R 1) [304,80,9,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2005 : Route 9 := (fun mask => (mask,id))

def c2005 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2005 : Upper (D 1) (R 1) [304,80,9,130,128,64] 13 := by
  apply FastRouting.sound _ _ [304,80,9,130,128,64] 13 (by decide) (choices 1) [2,4,32] r2005 c2005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u346
  · exact u347
  · exact u348

def r2006 : Route 9 := (fun mask => (mask,id))

def c2006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2006 : Upper (D 1) (R 1) [304,80,10,129,128,2] 13 := by
  apply FastRouting.sound _ _ [304,80,10,129,128,2] 13 (by decide) (choices 1) [4,32] r2006 c2006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u349
  · exact u350

def b2007 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 82 14 137 144 36 98 226 354), lower := (rows 305 82 14 137 144 36 64 128 256), losses := [] }

theorem u2007 : Upper (D 1) (R 1) [304,80,10,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2008 : Route 9 := (fun mask => (mask,id))

def c2008 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2008 : Upper (D 1) (R 1) [304,80,10,129,128,64] 13 := by
  apply FastRouting.sound _ _ [304,80,10,129,128,64] 13 (by decide) (choices 1) [2,4,32] r2008 c2008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u351
  · exact u352
  · exact u353

def b2009 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 82 14 168 144 33 70 198 326), lower := (rows 305 82 14 168 144 33 64 128 256), losses := [] }

theorem u2009 : Upper (D 1) (R 1) [304,80,10,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2009
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2010 : Route 9 := (fun mask => (mask,id))

def c2010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2010 : Upper (D 1) (R 1) [304,80,10,160,128,2] 13 := by
  apply FastRouting.sound _ _ [304,80,10,160,128,2] 13 (by decide) (choices 1) [1,4] r2010 c2010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u354
  · exact u355

def b2011 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 82 14 168 144 36 67 195 323), lower := (rows 305 82 14 168 144 36 64 128 256), losses := [] }

theorem u2011 : Upper (D 1) (R 1) [304,80,10,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2011
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2012 : Route 9 := (fun mask => (mask,id))

def c2012 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2012 : Upper (D 1) (R 1) [304,80,10,160,128,64] 13 := by
  apply FastRouting.sound _ _ [304,80,10,160,128,64] 13 (by decide) (choices 1) [1,2,4] r2012 c2012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u356
  · exact u357
  · exact u358

def b2013 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 73 144 34 204 140 396), lower := (rows 305 82 38 73 144 34 64 128 256), losses := [] }

theorem u2013 : Upper (D 1) (R 1) [304,80,34,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2013
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 38 73 144 36 202 138 394), lower := (rows 305 82 38 73 144 36 64 128 256), losses := [] }

theorem u2014 : Upper (D 1) (R 1) [304,80,34,65,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 82 38 73 144 40 198 134 390), lower := (rows 305 82 38 73 144 40 64 128 256), losses := [] }

theorem u2015 : Upper (D 1) (R 1) [304,80,34,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2015
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 38 73 144 160 78 142 270), lower := (rows 305 82 38 73 144 160 64 128 256), losses := [] }

theorem u2016 : Upper (D 1) (R 1) [304,80,34,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 38 76 144 33 202 138 394), lower := (rows 305 82 38 76 144 33 64 128 256), losses := [] }

theorem u2017 : Upper (D 1) (R 1) [304,80,34,68,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2018 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 76 144 34 201 137 393), lower := (rows 305 82 38 76 144 34 64 128 256), losses := [] }

theorem u2018 : Upper (D 1) (R 1) [304,80,34,68,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2018
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2019 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 82 38 76 144 40 195 131 387), lower := (rows 305 82 38 76 144 40 64 128 256), losses := [] }

theorem u2019 : Upper (D 1) (R 1) [304,80,34,68,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2019
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 38 76 144 160 75 139 267), lower := (rows 305 82 38 76 144 160 64 128 256), losses := [] }

theorem u2020 : Upper (D 1) (R 1) [304,80,34,68,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 137 144 34 76 204 332), lower := (rows 305 82 38 137 144 34 64 128 256), losses := [] }

theorem u2021 : Upper (D 1) (R 1) [304,80,34,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 82 38 137 144 36 74 202 330), lower := (rows 305 82 38 137 144 36 64 128 256), losses := [] }

theorem u2022 : Upper (D 1) (R 1) [304,80,34,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2022
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 82 38 137 144 40 70 198 326), lower := (rows 305 82 38 137 144 40 64 128 256), losses := [] }

theorem u2023 : Upper (D 1) (R 1) [304,80,34,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 137 144 96 78 142 270), lower := (rows 305 82 38 137 144 96 64 128 256), losses := [] }

theorem u2024 : Upper (D 1) (R 1) [304,80,34,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 305 82 38 138 144 33 76 204 332), lower := (rows 305 82 38 138 144 33 64 128 256), losses := [] }

theorem u2025 : Upper (D 1) (R 1) [304,80,34,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 305 82 38 138 144 36 73 201 329), lower := (rows 305 82 38 138 144 36 64 128 256), losses := [] }

theorem u2026 : Upper (D 1) (R 1) [304,80,34,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2026
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2027 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 305 82 38 138 144 40 69 197 325), lower := (rows 305 82 38 138 144 40 64 128 256), losses := [] }

theorem u2027 : Upper (D 1) (R 1) [304,80,34,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2028 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 138 144 96 77 141 269), lower := (rows 305 82 38 138 144 96 64 128 256), losses := [] }

theorem u2028 : Upper (D 1) (R 1) [304,80,34,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2029 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 82 38 140 144 33 74 202 330), lower := (rows 305 82 38 140 144 33 64 128 256), losses := [] }

theorem u2029 : Upper (D 1) (R 1) [304,80,34,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 140 144 34 73 201 329), lower := (rows 305 82 38 140 144 34 64 128 256), losses := [] }

theorem u2030 : Upper (D 1) (R 1) [304,80,34,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2030
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 82 38 140 144 40 67 195 323), lower := (rows 305 82 38 140 144 40 64 128 256), losses := [] }

theorem u2031 : Upper (D 1) (R 1) [304,80,34,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 38 140 144 96 75 139 267), lower := (rows 305 82 38 140 144 96 64 128 256), losses := [] }

theorem u2032 : Upper (D 1) (R 1) [304,80,34,132,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 82 44 138 144 33 70 198 326), lower := (rows 305 82 44 138 144 33 64 128 256), losses := [] }

theorem u2033 : Upper (D 1) (R 1) [304,80,40,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 44 138 144 34 69 197 325), lower := (rows 305 82 44 138 144 34 64 128 256), losses := [] }

theorem u2034 : Upper (D 1) (R 1) [304,80,40,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 82 44 138 144 36 67 195 323), lower := (rows 305 82 44 138 144 36 64 128 256), losses := [] }

theorem u2035 : Upper (D 1) (R 1) [304,80,40,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 7, camps := [], pairs := [(2,1)], upper := (rows 305 82 44 138 144 96 71 135 263), lower := (rows 305 82 44 138 144 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 152 98 64 128 256), good := (rows 305 112 60 188 144 96 96 144 256) }] }

theorem u2036 : Upper (D 1) (R 1) [304,80,40,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2037 : Route 9 := (fun mask => (mask,id))

def c2037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2037 : Upper (D 1) (R 1) [304,80,65,130,128,2] 13 := by
  apply FastRouting.sound _ _ [304,80,65,130,128,2] 13 (by decide) (choices 1) [4,8,32] r2037 c2037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u359
  · exact u360
  · exact u361

def b2038 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 82 69 138 144 36 106 170 298), lower := (rows 305 82 69 138 144 36 64 128 256), losses := [] }

theorem u2038 : Upper (D 1) (R 1) [304,80,65,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2038
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 82 69 138 144 40 102 166 294), lower := (rows 305 82 69 138 144 40 64 128 256), losses := [] }

theorem u2039 : Upper (D 1) (R 1) [304,80,65,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2039
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P01
