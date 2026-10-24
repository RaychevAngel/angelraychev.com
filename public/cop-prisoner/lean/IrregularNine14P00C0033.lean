import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0012
import IrregularNine14P00C0013

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 275 38 69 88 24 161 225 161 417), lower := (rows 275 38 69 88 24 32 64 128 256), losses := [] }

theorem u1980 : Upper (D 0) (R 0) [274,36,65,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1980
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 88 48 169 201 137 393), lower := (rows 275 38 69 88 48 32 64 128 256), losses := [] }

theorem u1981 : Upper (D 0) (R 0) [274,36,65,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1981
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1982 : Route 9 := (fun mask => (mask,id))

def c1982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1982 : Upper (D 0) (R 0) [274,36,65,80,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,80,128] 13 (by decide) (choices 1) [1,8,128] r1982 c1982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u767
  · exact u768
  · exact u769

def b1983 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 69 104 17 184 216 152 408), lower := (rows 275 38 69 104 17 32 64 128 256), losses := [] }

theorem u1983 : Upper (D 0) (R 0) [274,36,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1983
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 38 69 104 24 177 209 145 401), lower := (rows 275 38 69 104 24 32 64 128 256), losses := [] }

theorem u1984 : Upper (D 0) (R 0) [274,36,65,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1984
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1985 : Route 9 := (fun mask => (mask,id))

def c1985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1985 : Upper (D 0) (R 0) [274,36,65,96,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,96,128] 13 (by decide) (choices 1) [1,8,16,128] r1985 c1985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u770
  · exact u771
  · exact u772
  · exact u773

def b1986 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 275 38 69 137 24 240 240 240 496), lower := (rows 275 38 69 137 24 32 64 128 256), losses := [] }

theorem u1986 : Upper (D 0) (R 0) [274,36,65,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1986
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 137 48 248 216 216 472), lower := (rows 275 38 69 137 48 32 64 128 256), losses := [] }

theorem u1987 : Upper (D 0) (R 0) [274,36,65,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1987
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 137 80 184 248 184 440), lower := (rows 275 38 69 137 80 32 64 128 256), losses := [] }

theorem u1988 : Upper (D 0) (R 0) [274,36,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1988
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1989 : Route 9 := (fun mask => (mask,id))

def c1989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1989 : Upper (D 0) (R 0) [274,36,65,129,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,129,128] 13 (by decide) (choices 1) [8,16,64] r1989 c1989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u774
  · exact u775
  · exact u776

def b1990 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 69 152 17 232 232 232 488), lower := (rows 275 38 69 152 17 32 64 128 256), losses := [] }

theorem u1990 : Upper (D 0) (R 0) [274,36,65,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1990
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 38 69 152 24 225 225 225 481), lower := (rows 275 38 69 152 24 32 64 128 256), losses := [] }

theorem u1991 : Upper (D 0) (R 0) [274,36,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1991
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 152 48 233 201 201 457), lower := (rows 275 38 69 152 48 32 64 128 256), losses := [] }

theorem u1992 : Upper (D 0) (R 0) [274,36,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1992
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 152 80 169 233 169 425), lower := (rows 275 38 69 152 80 32 64 128 256), losses := [] }

theorem u1993 : Upper (D 0) (R 0) [274,36,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1993
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 69 152 144 105 105 233 361), lower := (rows 275 38 69 152 144 32 64 128 256), losses := [] }

theorem u1994 : Upper (D 0) (R 0) [274,36,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1994
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 69 168 17 248 216 216 472), lower := (rows 275 38 69 168 17 32 64 128 256), losses := [] }

theorem u1995 : Upper (D 0) (R 0) [274,36,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1995
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 38 69 168 24 241 209 209 465), lower := (rows 275 38 69 168 24 32 64 128 256), losses := [] }

theorem u1996 : Upper (D 0) (R 0) [274,36,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1996
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 168 80 185 217 153 409), lower := (rows 275 38 69 168 80 32 64 128 256), losses := [] }

theorem u1997 : Upper (D 0) (R 0) [274,36,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1997
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1998 : Route 9 := (fun mask => (mask,id))

def c1998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1998 : Upper (D 0) (R 0) [274,36,65,160,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,160,128] 13 (by decide) (choices 1) [1,8,16,64] r1998 c1998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u777
  · exact u778
  · exact u779
  · exact u780

def b1999 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 69 200 17 184 248 184 440), lower := (rows 275 38 69 200 17 32 64 128 256), losses := [] }

theorem u1999 : Upper (D 0) (R 0) [274,36,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1999
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 275 38 69 200 24 177 241 177 433), lower := (rows 275 38 69 200 24 32 64 128 256), losses := [] }

theorem u2000 : Upper (D 0) (R 0) [274,36,65,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2000
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2001 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 200 48 185 217 153 409), lower := (rows 275 38 69 200 48 32 64 128 256), losses := [] }

theorem u2001 : Upper (D 0) (R 0) [274,36,65,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2001
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2002 : Route 9 := (fun mask => (mask,id))

def c2002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2002 : Upper (D 0) (R 0) [274,36,65,192,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,192,128] 13 (by decide) (choices 1) [1,8,16] r2002 c2002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u781
  · exact u782
  · exact u783

def b2003 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 275 38 76 137 17 240 240 240 496), lower := (rows 275 38 76 137 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 49 81 145 273), good := (rows 498 38 78 494 496 32 64 128 256) }] }

theorem u2003 : Upper (D 0) (R 0) [274,36,72,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2003
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 76 137 48 241 209 209 465), lower := (rows 275 38 76 137 48 32 64 128 256), losses := [] }

theorem u2004 : Upper (D 0) (R 0) [274,36,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2004
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 76 137 80 177 241 177 433), lower := (rows 275 38 76 137 80 32 64 128 256), losses := [] }

theorem u2005 : Upper (D 0) (R 0) [274,36,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2005
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 113, camps := [], pairs := [(1,7)], upper := (rows 275 38 76 137 144 113 113 241 369), lower := (rows 275 38 76 137 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 33 65 0 257), good := (rows 371 38 78 367 16 32 64 0 256) }] }

theorem u2006 : Upper (D 0) (R 0) [274,36,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2006
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2007 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 275 38 76 152 17 225 225 225 481), lower := (rows 275 38 76 152 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 81 145 273), good := (rows 483 38 78 494 481 32 64 128 256) }] }

theorem u2007 : Upper (D 0) (R 0) [274,36,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2007
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2008 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 76 152 48 225 193 193 449), lower := (rows 275 38 76 152 48 32 64 128 256), losses := [] }

theorem u2008 : Upper (D 0) (R 0) [274,36,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2008
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 76 152 80 161 225 161 417), lower := (rows 275 38 76 152 80 32 64 128 256), losses := [] }

theorem u2009 : Upper (D 0) (R 0) [274,36,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2009
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 76 152 144 97 97 225 353), lower := (rows 275 38 76 152 144 32 64 128 256), losses := [] }

theorem u2010 : Upper (D 0) (R 0) [274,36,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2010
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2011 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2011 : Upper (D 0) (R 0) [274,36,192,48,1] 13 := by
  apply FastRouting.sound _ _ [274,36,192,48,1] 13 (by decide) (choices 1) [1,8,64] r2011 c2011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u784
  · exact u785
  · exact u786

def b2012 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 38 196 56 24 225 193 193 449), lower := (rows 275 38 196 56 24 32 64 128 256), losses := [] }

theorem u2012 : Upper (D 0) (R 0) [274,36,192,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2012
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 196 56 80 169 201 137 393), lower := (rows 275 38 196 56 80 32 64 128 256), losses := [] }

theorem u2013 : Upper (D 0) (R 0) [274,36,192,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2013
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2014 : Route 9 := (fun mask => (mask,id))

def c2014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2014 : Upper (D 0) (R 0) [274,36,192,65,1] 13 := by
  apply FastRouting.sound _ _ [274,36,192,65,1] 13 (by decide) (choices 1) [8,16,128] r2014 c2014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u787
  · exact u788
  · exact u789

def b2015 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 275 38 196 73 24 177 241 177 433), lower := (rows 275 38 196 73 24 32 64 128 256), losses := [] }

theorem u2015 : Upper (D 0) (R 0) [274,36,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2015
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 196 73 48 185 217 153 409), lower := (rows 275 38 196 73 48 32 64 128 256), losses := [] }

theorem u2016 : Upper (D 0) (R 0) [274,36,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2016
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 275 38 196 73 144 57 121 185 313), lower := (rows 275 38 196 73 144 32 64 128 256), losses := [] }

theorem u2017 : Upper (D 0) (R 0) [274,36,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2017
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2018 : Route 9 := (fun mask => (mask,id))

def c2018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2018 : Upper (D 0) (R 0) [274,36,192,80,1] 13 := by
  apply FastRouting.sound _ _ [274,36,192,80,1] 13 (by decide) (choices 1) [1,8,128] r2018 c2018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u790
  · exact u791
  · exact u792

def b2019 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 275 38 196 88 24 161 225 161 417), lower := (rows 275 38 196 88 24 32 64 128 256), losses := [] }

theorem u2019 : Upper (D 0) (R 0) [274,36,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2019
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 196 88 48 169 201 137 393), lower := (rows 275 38 196 88 48 32 64 128 256), losses := [] }

theorem u2020 : Upper (D 0) (R 0) [274,36,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2020
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 196 88 144 41 105 169 297), lower := (rows 275 38 196 88 144 32 64 128 256), losses := [] }

theorem u2021 : Upper (D 0) (R 0) [274,36,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2021
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2022 : Route 9 := (fun mask => (mask,id))

def c2022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2022 : Upper (D 0) (R 0) [274,36,192,96,1] 13 := by
  apply FastRouting.sound _ _ [274,36,192,96,1] 13 (by decide) (choices 1) [1,8,16,128] r2022 c2022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u793
  · exact u794
  · exact u795
  · exact u796

def b2023 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 38 196 104 24 177 209 145 401), lower := (rows 275 38 196 104 24 32 64 128 256), losses := [] }

theorem u2023 : Upper (D 0) (R 0) [274,36,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2023
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 275 38 196 104 144 57 89 153 281), lower := (rows 275 38 196 104 144 32 64 128 256), losses := [] }

theorem u2024 : Upper (D 0) (R 0) [274,36,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2024
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 13 140 17 240 240 240 496), lower := (rows 275 98 13 140 17 32 64 128 256), losses := [] }

theorem u2025 : Upper (D 0) (R 0) [274,96,9,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2025
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 13 140 48 241 209 209 465), lower := (rows 275 98 13 140 48 32 64 128 256), losses := [] }

theorem u2026 : Upper (D 0) (R 0) [274,96,9,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2026
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2027 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 13 140 144 113 113 241 369), lower := (rows 275 98 13 140 144 32 64 128 256), losses := [] }

theorem u2027 : Upper (D 0) (R 0) [274,96,9,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2027
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2028 : Route 9 := (fun mask => (mask,id))

def c2028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2028 : Upper (D 0) (R 0) [274,96,9,160,1] 13 := by
  apply FastRouting.sound _ _ [274,96,9,160,1] 13 (by decide) (choices 1) [4,16,64,128] r2028 c2028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u797
  · exact u798
  · exact u799
  · exact u800

def b2029 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 98 13 168 20 241 209 209 465), lower := (rows 275 98 13 168 20 32 64 128 256), losses := [] }

theorem u2029 : Upper (D 0) (R 0) [274,96,9,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2029
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 13 168 80 181 213 149 405), lower := (rows 275 98 13 168 80 32 64 128 256), losses := [] }

theorem u2030 : Upper (D 0) (R 0) [274,96,9,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2030
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2031 : Route 9 := (fun mask => (mask,id))

def c2031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2031 : Upper (D 0) (R 0) [274,96,9,160,128] 13 := by
  apply FastRouting.sound _ _ [274,96,9,160,128] 13 (by decide) (choices 1) [1,4,16,64] r2031 c2031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u801
  · exact u802
  · exact u803
  · exact u804

def b2032 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 28 137 17 228 228 228 484), lower := (rows 275 98 28 137 17 32 64 128 256), losses := [] }

theorem u2032 : Upper (D 0) (R 0) [274,96,24,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2032
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 98 28 137 20 225 225 225 481), lower := (rows 275 98 28 137 20 32 64 128 256), losses := [] }

theorem u2033 : Upper (D 0) (R 0) [274,96,24,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2033
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 28 137 48 229 197 197 453), lower := (rows 275 98 28 137 48 32 64 128 256), losses := [] }

theorem u2034 : Upper (D 0) (R 0) [274,96,24,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2034
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 28 137 144 101 101 229 357), lower := (rows 275 98 28 137 144 32 64 128 256), losses := [] }

theorem u2035 : Upper (D 0) (R 0) [274,96,24,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2035
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2036 : Route 9 := (fun mask => (mask,id))

def c2036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2036 : Upper (D 0) (R 0) [274,96,24,160,1] 13 := by
  apply FastRouting.sound _ _ [274,96,24,160,1] 13 (by decide) (choices 1) [1,4,64,128] r2036 c2036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u805
  · exact u806
  · exact u807
  · exact u808

def b2037 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 98 28 168 20 225 193 193 449), lower := (rows 275 98 28 168 20 32 64 128 256), losses := [] }

theorem u2037 : Upper (D 0) (R 0) [274,96,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2037
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2038 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 28 168 80 165 197 133 389), lower := (rows 275 98 28 168 80 32 64 128 256), losses := [] }

theorem u2038 : Upper (D 0) (R 0) [274,96,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2038
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 28 168 144 101 69 197 325), lower := (rows 275 98 28 168 144 32 64 128 256), losses := [] }

theorem u2039 : Upper (D 0) (R 0) [274,96,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2039
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P00
