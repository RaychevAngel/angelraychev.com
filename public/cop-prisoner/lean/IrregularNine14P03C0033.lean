import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0005

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 35 69 88 176 36 201 137 393), lower := (rows 259 35 69 88 176 36 64 128 256), losses := [] }

theorem u1980 : Upper (D 3) (R 3) [258,33,65,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1980
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 69 88 176 40 197 133 389), lower := (rows 259 35 69 88 176 40 64 128 256), losses := [] }

theorem u1981 : Upper (D 3) (R 3) [258,33,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1981
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 69 88 176 160 77 141 269), lower := (rows 259 35 69 88 176 160 64 128 256), losses := [] }

theorem u1982 : Upper (D 3) (R 3) [258,33,65,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1982
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1983 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 259 35 69 104 145 36 216 152 408), lower := (rows 259 35 69 104 145 36 64 128 256), losses := [] }

theorem u1983 : Upper (D 3) (R 3) [258,33,65,96,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1983
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 148, camps := [], pairs := [], upper := (rows 259 35 69 104 145 40 212 148 404), lower := (rows 259 35 69 104 145 40 64 128 256), losses := [] }

theorem u1984 : Upper (D 3) (R 3) [258,33,65,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1984
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 140, camps := [], pairs := [], upper := (rows 259 35 69 104 145 48 204 140 396), lower := (rows 259 35 69 104 145 48 64 128 256), losses := [] }

theorem u1985 : Upper (D 3) (R 3) [258,33,65,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1985
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 69 104 145 160 92 156 284), lower := (rows 259 35 69 104 145 160 64 128 256), losses := [] }

theorem u1986 : Upper (D 3) (R 3) [258,33,65,96,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1986
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 104 148 33 216 152 408), lower := (rows 259 35 69 104 148 33 64 128 256), losses := [] }

theorem u1987 : Upper (D 3) (R 3) [258,33,65,96,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1987
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 69 104 148 40 209 145 401), lower := (rows 259 35 69 104 148 40 64 128 256), losses := [] }

theorem u1988 : Upper (D 3) (R 3) [258,33,65,96,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1988
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 35 69 104 148 48 201 137 393), lower := (rows 259 35 69 104 148 48 64 128 256), losses := [] }

theorem u1989 : Upper (D 3) (R 3) [258,33,65,96,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1989
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1990 : Route 9 := (fun mask => (mask,id))

def c1990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1990 : Upper (D 3) (R 3) [258,33,65,96,132,128] 13 := by
  apply FastRouting.sound _ _ [258,33,65,96,132,128] 13 (by decide) (choices 1) [1,8,16] r1990 c1990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u322
  · exact u323
  · exact u324

def b1991 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 104 152 33 212 148 404), lower := (rows 259 35 69 104 152 33 64 128 256), losses := [] }

theorem u1991 : Upper (D 3) (R 3) [258,33,65,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1991
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 69 104 152 36 209 145 401), lower := (rows 259 35 69 104 152 36 64 128 256), losses := [] }

theorem u1992 : Upper (D 3) (R 3) [258,33,65,96,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1992
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 69 104 152 48 197 133 389), lower := (rows 259 35 69 104 152 48 64 128 256), losses := [] }

theorem u1993 : Upper (D 3) (R 3) [258,33,65,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1993
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1994 : Route 9 := (fun mask => (mask,id))

def c1994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1994 : Upper (D 3) (R 3) [258,33,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [258,33,65,96,136,128] 13 (by decide) (choices 1) [1,4,16] r1994 c1994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u325
  · exact u326
  · exact u327

def b1995 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 259 35 69 137 208 36 120 184 312), lower := (rows 259 35 69 137 208 36 64 128 256), losses := [] }

theorem u1995 : Upper (D 3) (R 3) [258,33,65,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1995
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 259 35 69 137 208 48 108 172 300), lower := (rows 259 35 69 137 208 48 64 128 256), losses := [] }

theorem u1996 : Upper (D 3) (R 3) [258,33,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1996
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 140 176 33 88 216 344), lower := (rows 259 35 69 140 176 33 64 128 256), losses := [] }

theorem u1997 : Upper (D 3) (R 3) [258,33,65,132,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1997
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1998 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 259 35 69 140 176 40 81 209 337), lower := (rows 259 35 69 140 176 40 64 128 256), losses := [] }

theorem u1998 : Upper (D 3) (R 3) [258,33,65,132,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1998
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 259 35 69 140 176 48 73 201 329), lower := (rows 259 35 69 140 176 48 64 128 256), losses := [] }

theorem u1999 : Upper (D 3) (R 3) [258,33,65,132,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1999
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 259 35 69 140 176 96 89 153 281), lower := (rows 259 35 69 140 176 96 64 128 256), losses := [] }

theorem u2000 : Upper (D 3) (R 3) [258,33,65,132,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2000
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2001 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 140 208 33 120 184 312), lower := (rows 259 35 69 140 208 33 64 128 256), losses := [] }

theorem u2001 : Upper (D 3) (R 3) [258,33,65,132,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2001
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2002 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 35 69 140 208 40 113 177 305), lower := (rows 259 35 69 140 208 40 64 128 256), losses := [] }

theorem u2002 : Upper (D 3) (R 3) [258,33,65,132,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2002
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2003 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 35 69 140 208 48 105 169 297), lower := (rows 259 35 69 140 208 48 64 128 256), losses := [] }

theorem u2003 : Upper (D 3) (R 3) [258,33,65,132,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2003
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 168 208 33 92 156 284), lower := (rows 259 35 69 168 208 33 64 128 256), losses := [] }

theorem u2004 : Upper (D 3) (R 3) [258,33,65,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2004
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 259 35 69 168 208 36 89 153 281), lower := (rows 259 35 69 168 208 36 64 128 256), losses := [] }

theorem u2005 : Upper (D 3) (R 3) [258,33,65,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2005
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 259 35 69 168 208 40 85 149 277), lower := (rows 259 35 69 168 208 40 64 128 256), losses := [] }

theorem u2006 : Upper (D 3) (R 3) [258,33,65,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2006
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2007 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 259 35 69 168 208 48 77 141 269), lower := (rows 259 35 69 168 208 48 64 128 256), losses := [] }

theorem u2007 : Upper (D 3) (R 3) [258,33,65,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2007
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2008 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 168 208 33 85 149 277), lower := (rows 259 35 76 168 208 33 64 128 256), losses := [] }

theorem u2008 : Upper (D 3) (R 3) [258,33,72,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2008
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 35 76 168 208 36 81 145 273), lower := (rows 259 35 76 168 208 36 64 128 256), losses := [] }

theorem u2009 : Upper (D 3) (R 3) [258,33,72,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2009
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 35 76 168 208 48 69 133 261), lower := (rows 259 35 76 168 208 48 64 128 256), losses := [] }

theorem u2010 : Upper (D 3) (R 3) [258,33,72,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2010
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2011 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 13 88 145 33 224 224 480), lower := (rows 259 38 13 88 145 33 64 128 256), losses := [] }

theorem u2011 : Upper (D 3) (R 3) [258,36,9,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2011
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2012 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 88 145 96 225 161 417), lower := (rows 259 38 13 88 145 96 64 128 256), losses := [] }

theorem u2012 : Upper (D 3) (R 3) [258,36,9,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2012
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 13 88 145 160 97 225 353), lower := (rows 259 38 13 88 145 160 64 128 256), losses := [] }

theorem u2013 : Upper (D 3) (R 3) [258,36,9,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2013
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 13 200 81 33 240 176 432), lower := (rows 259 38 13 200 81 33 64 128 256), losses := [] }

theorem u2014 : Upper (D 3) (R 3) [258,36,9,192,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2014
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 13 200 81 48 225 161 417), lower := (rows 259 38 13 200 81 48 64 128 256), losses := [] }

theorem u2015 : Upper (D 3) (R 3) [258,36,9,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2015
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 13 200 81 160 113 177 305), lower := (rows 259 38 13 200 81 160 64 128 256), losses := [] }

theorem u2016 : Upper (D 3) (R 3) [258,36,9,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2016
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 13 200 112 33 209 145 401), lower := (rows 259 38 13 200 112 33 64 128 256), losses := [] }

theorem u2017 : Upper (D 3) (R 3) [258,36,9,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2017
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2018 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 13 200 112 48 193 129 385), lower := (rows 259 38 13 200 112 48 64 128 256), losses := [] }

theorem u2018 : Upper (D 3) (R 3) [258,36,9,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2018
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2019 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 13 200 112 160 81 145 273), lower := (rows 259 38 13 200 112 160 64 128 256), losses := [] }

theorem u2019 : Upper (D 3) (R 3) [258,36,9,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2019
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 224, camps := [], pairs := [(1,6)], upper := (rows 259 38 28 73 145 33 224 224 480), lower := (rows 259 38 28 73 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 57 0 128 256), good := (rows 291 38 62 41 177 33 0 128 256) }] }

theorem u2020 : Upper (D 3) (R 3) [258,36,24,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2020
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 73 145 96 225 161 417), lower := (rows 259 38 28 73 145 96 64 128 256), losses := [] }

theorem u2021 : Upper (D 3) (R 3) [258,36,24,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2021
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 25 152 33 224 224 480), lower := (rows 259 38 69 25 152 33 64 128 256), losses := [] }

theorem u2022 : Upper (D 3) (R 3) [258,36,65,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2022
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 25 152 96 225 161 417), lower := (rows 259 38 69 25 152 96 64 128 256), losses := [] }

theorem u2023 : Upper (D 3) (R 3) [258,36,65,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2023
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 25 152 160 97 225 353), lower := (rows 259 38 69 25 152 160 64 128 256), losses := [] }

theorem u2024 : Upper (D 3) (R 3) [258,36,65,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2024
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 25 208 33 232 168 424), lower := (rows 259 38 69 25 208 33 64 128 256), losses := [] }

theorem u2025 : Upper (D 3) (R 3) [258,36,65,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2025
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 69 25 208 40 225 161 417), lower := (rows 259 38 69 25 208 40 64 128 256), losses := [] }

theorem u2026 : Upper (D 3) (R 3) [258,36,65,17,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2027 : Route 9 := (fun mask => (mask,id))

def c2027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2027 : Upper (D 3) (R 3) [258,36,65,17,192,128] 13 := by
  apply FastRouting.sound _ _ [258,36,65,17,192,128] 13 (by decide) (choices 1) [1,8,32] r2027 c2027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u328
  · exact u329
  · exact u330

def b2028 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 56 145 33 200 200 456), lower := (rows 259 38 69 56 145 33 64 128 256), losses := [] }

theorem u2028 : Upper (D 3) (R 3) [258,36,65,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2029 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 38 69 56 145 40 193 193 449), lower := (rows 259 38 69 56 145 40 64 128 256), losses := [] }

theorem u2029 : Upper (D 3) (R 3) [258,36,65,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 56 145 96 201 137 393), lower := (rows 259 38 69 56 145 96 64 128 256), losses := [] }

theorem u2030 : Upper (D 3) (R 3) [258,36,65,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 56 145 160 73 201 329), lower := (rows 259 38 69 56 145 160 64 128 256), losses := [] }

theorem u2031 : Upper (D 3) (R 3) [258,36,65,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2031
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 56 208 33 201 137 393), lower := (rows 259 38 69 56 208 33 64 128 256), losses := [] }

theorem u2032 : Upper (D 3) (R 3) [258,36,65,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2032
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 69 56 208 40 193 129 385), lower := (rows 259 38 69 56 208 40 64 128 256), losses := [] }

theorem u2033 : Upper (D 3) (R 3) [258,36,65,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 56 208 160 73 137 265), lower := (rows 259 38 69 56 208 160 64 128 256), losses := [] }

theorem u2034 : Upper (D 3) (R 3) [258,36,65,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2034
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 88 145 33 232 168 424), lower := (rows 259 38 69 88 145 33 64 128 256), losses := [] }

theorem u2035 : Upper (D 3) (R 3) [258,36,65,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2035
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 69 88 145 40 225 161 417), lower := (rows 259 38 69 88 145 40 64 128 256), losses := [] }

theorem u2036 : Upper (D 3) (R 3) [258,36,65,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2036
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2037 : Route 9 := (fun mask => (mask,id))

def c2037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2037 : Upper (D 3) (R 3) [258,36,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [258,36,65,80,129,128] 13 (by decide) (choices 1) [1,8,32] r2037 c2037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u331
  · exact u332
  · exact u333

def b2038 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 88 176 33 201 137 393), lower := (rows 259 38 69 88 176 33 64 128 256), losses := [] }

theorem u2038 : Upper (D 3) (R 3) [258,36,65,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2038
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 69 88 176 40 193 129 385), lower := (rows 259 38 69 88 176 40 64 128 256), losses := [] }

theorem u2039 : Upper (D 3) (R 3) [258,36,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2039
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P03
