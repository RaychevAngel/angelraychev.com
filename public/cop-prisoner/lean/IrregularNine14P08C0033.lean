import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1980 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 67 164 200 304 36 89 153 281), lower := (rows 35 67 164 200 304 36 64 128 256), losses := [] }

theorem u1980 : Upper (D 8) (R 8) [34,65,160,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1980 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1981 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 164 200 304 40 85 149 277), lower := (rows 35 67 164 200 304 40 64 128 256), losses := [] }

theorem u1981 : Upper (D 8) (R 8) [34,65,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1981 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1982 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 67 164 200 304 48 77 141 269), lower := (rows 35 67 164 200 304 48 64 128 256), losses := [] }

theorem u1982 : Upper (D 8) (R 8) [34,65,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1982 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1983 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 56 400 33 224 224 480), lower := (rows 35 70 13 56 400 33 64 128 256), losses := [] }

theorem u1983 : Upper (D 8) (R 8) [34,68,9,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1984 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 56 400 96 225 161 417), lower := (rows 35 70 13 56 400 96 64 128 256), losses := [] }

theorem u1984 : Upper (D 8) (R 8) [34,68,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1985 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 56 400 160 97 225 353), lower := (rows 35 70 13 56 400 160 64 128 256), losses := [] }

theorem u1985 : Upper (D 8) (R 8) [34,68,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1986 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 152 304 33 224 224 480), lower := (rows 35 70 13 152 304 33 64 128 256), losses := [] }

theorem u1986 : Upper (D 8) (R 8) [34,68,9,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1987 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 152 304 96 225 161 417), lower := (rows 35 70 13 152 304 96 64 128 256), losses := [] }

theorem u1987 : Upper (D 8) (R 8) [34,68,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1988 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 13 152 304 160 97 225 353), lower := (rows 35 70 13 152 304 160 64 128 256), losses := [] }

theorem u1988 : Upper (D 8) (R 8) [34,68,9,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1989 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 112 33 464 400 400), lower := (rows 35 70 13 168 112 33 64 128 256), losses := [] }

theorem u1989 : Upper (D 8) (R 8) [34,68,9,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1990 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 70 13 168 112 48 449 385 385), lower := (rows 35 70 13 168 112 48 64 128 256), losses := [] }

theorem u1990 : Upper (D 8) (R 8) [34,68,9,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1990 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1991 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 168 112 160 337 401 273), lower := (rows 35 70 13 168 112 160 64 128 256), losses := [] }

theorem u1991 : Upper (D 8) (R 8) [34,68,9,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1992 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 13 168 112 288 209 145 401), lower := (rows 35 70 13 168 112 288 64 128 256), losses := [] }

theorem u1992 : Upper (D 8) (R 8) [34,68,9,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1992 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1993 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 208 33 368 432 304), lower := (rows 35 70 13 168 208 33 64 128 256), losses := [] }

theorem u1993 : Upper (D 8) (R 8) [34,68,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1994 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 70 13 168 208 48 353 417 289), lower := (rows 35 70 13 168 208 48 64 128 256), losses := [] }

theorem u1994 : Upper (D 8) (R 8) [34,68,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1994 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1995 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 13 168 208 288 113 177 305), lower := (rows 35 70 13 168 208 288 64 128 256), losses := [] }

theorem u1995 : Upper (D 8) (R 8) [34,68,9,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1995 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1996 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 304 33 208 208 464), lower := (rows 35 70 13 168 304 33 64 128 256), losses := [] }

theorem u1996 : Upper (D 8) (R 8) [34,68,9,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1997 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 13 168 304 48 193 193 449), lower := (rows 35 70 13 168 304 48 64 128 256), losses := [] }

theorem u1997 : Upper (D 8) (R 8) [34,68,9,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1997 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1998 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 168 304 96 209 145 401), lower := (rows 35 70 13 168 304 96 64 128 256), losses := [] }

theorem u1998 : Upper (D 8) (R 8) [34,68,9,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1999 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 168 304 160 81 209 337), lower := (rows 35 70 13 168 304 160 64 128 256), losses := [] }

theorem u1999 : Upper (D 8) (R 8) [34,68,9,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2000 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 336 33 240 176 432), lower := (rows 35 70 13 168 336 33 64 128 256), losses := [] }

theorem u2000 : Upper (D 8) (R 8) [34,68,9,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2001 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 13 168 336 48 225 161 417), lower := (rows 35 70 13 168 336 48 64 128 256), losses := [] }

theorem u2001 : Upper (D 8) (R 8) [34,68,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2001 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2002 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 168 336 160 113 177 305), lower := (rows 35 70 13 168 336 160 64 128 256), losses := [] }

theorem u2002 : Upper (D 8) (R 8) [34,68,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2003 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 400 33 112 240 368), lower := (rows 35 70 13 168 400 33 64 128 256), losses := [] }

theorem u2003 : Upper (D 8) (R 8) [34,68,9,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2004 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 13 168 400 48 97 225 353), lower := (rows 35 70 13 168 400 48 64 128 256), losses := [] }

theorem u2004 : Upper (D 8) (R 8) [34,68,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2004 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2005 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 168 400 96 113 177 305), lower := (rows 35 70 13 168 400 96 64 128 256), losses := [] }

theorem u2005 : Upper (D 8) (R 8) [34,68,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2006 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 280 176 33 224 224 480), lower := (rows 35 70 13 280 176 33 64 128 256), losses := [] }

theorem u2006 : Upper (D 8) (R 8) [34,68,9,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2007 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 280 176 96 225 161 417), lower := (rows 35 70 13 280 176 96 64 128 256), losses := [] }

theorem u2007 : Upper (D 8) (R 8) [34,68,9,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2008 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 280 176 160 97 225 353), lower := (rows 35 70 13 280 176 160 64 128 256), losses := [] }

theorem u2008 : Upper (D 8) (R 8) [34,68,9,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2009 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 296 112 33 208 144 400), lower := (rows 35 70 13 296 112 33 64 128 256), losses := [] }

theorem u2009 : Upper (D 8) (R 8) [34,68,9,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2010 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 13 296 112 48 193 129 385), lower := (rows 35 70 13 296 112 48 64 128 256), losses := [] }

theorem u2010 : Upper (D 8) (R 8) [34,68,9,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2010 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2011 : Route 9 := (fun mask => (mask,id))

def c2011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2011 : Upper (D 8) (R 8) [34,68,9,288,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,96,128] 13 (by decide) (choices 1) [1,16,128] r2011 c2011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u273
  · exact u274
  · exact u275

def b2012 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 296 176 33 208 208 464), lower := (rows 35 70 13 296 176 33 64 128 256), losses := [] }

theorem u2012 : Upper (D 8) (R 8) [34,68,9,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2013 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 13 296 176 48 193 193 449), lower := (rows 35 70 13 296 176 48 64 128 256), losses := [] }

theorem u2013 : Upper (D 8) (R 8) [34,68,9,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2013 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2014 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 296 176 96 209 145 401), lower := (rows 35 70 13 296 176 96 64 128 256), losses := [] }

theorem u2014 : Upper (D 8) (R 8) [34,68,9,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2015 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 296 176 160 81 209 337), lower := (rows 35 70 13 296 176 160 64 128 256), losses := [] }

theorem u2015 : Upper (D 8) (R 8) [34,68,9,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2016 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 296 208 33 240 176 432), lower := (rows 35 70 13 296 208 33 64 128 256), losses := [] }

theorem u2016 : Upper (D 8) (R 8) [34,68,9,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2017 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 13 296 208 48 225 161 417), lower := (rows 35 70 13 296 208 48 64 128 256), losses := [] }

theorem u2017 : Upper (D 8) (R 8) [34,68,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2017 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2018 : Route 9 := (fun mask => (mask,id))

def c2018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2018 : Upper (D 8) (R 8) [34,68,9,288,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,192,128] 13 (by decide) (choices 1) [1,16,32] r2018 c2018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u276
  · exact u277
  · exact u278

def b2019 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 392 112 33 240 176 432), lower := (rows 35 70 13 392 112 33 64 128 256), losses := [] }

theorem u2019 : Upper (D 8) (R 8) [34,68,9,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2020 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 13 392 112 48 225 161 417), lower := (rows 35 70 13 392 112 48 64 128 256), losses := [] }

theorem u2020 : Upper (D 8) (R 8) [34,68,9,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2020 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2021 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 13 392 112 160 113 177 305), lower := (rows 35 70 13 392 112 160 64 128 256), losses := [] }

theorem u2021 : Upper (D 8) (R 8) [34,68,9,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2022 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 392 176 33 112 240 368), lower := (rows 35 70 13 392 176 33 64 128 256), losses := [] }

theorem u2022 : Upper (D 8) (R 8) [34,68,9,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2023 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 13 392 176 48 97 225 353), lower := (rows 35 70 13 392 176 48 64 128 256), losses := [] }

theorem u2023 : Upper (D 8) (R 8) [34,68,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2023 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2024 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 392 176 96 113 177 305), lower := (rows 35 70 13 392 176 96 64 128 256), losses := [] }

theorem u2024 : Upper (D 8) (R 8) [34,68,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2025 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 392 208 33 112 176 304), lower := (rows 35 70 13 392 208 33 64 128 256), losses := [] }

theorem u2025 : Upper (D 8) (R 8) [34,68,9,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2026 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 13 392 208 48 97 161 289), lower := (rows 35 70 13 392 208 48 64 128 256), losses := [] }

theorem u2026 : Upper (D 8) (R 8) [34,68,9,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2026 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2027 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 137 304 33 224 224 480), lower := (rows 35 70 28 137 304 33 64 128 256), losses := [] }

theorem u2027 : Upper (D 8) (R 8) [34,68,24,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2028 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 28 137 304 96 225 161 417), lower := (rows 35 70 28 137 304 96 64 128 256), losses := [] }

theorem u2028 : Upper (D 8) (R 8) [34,68,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2029 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 28 137 304 160 97 225 353), lower := (rows 35 70 28 137 304 160 64 128 256), losses := [] }

theorem u2029 : Upper (D 8) (R 8) [34,68,24,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2030 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 168 273 33 224 224 480), lower := (rows 35 70 28 168 273 33 64 128 256), losses := [] }

theorem u2030 : Upper (D 8) (R 8) [34,68,24,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2031 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 28 168 273 96 225 161 417), lower := (rows 35 70 28 168 273 96 64 128 256), losses := [] }

theorem u2031 : Upper (D 8) (R 8) [34,68,24,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2032 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 168 273 160 97 225 353), lower := (rows 35 70 28 168 273 160 64 128 256), losses := [] }

theorem u2032 : Upper (D 8) (R 8) [34,68,24,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2033 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 168 304 33 193 193 449), lower := (rows 35 70 28 168 304 33 64 128 256), losses := [] }

theorem u2033 : Upper (D 8) (R 8) [34,68,24,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2034 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 28 168 304 96 193 129 385), lower := (rows 35 70 28 168 304 96 64 128 256), losses := [] }

theorem u2034 : Upper (D 8) (R 8) [34,68,24,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2035 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 168 304 160 65 193 321), lower := (rows 35 70 28 168 304 160 64 128 256), losses := [] }

theorem u2035 : Upper (D 8) (R 8) [34,68,24,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2036 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 25 400 33 224 224 480), lower := (rows 35 70 44 25 400 33 64 128 256), losses := [] }

theorem u2036 : Upper (D 8) (R 8) [34,68,40,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2037 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 25 400 96 225 161 417), lower := (rows 35 70 44 25 400 96 64 128 256), losses := [] }

theorem u2037 : Upper (D 8) (R 8) [34,68,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2038 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 25 400 160 97 225 353), lower := (rows 35 70 44 25 400 160 64 128 256), losses := [] }

theorem u2038 : Upper (D 8) (R 8) [34,68,40,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2039 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 112 33 464 400 400), lower := (rows 35 70 44 137 112 33 64 128 256), losses := [] }

theorem u2039 : Upper (D 8) (R 8) [34,68,40,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2039
end Delivery.IrregularNine14.P08
