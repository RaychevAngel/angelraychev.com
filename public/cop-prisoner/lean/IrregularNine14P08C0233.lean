import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0079

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13980 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 296 146 177 241 177 433), lower := (rows 97 14 69 296 146 32 64 128 256), losses := [] }

theorem u13980 : Upper (D 8) (R 8) [96,12,65,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13981 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 296 176 179 211 147 403), lower := (rows 97 14 69 296 176 32 64 128 256), losses := [] }

theorem u13981 : Upper (D 8) (R 8) [96,12,65,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13982 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 392 50 177 241 177 433), lower := (rows 97 14 69 392 50 32 64 128 256), losses := [] }

theorem u13982 : Upper (D 8) (R 8) [96,12,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13983 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 392 145 50 114 178 306), lower := (rows 97 14 69 392 145 32 64 128 256), losses := [] }

theorem u13983 : Upper (D 8) (R 8) [96,12,65,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13984 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 392 176 51 115 179 307), lower := (rows 97 14 69 392 176 32 64 128 256), losses := [] }

theorem u13984 : Upper (D 8) (R 8) [96,12,65,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13985 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 137 176 305 369 433 305), lower := (rows 97 14 70 137 176 32 64 128 256), losses := [] }

theorem u13985 : Upper (D 8) (R 8) [96,12,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13986 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 137 273 176 240 176 432), lower := (rows 97 14 70 137 273 32 64 128 256), losses := [] }

theorem u13986 : Upper (D 8) (R 8) [96,12,66,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13987 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 137 304 177 241 177 433), lower := (rows 97 14 70 137 304 32 64 128 256), losses := [] }

theorem u13987 : Upper (D 8) (R 8) [96,12,66,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13988 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 137 400 49 113 177 305), lower := (rows 97 14 70 137 400 32 64 128 256), losses := [] }

theorem u13988 : Upper (D 8) (R 8) [96,12,66,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13989 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 152 273 161 225 161 417), lower := (rows 97 14 70 152 273 32 64 128 256), losses := [] }

theorem u13989 : Upper (D 8) (R 8) [96,12,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13990 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 152 304 161 225 161 417), lower := (rows 97 14 70 152 304 32 64 128 256), losses := [] }

theorem u13990 : Upper (D 8) (R 8) [96,12,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13991 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 168 145 305 369 433 305), lower := (rows 97 14 70 168 145 32 64 128 256), losses := [] }

theorem u13991 : Upper (D 8) (R 8) [96,12,66,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13992 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 168 273 177 241 177 433), lower := (rows 97 14 70 168 273 32 64 128 256), losses := [] }

theorem u13992 : Upper (D 8) (R 8) [96,12,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13993 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 168 304 177 209 145 401), lower := (rows 97 14 70 168 304 32 64 128 256), losses := [] }

theorem u13993 : Upper (D 8) (R 8) [96,12,66,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13994 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 168 400 49 113 177 305), lower := (rows 97 14 70 168 400 32 64 128 256), losses := [] }

theorem u13994 : Upper (D 8) (R 8) [96,12,66,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13995 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 265 145 176 240 176 432), lower := (rows 97 14 70 265 145 32 64 128 256), losses := [] }

theorem u13995 : Upper (D 8) (R 8) [96,12,66,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13996 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 265 176 177 241 177 433), lower := (rows 97 14 70 265 176 32 64 128 256), losses := [] }

theorem u13996 : Upper (D 8) (R 8) [96,12,66,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13997 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 280 145 161 225 161 417), lower := (rows 97 14 70 280 145 32 64 128 256), losses := [] }

theorem u13997 : Upper (D 8) (R 8) [96,12,66,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13998 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 280 176 161 225 161 417), lower := (rows 97 14 70 280 176 32 64 128 256), losses := [] }

theorem u13998 : Upper (D 8) (R 8) [96,12,66,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13999 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 296 145 177 241 177 433), lower := (rows 97 14 70 296 145 32 64 128 256), losses := [] }

theorem u13999 : Upper (D 8) (R 8) [96,12,66,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14000 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 296 176 177 209 145 401), lower := (rows 97 14 70 296 176 32 64 128 256), losses := [] }

theorem u14000 : Upper (D 8) (R 8) [96,12,66,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14001 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 392 145 49 113 177 305), lower := (rows 97 14 70 392 145 32 64 128 256), losses := [] }

theorem u14001 : Upper (D 8) (R 8) [96,12,66,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14002 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 392 176 49 113 177 305), lower := (rows 97 14 70 392 176 32 64 128 256), losses := [] }

theorem u14002 : Upper (D 8) (R 8) [96,12,66,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14003 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 20, targets := 128 }], pairs := [(2,7)], upper := (rows 97 14 84 137 49 418 482 418 418), lower := (rows 97 14 84 137 49 32 64 128 256), losses := [] }

theorem u14003 : Upper (D 8) (R 8) [96,12,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14004 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 137 50 417 481 417 417), lower := (rows 97 14 84 137 50 32 64 128 256), losses := [] }

theorem u14004 : Upper (D 8) (R 8) [96,12,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14005 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 84 137 145 290 354 418 290), lower := (rows 97 14 84 137 145 32 64 128 256), losses := [] }

theorem u14005 : Upper (D 8) (R 8) [96,12,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14006 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 137 146 289 353 417 289), lower := (rows 97 14 84 137 146 32 64 128 256), losses := [] }

theorem u14006 : Upper (D 8) (R 8) [96,12,80,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14007 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 137 176 291 355 419 291), lower := (rows 97 14 84 137 176 32 64 128 256), losses := [] }

theorem u14007 : Upper (D 8) (R 8) [96,12,80,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14008 : Route 9 := (fun mask => (mask,id))

def c14008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14008 : Upper (D 8) (R 8) [96,12,80,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,80,129,257] 13 (by decide) (choices 1) [2,128] r14008 c14008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4748
  · exact u4749

def b14009 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 137 274 161 225 161 417), lower := (rows 97 14 84 137 274 32 64 128 256), losses := [] }

theorem u14009 : Upper (D 8) (R 8) [96,12,80,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14010 : Route 9 := (fun mask => (mask,id))

def c14010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14010 : Upper (D 8) (R 8) [96,12,80,129,288] 13 := by
  apply FastRouting.sound _ _ [96,12,80,129,288] 13 (by decide) (choices 1) [1,2,128] r14010 c14010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4750
  · exact u4751
  · exact u4752

def b14011 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 137 400 35 99 163 291), lower := (rows 97 14 84 137 400 32 64 128 256), losses := [] }

theorem u14011 : Upper (D 8) (R 8) [96,12,80,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14012 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 138 145 289 353 417 289), lower := (rows 97 14 84 138 145 32 64 128 256), losses := [] }

theorem u14012 : Upper (D 8) (R 8) [96,12,80,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14013 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 138 176 289 353 417 289), lower := (rows 97 14 84 138 176 32 64 128 256), losses := [] }

theorem u14013 : Upper (D 8) (R 8) [96,12,80,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14014 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 84 138 273 161 225 161 417), lower := (rows 97 14 84 138 273 32 64 128 256), losses := [] }

theorem u14014 : Upper (D 8) (R 8) [96,12,80,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14015 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 84 138 304 161 225 161 417), lower := (rows 97 14 84 138 304 32 64 128 256), losses := [] }

theorem u14015 : Upper (D 8) (R 8) [96,12,80,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14016 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 138 400 33 97 161 289), lower := (rows 97 14 84 138 400 32 64 128 256), losses := [] }

theorem u14016 : Upper (D 8) (R 8) [96,12,80,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14017 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 20, targets := 128 }], pairs := [(2,7)], upper := (rows 97 14 84 168 49 419 451 387 387), lower := (rows 97 14 84 168 49 32 64 128 256), losses := [] }

theorem u14017 : Upper (D 8) (R 8) [96,12,80,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14018 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 168 50 417 449 385 385), lower := (rows 97 14 84 168 50 32 64 128 256), losses := [] }

theorem u14018 : Upper (D 8) (R 8) [96,12,80,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14019 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 145 291 355 419 291), lower := (rows 97 14 84 168 145 32 64 128 256), losses := [] }

theorem u14019 : Upper (D 8) (R 8) [96,12,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14020 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 146 289 353 417 289), lower := (rows 97 14 84 168 146 32 64 128 256), losses := [] }

theorem u14020 : Upper (D 8) (R 8) [96,12,80,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14021 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 84 168 176 291 323 387 259), lower := (rows 97 14 84 168 176 32 64 128 256), losses := [] }

theorem u14021 : Upper (D 8) (R 8) [96,12,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14022 : Route 9 := (fun mask => (mask,id))

def c14022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14022 : Upper (D 8) (R 8) [96,12,80,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,80,160,257] 13 (by decide) (choices 1) [1,2,128] r14022 c14022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4753
  · exact u4754
  · exact u4755

def b14023 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 168 274 161 225 161 417), lower := (rows 97 14 84 168 274 32 64 128 256), losses := [] }

theorem u14023 : Upper (D 8) (R 8) [96,12,80,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14024 : Route 9 := (fun mask => (mask,id))

def c14024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14024 : Upper (D 8) (R 8) [96,12,80,160,288] 13 := by
  apply FastRouting.sound _ _ [96,12,80,160,288] 13 (by decide) (choices 1) [1,2,128] r14024 c14024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4756
  · exact u4757
  · exact u4758

def b14025 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 400 35 99 163 291), lower := (rows 97 14 84 168 400 32 64 128 256), losses := [] }

theorem u14025 : Upper (D 8) (R 8) [96,12,80,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14026 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 20, targets := 128 }], pairs := [(2,7)], upper := (rows 97 14 84 265 49 162 226 162 418), lower := (rows 97 14 84 265 49 32 64 128 256), losses := [] }

theorem u14026 : Upper (D 8) (R 8) [96,12,80,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14027 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 265 50 161 225 161 417), lower := (rows 97 14 84 265 50 32 64 128 256), losses := [] }

theorem u14027 : Upper (D 8) (R 8) [96,12,80,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14028 : Route 9 := (fun mask => (mask,id))

def c14028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14028 : Upper (D 8) (R 8) [96,12,80,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,80,257,129] 13 (by decide) (choices 1) [2,128] r14028 c14028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4759
  · exact u4760

def b14029 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 265 146 161 225 161 417), lower := (rows 97 14 84 265 146 32 64 128 256), losses := [] }

theorem u14029 : Upper (D 8) (R 8) [96,12,80,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14030 : Route 9 := (fun mask => (mask,id))

def c14030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14030 : Upper (D 8) (R 8) [96,12,80,257,160] 13 := by
  apply FastRouting.sound _ _ [96,12,80,257,160] 13 (by decide) (choices 1) [1,2,128] r14030 c14030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4761
  · exact u4762
  · exact u4763

def b14031 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 84 266 145 161 225 161 417), lower := (rows 97 14 84 266 145 32 64 128 256), losses := [] }

theorem u14031 : Upper (D 8) (R 8) [96,12,80,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14032 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 84 266 176 161 225 161 417), lower := (rows 97 14 84 266 176 32 64 128 256), losses := [] }

theorem u14032 : Upper (D 8) (R 8) [96,12,80,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14033 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 20, targets := 128 }], pairs := [(2,7)], upper := (rows 97 14 84 296 49 163 195 131 387), lower := (rows 97 14 84 296 49 32 64 128 256), losses := [] }

theorem u14033 : Upper (D 8) (R 8) [96,12,80,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14034 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 296 50 161 193 129 385), lower := (rows 97 14 84 296 50 32 64 128 256), losses := [] }

theorem u14034 : Upper (D 8) (R 8) [96,12,80,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14035 : Route 9 := (fun mask => (mask,id))

def c14035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14035 : Upper (D 8) (R 8) [96,12,80,288,129] 13 := by
  apply FastRouting.sound _ _ [96,12,80,288,129] 13 (by decide) (choices 1) [1,2,128] r14035 c14035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4764
  · exact u4765
  · exact u4766

def b14036 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 296 146 161 225 161 417), lower := (rows 97 14 84 296 146 32 64 128 256), losses := [] }

theorem u14036 : Upper (D 8) (R 8) [96,12,80,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14037 : Route 9 := (fun mask => (mask,id))

def c14037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14037 : Upper (D 8) (R 8) [96,12,80,288,160] 13 := by
  apply FastRouting.sound _ _ [96,12,80,288,160] 13 (by decide) (choices 1) [1,2,128] r14037 c14037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4767
  · exact u4768
  · exact u4769

def b14038 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 20, targets := 128 }], pairs := [(2,7)], upper := (rows 97 14 84 392 49 163 227 163 419), lower := (rows 97 14 84 392 49 32 64 128 256), losses := [] }

theorem u14038 : Upper (D 8) (R 8) [96,12,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14039 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 84 392 50 161 225 161 417), lower := (rows 97 14 84 392 50 32 64 128 256), losses := [] }

theorem u14039 : Upper (D 8) (R 8) [96,12,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14039
end Delivery.IrregularNine14.P08
