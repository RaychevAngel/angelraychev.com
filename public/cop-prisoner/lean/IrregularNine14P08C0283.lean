import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0103

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16980 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 56 84 161 225 161 417), lower := (rows 259 194 13 56 84 32 64 128 256), losses := [] }

theorem u16980 : Upper (D 8) (R 8) [258,192,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16981 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 13 56 112 165 229 165 421), lower := (rows 259 194 13 56 112 32 64 128 256), losses := [] }

theorem u16981 : Upper (D 8) (R 8) [258,192,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16982 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 13 56 208 37 101 165 293), lower := (rows 259 194 13 56 208 32 64 128 256), losses := [] }

theorem u16982 : Upper (D 8) (R 8) [258,192,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16983 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 73 52 176 240 176 432), lower := (rows 259 194 13 73 52 32 64 128 256), losses := [] }

theorem u16983 : Upper (D 8) (R 8) [258,192,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16984 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 73 148 48 112 176 304), lower := (rows 259 194 13 73 148 32 64 128 256), losses := [] }

theorem u16984 : Upper (D 8) (R 8) [258,192,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16985 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 73 176 52 116 180 308), lower := (rows 259 194 13 73 176 32 64 128 256), losses := [] }

theorem u16985 : Upper (D 8) (R 8) [258,192,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16986 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 76 49 176 240 176 432), lower := (rows 259 194 13 76 49 32 64 128 256), losses := [] }

theorem u16986 : Upper (D 8) (R 8) [258,192,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16987 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 76 176 49 113 177 305), lower := (rows 259 194 13 76 176 32 64 128 256), losses := [] }

theorem u16987 : Upper (D 8) (R 8) [258,192,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16988 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 88 49 164 228 164 420), lower := (rows 259 194 13 88 49 32 64 128 256), losses := [] }

theorem u16988 : Upper (D 8) (R 8) [258,192,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16989 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 88 52 161 225 161 417), lower := (rows 259 194 13 88 52 32 64 128 256), losses := [] }

theorem u16989 : Upper (D 8) (R 8) [258,192,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16990 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 88 148 33 97 161 289), lower := (rows 259 194 13 88 148 32 64 128 256), losses := [] }

theorem u16990 : Upper (D 8) (R 8) [258,192,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16991 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 88 176 37 101 165 293), lower := (rows 259 194 13 88 176 32 64 128 256), losses := [] }

theorem u16991 : Upper (D 8) (R 8) [258,192,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16992 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 104 49 180 244 180 436), lower := (rows 259 194 13 104 49 32 64 128 256), losses := [] }

theorem u16992 : Upper (D 8) (R 8) [258,192,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16993 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 104 52 177 241 177 433), lower := (rows 259 194 13 104 52 32 64 128 256), losses := [] }

theorem u16993 : Upper (D 8) (R 8) [258,192,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16994 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 104 148 49 113 177 305), lower := (rows 259 194 13 104 148 32 64 128 256), losses := [] }

theorem u16994 : Upper (D 8) (R 8) [258,192,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16995 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 194 13 104 176 53 117 181 309), lower := (rows 259 194 13 104 176 32 64 128 256), losses := [] }

theorem u16995 : Upper (D 8) (R 8) [258,192,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16996 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 13 200 49 52 116 180 308), lower := (rows 259 194 13 200 49 32 64 128 256), losses := [] }

theorem u16996 : Upper (D 8) (R 8) [258,192,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16997 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 13 200 52 49 113 177 305), lower := (rows 259 194 13 200 52 32 64 128 256), losses := [] }

theorem u16997 : Upper (D 8) (R 8) [258,192,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16998 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 28 41 49 228 228 228 484), lower := (rows 259 194 28 41 49 32 64 128 256), losses := [] }

theorem u16998 : Upper (D 8) (R 8) [258,192,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16999 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 28 41 52 225 225 225 481), lower := (rows 259 194 28 41 52 32 64 128 256), losses := [] }

theorem u16999 : Upper (D 8) (R 8) [258,192,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17000 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 28 41 81 164 228 164 420), lower := (rows 259 194 28 41 81 32 64 128 256), losses := [] }

theorem u17000 : Upper (D 8) (R 8) [258,192,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17001 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 28 41 84 161 225 161 417), lower := (rows 259 194 28 41 84 32 64 128 256), losses := [] }

theorem u17001 : Upper (D 8) (R 8) [258,192,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17002 : Route 9 := (fun mask => (mask,id))

def c17002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17002 : Upper (D 8) (R 8) [258,192,24,33,96] 13 := by
  apply FastRouting.sound _ _ [258,192,24,33,96] 13 (by decide) (choices 1) [1,4,128] r17002 c17002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6210
  · exact u6211
  · exact u6212

def b17003 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 28 41 208 37 101 165 293), lower := (rows 259 194 28 41 208 32 64 128 256), losses := [] }

theorem u17003 : Upper (D 8) (R 8) [258,192,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17004 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 28 44 81 161 225 161 417), lower := (rows 259 194 28 44 81 32 64 128 256), losses := [] }

theorem u17004 : Upper (D 8) (R 8) [258,192,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17005 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 28 44 112 161 225 161 417), lower := (rows 259 194 28 44 112 32 64 128 256), losses := [] }

theorem u17005 : Upper (D 8) (R 8) [258,192,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17006 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 28 44 208 33 97 161 289), lower := (rows 259 194 28 44 208 32 64 128 256), losses := [] }

theorem u17006 : Upper (D 8) (R 8) [258,192,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17007 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 28 73 176 37 101 165 293), lower := (rows 259 194 28 73 176 32 64 128 256), losses := [] }

theorem u17007 : Upper (D 8) (R 8) [258,192,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17008 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 28 76 176 33 97 161 289), lower := (rows 259 194 28 76 176 32 64 128 256), losses := [] }

theorem u17008 : Upper (D 8) (R 8) [258,192,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17009 : Route 9 := (fun mask => (mask,id))

def c17009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17009 : Upper (D 8) (R 8) [258,192,24,96,160] 13 := by
  apply FastRouting.sound _ _ [258,192,24,96,160] 13 (by decide) (choices 1) [1,4] r17009 c17009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6213
  · exact u6214

def b17010 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 194 37 41 52 248 216 216 472), lower := (rows 259 194 37 41 52 32 64 128 256), losses := [] }

theorem u17010 : Upper (D 8) (R 8) [258,192,33,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17011 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 194 37 41 84 184 248 184 440), lower := (rows 259 194 37 41 84 32 64 128 256), losses := [] }

theorem u17011 : Upper (D 8) (R 8) [258,192,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17012 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 194 37 41 112 188 220 156 412), lower := (rows 259 194 37 41 112 32 64 128 256), losses := [] }

theorem u17012 : Upper (D 8) (R 8) [258,192,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17013 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 44 56 241 209 209 465), lower := (rows 259 194 37 44 56 32 64 128 256), losses := [] }

theorem u17013 : Upper (D 8) (R 8) [258,192,33,36,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17014 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 44 88 177 241 177 433), lower := (rows 259 194 37 44 88 32 64 128 256), losses := [] }

theorem u17014 : Upper (D 8) (R 8) [258,192,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17015 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 44 112 185 217 153 409), lower := (rows 259 194 37 44 112 32 64 128 256), losses := [] }

theorem u17015 : Upper (D 8) (R 8) [258,192,33,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17016 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 56 56 229 197 197 453), lower := (rows 259 194 37 56 56 32 64 128 256), losses := [] }

theorem u17016 : Upper (D 8) (R 8) [258,192,33,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17017 : PairBound 9 := { available := 172, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 37 56 81 172 236 172 428), lower := (rows 259 194 37 56 81 32 64 128 256), losses := [] }

theorem u17017 : Upper (D 8) (R 8) [258,192,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17018 : Route 9 := (fun mask => (mask,id))

def c17018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17018 : Upper (D 8) (R 8) [258,192,33,48,68] 13 := by
  apply FastRouting.sound _ _ [258,192,33,48,68] 13 (by decide) (choices 1) [1,8,128] r17018 c17018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6215
  · exact u6216
  · exact u6217

def b17019 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 37 56 88 165 229 165 421), lower := (rows 259 194 37 56 88 32 64 128 256), losses := [] }

theorem u17019 : Upper (D 8) (R 8) [258,192,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17020 : PairBound 9 := { available := 141, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 56 112 173 205 141 397), lower := (rows 259 194 37 56 112 32 64 128 256), losses := [] }

theorem u17020 : Upper (D 8) (R 8) [258,192,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17021 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 37 56 208 45 109 173 301), lower := (rows 259 194 37 56 208 32 64 128 256), losses := [] }

theorem u17021 : Upper (D 8) (R 8) [258,192,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17022 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 37 73 148 56 120 184 312), lower := (rows 259 194 37 73 148 32 64 128 256), losses := [] }

theorem u17022 : Upper (D 8) (R 8) [258,192,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17023 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 37 73 152 52 116 180 308), lower := (rows 259 194 37 73 152 32 64 128 256), losses := [] }

theorem u17023 : Upper (D 8) (R 8) [258,192,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17024 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 37 73 176 60 124 188 316), lower := (rows 259 194 37 73 176 32 64 128 256), losses := [] }

theorem u17024 : Upper (D 8) (R 8) [258,192,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17025 : Route 9 := (fun mask => (mask,id))

def c17025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17025 : Upper (D 8) (R 8) [258,192,33,68,136] 13 := by
  apply FastRouting.sound _ _ [258,192,33,68,136] 13 (by decide) (choices 1) [1,16] r17025 c17025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6218
  · exact u6219

def r17026 : Route 9 := (fun mask => (mask,id))

def c17026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17026 : Upper (D 8) (R 8) [258,192,33,68,160] 13 := by
  apply FastRouting.sound _ _ [258,192,33,68,160] 13 (by decide) (choices 1) [1,8,16] r17026 c17026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6220
  · exact u6221
  · exact u6222

def b17027 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 37 88 152 37 101 165 293), lower := (rows 259 194 37 88 152 32 64 128 256), losses := [] }

theorem u17027 : Upper (D 8) (R 8) [258,192,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17028 : Route 9 := (fun mask => (mask,id))

def c17028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17028 : Upper (D 8) (R 8) [258,192,33,80,160] 13 := by
  apply FastRouting.sound _ _ [258,192,33,80,160] 13 (by decide) (choices 1) [1,4,8] r17028 c17028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6223
  · exact u6224
  · exact u6225

theorem m17029_16 : Upper (D 8) (R 8) [258,192,33,96,160,16] 13 :=
  permutation_upper _ _ _ [258,192,33,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6228

def r17029 : Route 9 := (fun mask => (mask,id))

def c17029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17029 : Upper (D 8) (R 8) [258,192,33,96,160] 13 := by
  apply FastRouting.sound _ _ [258,192,33,96,160] 13 (by decide) (choices 1) [1,4,8,16] r17029 c17029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6226
  · exact u6227
  · exact u6228
  · exact m17029_16

def b17030 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 44 112 177 209 145 401), lower := (rows 259 194 44 44 112 32 64 128 256), losses := [] }

theorem u17030 : Upper (D 8) (R 8) [258,192,40,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17031 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 56 84 161 225 161 417), lower := (rows 259 194 44 56 84 32 64 128 256), losses := [] }

theorem u17031 : Upper (D 8) (R 8) [258,192,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17032 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 56 112 165 197 133 389), lower := (rows 259 194 44 56 112 32 64 128 256), losses := [] }

theorem u17032 : Upper (D 8) (R 8) [258,192,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17033 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 44 73 148 49 113 177 305), lower := (rows 259 194 44 73 148 32 64 128 256), losses := [] }

theorem u17033 : Upper (D 8) (R 8) [258,192,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17034 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 44 73 176 53 117 181 309), lower := (rows 259 194 44 73 176 32 64 128 256), losses := [] }

theorem u17034 : Upper (D 8) (R 8) [258,192,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17035 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 44 76 176 49 113 177 305), lower := (rows 259 194 44 76 176 32 64 128 256), losses := [] }

theorem u17035 : Upper (D 8) (R 8) [258,192,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17036 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 259 194 44 88 145 37 101 165 293), lower := (rows 259 194 44 88 145 32 64 128 256), losses := [] }

theorem u17036 : Upper (D 8) (R 8) [258,192,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17037 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 44 88 148 33 97 161 289), lower := (rows 259 194 44 88 148 32 64 128 256), losses := [] }

theorem u17037 : Upper (D 8) (R 8) [258,192,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17038 : Route 9 := (fun mask => (mask,id))

def c17038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17038 : Upper (D 8) (R 8) [258,192,40,80,160] 13 := by
  apply FastRouting.sound _ _ [258,192,40,80,160] 13 (by decide) (choices 1) [1,4] r17038 c17038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6229
  · exact u6230

def b17039 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 104 148 49 113 177 305), lower := (rows 259 194 44 104 148 32 64 128 256), losses := [] }

theorem u17039 : Upper (D 8) (R 8) [258,192,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17039
end Delivery.IrregularNine14.P08
