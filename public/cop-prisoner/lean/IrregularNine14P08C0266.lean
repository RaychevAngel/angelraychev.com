import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0095

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15960 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 88 146 289 353 417 289), lower := (rows 193 38 44 88 146 32 64 128 256), losses := [] }

theorem u15960 : Upper (D 8) (R 8) [192,36,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15961 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 88 176 291 323 387 259), lower := (rows 193 38 44 88 176 32 64 128 256), losses := [] }

theorem u15961 : Upper (D 8) (R 8) [192,36,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15962 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 88 273 163 227 163 419), lower := (rows 193 38 44 88 273 32 64 128 256), losses := [] }

theorem u15962 : Upper (D 8) (R 8) [192,36,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15963 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 88 274 161 225 161 417), lower := (rows 193 38 44 88 274 32 64 128 256), losses := [] }

theorem u15963 : Upper (D 8) (R 8) [192,36,40,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15964 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 88 304 163 195 131 387), lower := (rows 193 38 44 88 304 32 64 128 256), losses := [] }

theorem u15964 : Upper (D 8) (R 8) [192,36,40,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15965 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 88 400 35 99 163 291), lower := (rows 193 38 44 88 400 32 64 128 256), losses := [] }

theorem u15965 : Upper (D 8) (R 8) [192,36,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15966 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 104 146 305 337 401 273), lower := (rows 193 38 44 104 146 32 64 128 256), losses := [] }

theorem u15966 : Upper (D 8) (R 8) [192,36,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15967 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 104 273 179 211 147 403), lower := (rows 193 38 44 104 273 32 64 128 256), losses := [] }

theorem u15967 : Upper (D 8) (R 8) [192,36,40,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15968 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 104 274 177 209 145 401), lower := (rows 193 38 44 104 274 32 64 128 256), losses := [] }

theorem u15968 : Upper (D 8) (R 8) [192,36,40,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15969 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 104 400 51 83 147 275), lower := (rows 193 38 44 104 400 32 64 128 256), losses := [] }

theorem u15969 : Upper (D 8) (R 8) [192,36,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15970 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 265 82 177 241 177 433), lower := (rows 193 38 44 265 82 32 64 128 256), losses := [] }

theorem u15970 : Upper (D 8) (R 8) [192,36,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15971 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 265 112 179 211 147 403), lower := (rows 193 38 44 265 112 32 64 128 256), losses := [] }

theorem u15971 : Upper (D 8) (R 8) [192,36,40,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15972 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 266 112 177 209 145 401), lower := (rows 193 38 44 266 112 32 64 128 256), losses := [] }

theorem u15972 : Upper (D 8) (R 8) [192,36,40,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15973 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 280 82 161 225 161 417), lower := (rows 193 38 44 280 82 32 64 128 256), losses := [] }

theorem u15973 : Upper (D 8) (R 8) [192,36,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15974 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 280 112 163 195 131 387), lower := (rows 193 38 44 280 112 32 64 128 256), losses := [] }

theorem u15974 : Upper (D 8) (R 8) [192,36,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15975 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 296 82 177 209 145 401), lower := (rows 193 38 44 296 82 32 64 128 256), losses := [] }

theorem u15975 : Upper (D 8) (R 8) [192,36,40,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15976 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 328 146 49 113 177 305), lower := (rows 193 38 44 328 146 32 64 128 256), losses := [] }

theorem u15976 : Upper (D 8) (R 8) [192,36,40,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15977 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 328 176 51 83 147 275), lower := (rows 193 38 44 328 176 32 64 128 256), losses := [] }

theorem u15977 : Upper (D 8) (R 8) [192,36,40,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15978 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 56 146 297 361 425 297), lower := (rows 193 38 69 56 146 32 64 128 256), losses := [] }

theorem u15978 : Upper (D 8) (R 8) [192,36,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15979 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 56 273 170 234 170 426), lower := (rows 193 38 69 56 273 32 64 128 256), losses := [] }

theorem u15979 : Upper (D 8) (R 8) [192,36,65,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15980 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 56 274 169 233 169 425), lower := (rows 193 38 69 56 274 32 64 128 256), losses := [] }

theorem u15980 : Upper (D 8) (R 8) [192,36,65,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15981 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 56 280 163 227 163 419), lower := (rows 193 38 69 56 280 32 64 128 256), losses := [] }

theorem u15981 : Upper (D 8) (R 8) [192,36,65,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15982 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 56 400 43 107 171 299), lower := (rows 193 38 69 56 400 32 64 128 256), losses := [] }

theorem u15982 : Upper (D 8) (R 8) [192,36,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15983 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 138 273 56 120 184 312), lower := (rows 193 38 69 138 273 32 64 128 256), losses := [] }

theorem u15983 : Upper (D 8) (R 8) [192,36,65,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15984 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 138 280 49 113 177 305), lower := (rows 193 38 69 138 280 32 64 128 256), losses := [] }

theorem u15984 : Upper (D 8) (R 8) [192,36,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15985 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 138 304 57 121 185 313), lower := (rows 193 38 69 138 304 32 64 128 256), losses := [] }

theorem u15985 : Upper (D 8) (R 8) [192,36,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15986 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 152 273 42 106 170 298), lower := (rows 193 38 69 152 273 32 64 128 256), losses := [] }

theorem u15986 : Upper (D 8) (R 8) [192,36,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15987 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 152 274 41 105 169 297), lower := (rows 193 38 69 152 274 32 64 128 256), losses := [] }

theorem u15987 : Upper (D 8) (R 8) [192,36,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15988 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 152 304 43 107 171 299), lower := (rows 193 38 69 152 304 32 64 128 256), losses := [] }

theorem u15988 : Upper (D 8) (R 8) [192,36,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15989 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 168 273 58 122 186 314), lower := (rows 193 38 69 168 273 32 64 128 256), losses := [] }

theorem u15989 : Upper (D 8) (R 8) [192,36,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15990 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 168 274 57 121 185 313), lower := (rows 193 38 69 168 274 32 64 128 256), losses := [] }

theorem u15990 : Upper (D 8) (R 8) [192,36,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15991 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 168 280 51 115 179 307), lower := (rows 193 38 69 168 280 32 64 128 256), losses := [] }

theorem u15991 : Upper (D 8) (R 8) [192,36,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15992 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 168 304 59 91 155 283), lower := (rows 193 38 69 168 304 32 64 128 256), losses := [] }

theorem u15992 : Upper (D 8) (R 8) [192,36,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15993 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 56 273 169 233 169 425), lower := (rows 193 38 70 56 273 32 64 128 256), losses := [] }

theorem u15993 : Upper (D 8) (R 8) [192,36,66,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15994 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 56 280 161 225 161 417), lower := (rows 193 38 70 56 280 32 64 128 256), losses := [] }

theorem u15994 : Upper (D 8) (R 8) [192,36,66,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15995 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 56 400 41 105 169 297), lower := (rows 193 38 70 56 400 32 64 128 256), losses := [] }

theorem u15995 : Upper (D 8) (R 8) [192,36,66,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15996 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 152 273 41 105 169 297), lower := (rows 193 38 70 152 273 32 64 128 256), losses := [] }

theorem u15996 : Upper (D 8) (R 8) [192,36,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15997 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 152 304 41 105 169 297), lower := (rows 193 38 70 152 304 32 64 128 256), losses := [] }

theorem u15997 : Upper (D 8) (R 8) [192,36,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15998 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 168 273 57 121 185 313), lower := (rows 193 38 70 168 273 32 64 128 256), losses := [] }

theorem u15998 : Upper (D 8) (R 8) [192,36,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15999 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 168 280 49 113 177 305), lower := (rows 193 38 70 168 280 32 64 128 256), losses := [] }

theorem u15999 : Upper (D 8) (R 8) [192,36,66,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16000 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 168 304 57 89 153 281), lower := (rows 193 38 70 168 304 32 64 128 256), losses := [] }

theorem u16000 : Upper (D 8) (R 8) [192,36,66,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16001 : Route 9 := (fun mask => (mask,id))

def c16001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u16001 : Upper (D 8) (R 8) [192,36,72,48,130] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48,130] 13 (by decide) (choices 1) [1,256] r16001 c16001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5717
  · exact u5718

def b16002 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 76 56 176 291 323 387 259), lower := (rows 193 38 76 56 176 32 64 128 256), losses := [] }

theorem u16002 : Upper (D 8) (R 8) [192,36,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16003 : Route 9 := (fun mask => (mask,id))

def c16003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16003 : Upper (D 8) (R 8) [192,36,72,48,257] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48,257] 13 (by decide) (choices 1) [1,2,128] r16003 c16003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5719
  · exact u5720
  · exact u5721

def r16004 : Route 9 := (fun mask => (mask,id))

def c16004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16004 : Upper (D 8) (R 8) [192,36,72,48,258] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48,258] 13 (by decide) (choices 1) [1,128] r16004 c16004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5722
  · exact u5723

def b16005 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 76 56 304 163 195 131 387), lower := (rows 193 38 76 56 304 32 64 128 256), losses := [] }

theorem u16005 : Upper (D 8) (R 8) [192,36,72,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16006 : Route 9 := (fun mask => (mask,id))

def c16006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16006 : Upper (D 8) (R 8) [192,36,72,48,384] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48,384] 13 (by decide) (choices 1) [1,2] r16006 c16006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5724
  · exact u5725

def b16007 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 374, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 137 273 50 114 178 306), lower := (rows 193 38 76 137 273 32 64 128 256), losses := [] }

theorem u16007 : Upper (D 8) (R 8) [192,36,72,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16008 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 374, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 137 274 49 113 177 305), lower := (rows 193 38 76 137 274 32 64 128 256), losses := [] }

theorem u16008 : Upper (D 8) (R 8) [192,36,72,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16009 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 374, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 137 304 51 115 179 307), lower := (rows 193 38 76 137 304 32 64 128 256), losses := [] }

theorem u16009 : Upper (D 8) (R 8) [192,36,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16010 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 138 273 49 113 177 305), lower := (rows 193 38 76 138 273 32 64 128 256), losses := [] }

theorem u16010 : Upper (D 8) (R 8) [192,36,72,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16011 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 138 304 49 113 177 305), lower := (rows 193 38 76 138 304 32 64 128 256), losses := [] }

theorem u16011 : Upper (D 8) (R 8) [192,36,72,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16012 : Route 9 := (fun mask => (mask,id))

def c16012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16012 : Upper (D 8) (R 8) [192,36,72,144,257] 13 := by
  apply FastRouting.sound _ _ [192,36,72,144,257] 13 (by decide) (choices 1) [1,2] r16012 c16012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5726
  · exact u5727

def r16013 : Route 9 := (fun mask => (mask,id))

def c16013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16013 : Upper (D 8) (R 8) [192,36,72,144,258] 13 := by
  apply FastRouting.sound _ _ [192,36,72,144,258] 13 (by decide) (choices 1) [1] r16013 c16013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5728

def r16014 : Route 9 := (fun mask => (mask,id))

def c16014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16014 : Upper (D 8) (R 8) [192,36,72,144,288] 13 := by
  apply FastRouting.sound _ _ [192,36,72,144,288] 13 (by decide) (choices 1) [1,2] r16014 c16014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5729
  · exact u5730

def r16015 : Route 9 := (fun mask => (mask,id))

def c16015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16015 : Upper (D 8) (R 8) [192,36,72,160,257] 13 := by
  apply FastRouting.sound _ _ [192,36,72,160,257] 13 (by decide) (choices 1) [1,2,16] r16015 c16015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5731
  · exact u5732
  · exact u5733

def r16016 : Route 9 := (fun mask => (mask,id))

def c16016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16016 : Upper (D 8) (R 8) [192,36,72,160,258] 13 := by
  apply FastRouting.sound _ _ [192,36,72,160,258] 13 (by decide) (choices 1) [1,16] r16016 c16016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5734
  · exact u5735

def r16017 : Route 9 := (fun mask => (mask,id))

def c16017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16017 : Upper (D 8) (R 8) [192,36,72,160,288] 13 := by
  apply FastRouting.sound _ _ [192,36,72,160,288] 13 (by decide) (choices 1) [1,2,16] r16017 c16017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5736
  · exact u5737
  · exact u5738

def b16018 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 265 145 50 114 178 306), lower := (rows 193 38 76 265 145 32 64 128 256), losses := [] }

theorem u16018 : Upper (D 8) (R 8) [192,36,72,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16019 : Route 9 := (fun mask => (mask,id))

def c16019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16019 : Upper (D 8) (R 8) [192,36,72,257,130] 13 := by
  apply FastRouting.sound _ _ [192,36,72,257,130] 13 (by decide) (choices 1) [1,16] r16019 c16019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5739
  · exact u5740

#print axioms u16019
end Delivery.IrregularNine14.P08
