import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12960 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 56 152 418 482 418 418), lower := (rows 97 7 69 56 152 32 64 128 256), losses := [] }

theorem u12960 : Upper (D 8) (R 8) [96,5,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12961 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 56 274 168 232 168 424), lower := (rows 97 7 69 56 274 32 64 128 256), losses := [] }

theorem u12961 : Upper (D 8) (R 8) [96,5,65,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12962 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 56 280 162 226 162 418), lower := (rows 97 7 69 56 280 32 64 128 256), losses := [] }

theorem u12962 : Upper (D 8) (R 8) [96,5,65,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12963 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 56 400 170 234 170 426), lower := (rows 97 7 69 56 400 32 64 128 256), losses := [] }

theorem u12963 : Upper (D 8) (R 8) [96,5,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12964 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 138 176 312 376 440 312), lower := (rows 97 7 69 138 176 32 64 128 256), losses := [] }

theorem u12964 : Upper (D 8) (R 8) [96,5,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12965 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 138 280 176 240 176 432), lower := (rows 97 7 69 138 280 32 64 128 256), losses := [] }

theorem u12965 : Upper (D 8) (R 8) [96,5,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12966 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 138 304 184 248 184 440), lower := (rows 97 7 69 138 304 32 64 128 256), losses := [] }

theorem u12966 : Upper (D 8) (R 8) [96,5,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12967 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 138 400 56 120 184 312), lower := (rows 97 7 69 138 400 32 64 128 256), losses := [] }

theorem u12967 : Upper (D 8) (R 8) [96,5,65,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12968 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 152 274 168 232 168 424), lower := (rows 97 7 69 152 274 32 64 128 256), losses := [] }

theorem u12968 : Upper (D 8) (R 8) [96,5,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12969 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 152 280 162 226 162 418), lower := (rows 97 7 69 152 280 32 64 128 256), losses := [] }

theorem u12969 : Upper (D 8) (R 8) [96,5,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12970 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 152 304 170 234 170 426), lower := (rows 97 7 69 152 304 32 64 128 256), losses := [] }

theorem u12970 : Upper (D 8) (R 8) [96,5,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12971 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 168 274 184 248 184 440), lower := (rows 97 7 69 168 274 32 64 128 256), losses := [] }

theorem u12971 : Upper (D 8) (R 8) [96,5,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12972 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 168 280 178 242 178 434), lower := (rows 97 7 69 168 280 32 64 128 256), losses := [] }

theorem u12972 : Upper (D 8) (R 8) [96,5,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12973 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 168 304 186 218 154 410), lower := (rows 97 7 69 168 304 32 64 128 256), losses := [] }

theorem u12973 : Upper (D 8) (R 8) [96,5,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12974 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 168 400 58 122 186 314), lower := (rows 97 7 69 168 400 32 64 128 256), losses := [] }

theorem u12974 : Upper (D 8) (R 8) [96,5,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12975 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 25 152 416 480 416 416), lower := (rows 97 7 70 25 152 32 64 128 256), losses := [] }

theorem u12975 : Upper (D 8) (R 8) [96,5,66,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12976 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 25 176 424 488 424 424), lower := (rows 97 7 70 25 176 32 64 128 256), losses := [] }

theorem u12976 : Upper (D 8) (R 8) [96,5,66,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12977 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 25 280 160 224 160 416), lower := (rows 97 7 70 25 280 32 64 128 256), losses := [] }

theorem u12977 : Upper (D 8) (R 8) [96,5,66,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12978 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 25 304 168 232 168 424), lower := (rows 97 7 70 25 304 32 64 128 256), losses := [] }

theorem u12978 : Upper (D 8) (R 8) [96,5,66,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12979 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 25 400 168 232 168 424), lower := (rows 97 7 70 25 400 32 64 128 256), losses := [] }

theorem u12979 : Upper (D 8) (R 8) [96,5,66,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12980 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 56 145 424 488 424 424), lower := (rows 97 7 70 56 145 32 64 128 256), losses := [] }

theorem u12980 : Upper (D 8) (R 8) [96,5,66,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12981 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 56 152 417 481 417 417), lower := (rows 97 7 70 56 152 32 64 128 256), losses := [] }

theorem u12981 : Upper (D 8) (R 8) [96,5,66,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12982 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 56 273 168 232 168 424), lower := (rows 97 7 70 56 273 32 64 128 256), losses := [] }

theorem u12982 : Upper (D 8) (R 8) [96,5,66,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12983 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 56 280 161 225 161 417), lower := (rows 97 7 70 56 280 32 64 128 256), losses := [] }

theorem u12983 : Upper (D 8) (R 8) [96,5,66,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12984 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 56 400 169 233 169 425), lower := (rows 97 7 70 56 400 32 64 128 256), losses := [] }

theorem u12984 : Upper (D 8) (R 8) [96,5,66,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12985 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 137 176 312 376 440 312), lower := (rows 97 7 70 137 176 32 64 128 256), losses := [] }

theorem u12985 : Upper (D 8) (R 8) [96,5,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12986 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 137 280 176 240 176 432), lower := (rows 97 7 70 137 280 32 64 128 256), losses := [] }

theorem u12986 : Upper (D 8) (R 8) [96,5,66,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12987 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 137 304 184 248 184 440), lower := (rows 97 7 70 137 304 32 64 128 256), losses := [] }

theorem u12987 : Upper (D 8) (R 8) [96,5,66,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12988 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 137 400 56 120 184 312), lower := (rows 97 7 70 137 400 32 64 128 256), losses := [] }

theorem u12988 : Upper (D 8) (R 8) [96,5,66,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12989 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 152 273 168 232 168 424), lower := (rows 97 7 70 152 273 32 64 128 256), losses := [] }

theorem u12989 : Upper (D 8) (R 8) [96,5,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12990 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 152 280 161 225 161 417), lower := (rows 97 7 70 152 280 32 64 128 256), losses := [] }

theorem u12990 : Upper (D 8) (R 8) [96,5,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12991 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 152 304 169 233 169 425), lower := (rows 97 7 70 152 304 32 64 128 256), losses := [] }

theorem u12991 : Upper (D 8) (R 8) [96,5,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12992 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 168 273 184 248 184 440), lower := (rows 97 7 70 168 273 32 64 128 256), losses := [] }

theorem u12992 : Upper (D 8) (R 8) [96,5,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12993 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 168 280 177 241 177 433), lower := (rows 97 7 70 168 280 32 64 128 256), losses := [] }

theorem u12993 : Upper (D 8) (R 8) [96,5,66,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12994 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 168 304 185 217 153 409), lower := (rows 97 7 70 168 304 32 64 128 256), losses := [] }

theorem u12994 : Upper (D 8) (R 8) [96,5,66,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12995 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 168 400 57 121 185 313), lower := (rows 97 7 70 168 400 32 64 128 256), losses := [] }

theorem u12995 : Upper (D 8) (R 8) [96,5,66,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12996 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 25 146 416 480 416 416), lower := (rows 97 7 76 25 146 32 64 128 256), losses := [] }

theorem u12996 : Upper (D 8) (R 8) [96,5,72,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12997 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 25 176 418 482 418 418), lower := (rows 97 7 76 25 176 32 64 128 256), losses := [] }

theorem u12997 : Upper (D 8) (R 8) [96,5,72,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12998 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 25 274 160 224 160 416), lower := (rows 97 7 76 25 274 32 64 128 256), losses := [] }

theorem u12998 : Upper (D 8) (R 8) [96,5,72,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12999 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 25 304 162 226 162 418), lower := (rows 97 7 76 25 304 32 64 128 256), losses := [] }

theorem u12999 : Upper (D 8) (R 8) [96,5,72,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13000 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 25 400 162 226 162 418), lower := (rows 97 7 76 25 400 32 64 128 256), losses := [] }

theorem u13000 : Upper (D 8) (R 8) [96,5,72,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13001 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 26 145 416 480 416 416), lower := (rows 97 7 76 26 145 32 64 128 256), losses := [] }

theorem u13001 : Upper (D 8) (R 8) [96,5,72,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13002 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 26 176 417 481 417 417), lower := (rows 97 7 76 26 176 32 64 128 256), losses := [] }

theorem u13002 : Upper (D 8) (R 8) [96,5,72,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13003 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 26 273 160 224 160 416), lower := (rows 97 7 76 26 273 32 64 128 256), losses := [] }

theorem u13003 : Upper (D 8) (R 8) [96,5,72,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13004 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 26 304 161 225 161 417), lower := (rows 97 7 76 26 304 32 64 128 256), losses := [] }

theorem u13004 : Upper (D 8) (R 8) [96,5,72,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13005 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 26 400 161 225 161 417), lower := (rows 97 7 76 26 400 32 64 128 256), losses := [] }

theorem u13005 : Upper (D 8) (R 8) [96,5,72,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13006 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 76 42 145 432 496 432 432), lower := (rows 97 7 76 42 145 32 64 128 256), losses := [] }

theorem u13006 : Upper (D 8) (R 8) [96,5,72,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13007 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 76 42 176 433 465 401 401), lower := (rows 97 7 76 42 176 32 64 128 256), losses := [] }

theorem u13007 : Upper (D 8) (R 8) [96,5,72,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13008 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 76 42 273 176 240 176 432), lower := (rows 97 7 76 42 273 32 64 128 256), losses := [] }

theorem u13008 : Upper (D 8) (R 8) [96,5,72,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13009 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 76 42 304 177 209 145 401), lower := (rows 97 7 76 42 304 32 64 128 256), losses := [] }

theorem u13009 : Upper (D 8) (R 8) [96,5,72,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13010 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 76 42 400 177 241 177 433), lower := (rows 97 7 76 42 400 32 64 128 256), losses := [] }

theorem u13010 : Upper (D 8) (R 8) [96,5,72,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13011 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 56 145 418 482 418 418), lower := (rows 97 7 76 56 145 32 64 128 256), losses := [] }

theorem u13011 : Upper (D 8) (R 8) [96,5,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13012 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 56 146 417 481 417 417), lower := (rows 97 7 76 56 146 32 64 128 256), losses := [] }

theorem u13012 : Upper (D 8) (R 8) [96,5,72,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13013 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 56 273 162 226 162 418), lower := (rows 97 7 76 56 273 32 64 128 256), losses := [] }

theorem u13013 : Upper (D 8) (R 8) [96,5,72,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13014 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 56 274 161 225 161 417), lower := (rows 97 7 76 56 274 32 64 128 256), losses := [] }

theorem u13014 : Upper (D 8) (R 8) [96,5,72,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13015 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 56 400 163 227 163 419), lower := (rows 97 7 76 56 400 32 64 128 256), losses := [] }

theorem u13015 : Upper (D 8) (R 8) [96,5,72,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13016 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 50 432 496 432 432), lower := (rows 97 7 76 137 50 32 64 128 256), losses := [] }

theorem u13016 : Upper (D 8) (R 8) [96,5,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13017 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 146 304 368 432 304), lower := (rows 97 7 76 137 146 32 64 128 256), losses := [] }

theorem u13017 : Upper (D 8) (R 8) [96,5,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13018 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 176 306 370 434 306), lower := (rows 97 7 76 137 176 32 64 128 256), losses := [] }

theorem u13018 : Upper (D 8) (R 8) [96,5,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13019 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 274 176 240 176 432), lower := (rows 97 7 76 137 274 32 64 128 256), losses := [] }

theorem u13019 : Upper (D 8) (R 8) [96,5,72,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13019
end Delivery.IrregularNine14.P08
