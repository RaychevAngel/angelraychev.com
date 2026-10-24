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

def b18060 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 168 145 50 114 178 306), lower := (rows 321 7 76 168 145 32 64 128 256), losses := [] }

theorem u18060 : Upper (D 8) (R 8) [320,5,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18061 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 168 146 49 113 177 305), lower := (rows 321 7 76 168 146 32 64 128 256), losses := [] }

theorem u18061 : Upper (D 8) (R 8) [320,5,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18062 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 25 146 168 232 168 424), lower := (rows 321 7 100 25 146 32 64 128 256), losses := [] }

theorem u18062 : Upper (D 8) (R 8) [320,5,96,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18063 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 25 152 162 226 162 418), lower := (rows 321 7 100 25 152 32 64 128 256), losses := [] }

theorem u18063 : Upper (D 8) (R 8) [320,5,96,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18064 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 25 176 170 234 170 426), lower := (rows 321 7 100 25 176 32 64 128 256), losses := [] }

theorem u18064 : Upper (D 8) (R 8) [320,5,96,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18065 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 26 49 168 232 168 424), lower := (rows 321 7 100 26 49 32 64 128 256), losses := [] }

theorem u18065 : Upper (D 8) (R 8) [320,5,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18066 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 26 56 161 225 161 417), lower := (rows 321 7 100 26 56 32 64 128 256), losses := [] }

theorem u18066 : Upper (D 8) (R 8) [320,5,96,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18067 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 26 145 168 232 168 424), lower := (rows 321 7 100 26 145 32 64 128 256), losses := [] }

theorem u18067 : Upper (D 8) (R 8) [320,5,96,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18068 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 26 152 161 225 161 417), lower := (rows 321 7 100 26 152 32 64 128 256), losses := [] }

theorem u18068 : Upper (D 8) (R 8) [320,5,96,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18069 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 26 176 169 233 169 425), lower := (rows 321 7 100 26 176 32 64 128 256), losses := [] }

theorem u18069 : Upper (D 8) (R 8) [320,5,96,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18070 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 41 50 184 216 152 408), lower := (rows 321 7 100 41 50 32 64 128 256), losses := [] }

theorem u18070 : Upper (D 8) (R 8) [320,5,96,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18071 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 41 146 184 248 184 440), lower := (rows 321 7 100 41 146 32 64 128 256), losses := [] }

theorem u18071 : Upper (D 8) (R 8) [320,5,96,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18072 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 41 152 178 242 178 434), lower := (rows 321 7 100 41 152 32 64 128 256), losses := [] }

theorem u18072 : Upper (D 8) (R 8) [320,5,96,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18073 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 41 176 186 218 154 410), lower := (rows 321 7 100 41 176 32 64 128 256), losses := [] }

theorem u18073 : Upper (D 8) (R 8) [320,5,96,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18074 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 42 145 184 248 184 440), lower := (rows 321 7 100 42 145 32 64 128 256), losses := [] }

theorem u18074 : Upper (D 8) (R 8) [320,5,96,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18075 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 42 152 177 241 177 433), lower := (rows 321 7 100 42 152 32 64 128 256), losses := [] }

theorem u18075 : Upper (D 8) (R 8) [320,5,96,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18076 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 42 176 185 217 153 409), lower := (rows 321 7 100 42 176 32 64 128 256), losses := [] }

theorem u18076 : Upper (D 8) (R 8) [320,5,96,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18077 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 56 145 170 234 170 426), lower := (rows 321 7 100 56 145 32 64 128 256), losses := [] }

theorem u18077 : Upper (D 8) (R 8) [320,5,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18078 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 56 146 169 233 169 425), lower := (rows 321 7 100 56 146 32 64 128 256), losses := [] }

theorem u18078 : Upper (D 8) (R 8) [320,5,96,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18079 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 56 152 163 227 163 419), lower := (rows 321 7 100 56 152 32 64 128 256), losses := [] }

theorem u18079 : Upper (D 8) (R 8) [320,5,96,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18080 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 137 146 56 120 184 312), lower := (rows 321 7 100 137 146 32 64 128 256), losses := [] }

theorem u18080 : Upper (D 8) (R 8) [320,5,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18081 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 137 176 58 122 186 314), lower := (rows 321 7 100 137 176 32 64 128 256), losses := [] }

theorem u18081 : Upper (D 8) (R 8) [320,5,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18082 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 138 176 57 121 185 313), lower := (rows 321 7 100 138 176 32 64 128 256), losses := [] }

theorem u18082 : Upper (D 8) (R 8) [320,5,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18083 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 26 56 224 224 224 480), lower := (rows 321 7 133 26 56 32 64 128 256), losses := [] }

theorem u18083 : Upper (D 8) (R 8) [320,5,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18084 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 26 112 168 232 168 424), lower := (rows 321 7 133 26 112 32 64 128 256), losses := [] }

theorem u18084 : Upper (D 8) (R 8) [320,5,129,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18085 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 26 152 96 96 224 352), lower := (rows 321 7 133 26 152 32 64 128 256), losses := [] }

theorem u18085 : Upper (D 8) (R 8) [320,5,129,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18086 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 26 176 104 104 232 360), lower := (rows 321 7 133 26 176 32 64 128 256), losses := [] }

theorem u18086 : Upper (D 8) (R 8) [320,5,129,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18087 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 26 208 40 104 168 296), lower := (rows 321 7 133 26 208 32 64 128 256), losses := [] }

theorem u18087 : Upper (D 8) (R 8) [320,5,129,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18088 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 42 88 176 240 176 432), lower := (rows 321 7 133 42 88 32 64 128 256), losses := [] }

theorem u18088 : Upper (D 8) (R 8) [320,5,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18089 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 42 112 184 248 184 440), lower := (rows 321 7 133 42 112 32 64 128 256), losses := [] }

theorem u18089 : Upper (D 8) (R 8) [320,5,129,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18090 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 42 152 112 112 240 368), lower := (rows 321 7 133 42 152 32 64 128 256), losses := [] }

theorem u18090 : Upper (D 8) (R 8) [320,5,129,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18091 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 42 176 120 120 248 376), lower := (rows 321 7 133 42 176 32 64 128 256), losses := [] }

theorem u18091 : Upper (D 8) (R 8) [320,5,129,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18092 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 42 208 56 120 184 312), lower := (rows 321 7 133 42 208 32 64 128 256), losses := [] }

theorem u18092 : Upper (D 8) (R 8) [320,5,129,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18093 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 56 82 168 232 168 424), lower := (rows 321 7 133 56 82 32 64 128 256), losses := [] }

theorem u18093 : Upper (D 8) (R 8) [320,5,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18094 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 56 146 104 104 232 360), lower := (rows 321 7 133 56 146 32 64 128 256), losses := [] }

theorem u18094 : Upper (D 8) (R 8) [320,5,129,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18095 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 133 56 152 98 98 226 354), lower := (rows 321 7 133 56 152 32 64 128 256), losses := [] }

theorem u18095 : Upper (D 8) (R 8) [320,5,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18096 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 56 208 42 106 170 298), lower := (rows 321 7 133 56 208 32 64 128 256), losses := [] }

theorem u18096 : Upper (D 8) (R 8) [320,5,129,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18097 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 74 152 48 112 176 304), lower := (rows 321 7 133 74 152 32 64 128 256), losses := [] }

theorem u18097 : Upper (D 8) (R 8) [320,5,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18098 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 74 176 56 120 184 312), lower := (rows 321 7 133 74 176 32 64 128 256), losses := [] }

theorem u18098 : Upper (D 8) (R 8) [320,5,129,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18099 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 88 146 40 104 168 296), lower := (rows 321 7 133 88 146 32 64 128 256), losses := [] }

theorem u18099 : Upper (D 8) (R 8) [320,5,129,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18100 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 88 176 42 106 170 298), lower := (rows 321 7 133 88 176 32 64 128 256), losses := [] }

theorem u18100 : Upper (D 8) (R 8) [320,5,129,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18101 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 104 146 56 120 184 312), lower := (rows 321 7 133 104 146 32 64 128 256), losses := [] }

theorem u18101 : Upper (D 8) (R 8) [320,5,129,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18102 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 104 152 50 114 178 306), lower := (rows 321 7 133 104 152 32 64 128 256), losses := [] }

theorem u18102 : Upper (D 8) (R 8) [320,5,129,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18103 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 104 176 58 122 186 314), lower := (rows 321 7 133 104 176 32 64 128 256), losses := [] }

theorem u18103 : Upper (D 8) (R 8) [320,5,129,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18104 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 25 176 104 104 232 360), lower := (rows 321 7 134 25 176 32 64 128 256), losses := [] }

theorem u18104 : Upper (D 8) (R 8) [320,5,130,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18105 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 134 41 56 240 240 240 496), lower := (rows 321 7 134 41 56 32 64 128 256), losses := [] }

theorem u18105 : Upper (D 8) (R 8) [320,5,130,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18106 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 134 41 88 176 240 176 432), lower := (rows 321 7 134 41 88 32 64 128 256), losses := [] }

theorem u18106 : Upper (D 8) (R 8) [320,5,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18107 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 134 41 112 184 248 184 440), lower := (rows 321 7 134 41 112 32 64 128 256), losses := [] }

theorem u18107 : Upper (D 8) (R 8) [320,5,130,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18108 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 41 152 112 112 240 368), lower := (rows 321 7 134 41 152 32 64 128 256), losses := [] }

theorem u18108 : Upper (D 8) (R 8) [320,5,130,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18109 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 41 176 120 120 248 376), lower := (rows 321 7 134 41 176 32 64 128 256), losses := [] }

theorem u18109 : Upper (D 8) (R 8) [320,5,130,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18110 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 41 208 56 120 184 312), lower := (rows 321 7 134 41 208 32 64 128 256), losses := [] }

theorem u18110 : Upper (D 8) (R 8) [320,5,130,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18111 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 134 56 56 225 225 225 481), lower := (rows 321 7 134 56 56 32 64 128 256), losses := [] }

theorem u18111 : Upper (D 8) (R 8) [320,5,130,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18112 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 134 56 81 168 232 168 424), lower := (rows 321 7 134 56 81 32 64 128 256), losses := [] }

theorem u18112 : Upper (D 8) (R 8) [320,5,130,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18113 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 134 56 88 161 225 161 417), lower := (rows 321 7 134 56 88 32 64 128 256), losses := [] }

theorem u18113 : Upper (D 8) (R 8) [320,5,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18114 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 134 56 112 169 233 169 425), lower := (rows 321 7 134 56 112 32 64 128 256), losses := [] }

theorem u18114 : Upper (D 8) (R 8) [320,5,130,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18115 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 134 56 145 104 104 232 360), lower := (rows 321 7 134 56 145 32 64 128 256), losses := [] }

theorem u18115 : Upper (D 8) (R 8) [320,5,130,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18116 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 56 152 97 97 225 353), lower := (rows 321 7 134 56 152 32 64 128 256), losses := [] }

theorem u18116 : Upper (D 8) (R 8) [320,5,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18117 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 134 56 176 105 105 233 361), lower := (rows 321 7 134 56 176 32 64 128 256), losses := [] }

theorem u18117 : Upper (D 8) (R 8) [320,5,130,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18118 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 56 208 41 105 169 297), lower := (rows 321 7 134 56 208 32 64 128 256), losses := [] }

theorem u18118 : Upper (D 8) (R 8) [320,5,130,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18119 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 134 88 145 40 104 168 296), lower := (rows 321 7 134 88 145 32 64 128 256), losses := [] }

theorem u18119 : Upper (D 8) (R 8) [320,5,130,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18119
end Delivery.IrregularNine14.P08
