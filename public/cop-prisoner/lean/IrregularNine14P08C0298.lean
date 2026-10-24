import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0110

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17880 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 28 168 208 35 99 163 291), lower := (rows 321 7 28 168 208 32 64 128 256), losses := [] }

theorem u17880 : Upper (D 8) (R 8) [320,5,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17881 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 26 56 224 224 224 480), lower := (rows 321 7 37 26 56 32 64 128 256), losses := [] }

theorem u17881 : Upper (D 8) (R 8) [320,5,33,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17882 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 26 112 168 232 168 424), lower := (rows 321 7 37 26 112 32 64 128 256), losses := [] }

theorem u17882 : Upper (D 8) (R 8) [320,5,33,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17883 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 26 152 224 224 224 480), lower := (rows 321 7 37 26 152 32 64 128 256), losses := [] }

theorem u17883 : Upper (D 8) (R 8) [320,5,33,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17884 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 26 176 232 232 232 488), lower := (rows 321 7 37 26 176 32 64 128 256), losses := [] }

theorem u17884 : Upper (D 8) (R 8) [320,5,33,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17885 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 26 208 168 232 168 424), lower := (rows 321 7 37 26 208 32 64 128 256), losses := [] }

theorem u17885 : Upper (D 8) (R 8) [320,5,33,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17886 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 42 88 176 240 176 432), lower := (rows 321 7 37 42 88 32 64 128 256), losses := [] }

theorem u17886 : Upper (D 8) (R 8) [320,5,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17887 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 42 112 184 216 152 408), lower := (rows 321 7 37 42 112 32 64 128 256), losses := [] }

theorem u17887 : Upper (D 8) (R 8) [320,5,33,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17888 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 42 152 240 240 240 496), lower := (rows 321 7 37 42 152 32 64 128 256), losses := [] }

theorem u17888 : Upper (D 8) (R 8) [320,5,33,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17889 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 42 176 248 216 216 472), lower := (rows 321 7 37 42 176 32 64 128 256), losses := [] }

theorem u17889 : Upper (D 8) (R 8) [320,5,33,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17890 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 42 208 184 248 184 440), lower := (rows 321 7 37 42 208 32 64 128 256), losses := [] }

theorem u17890 : Upper (D 8) (R 8) [320,5,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17891 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 56 82 168 232 168 424), lower := (rows 321 7 37 56 82 32 64 128 256), losses := [] }

theorem u17891 : Upper (D 8) (R 8) [320,5,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17892 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 56 146 232 232 232 488), lower := (rows 321 7 37 56 146 32 64 128 256), losses := [] }

theorem u17892 : Upper (D 8) (R 8) [320,5,33,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17893 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 56 152 226 226 226 482), lower := (rows 321 7 37 56 152 32 64 128 256), losses := [] }

theorem u17893 : Upper (D 8) (R 8) [320,5,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17894 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 56 208 170 234 170 426), lower := (rows 321 7 37 56 208 32 64 128 256), losses := [] }

theorem u17894 : Upper (D 8) (R 8) [320,5,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17895 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 74 152 176 240 176 432), lower := (rows 321 7 37 74 152 32 64 128 256), losses := [] }

theorem u17895 : Upper (D 8) (R 8) [320,5,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17896 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 74 176 184 248 184 440), lower := (rows 321 7 37 74 176 32 64 128 256), losses := [] }

theorem u17896 : Upper (D 8) (R 8) [320,5,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17897 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 88 146 168 232 168 424), lower := (rows 321 7 37 88 146 32 64 128 256), losses := [] }

theorem u17897 : Upper (D 8) (R 8) [320,5,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17898 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 88 176 170 234 170 426), lower := (rows 321 7 37 88 176 32 64 128 256), losses := [] }

theorem u17898 : Upper (D 8) (R 8) [320,5,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17899 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 104 146 184 248 184 440), lower := (rows 321 7 37 104 146 32 64 128 256), losses := [] }

theorem u17899 : Upper (D 8) (R 8) [320,5,33,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17900 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 104 152 178 242 178 434), lower := (rows 321 7 37 104 152 32 64 128 256), losses := [] }

theorem u17900 : Upper (D 8) (R 8) [320,5,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17901 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 104 176 186 218 154 410), lower := (rows 321 7 37 104 176 32 64 128 256), losses := [] }

theorem u17901 : Upper (D 8) (R 8) [320,5,33,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17902 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 138 176 120 120 248 376), lower := (rows 321 7 37 138 176 32 64 128 256), losses := [] }

theorem u17902 : Upper (D 8) (R 8) [320,5,33,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17903 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 138 208 56 120 184 312), lower := (rows 321 7 37 138 208 32 64 128 256), losses := [] }

theorem u17903 : Upper (D 8) (R 8) [320,5,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17904 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 168 208 58 122 186 314), lower := (rows 321 7 37 168 208 32 64 128 256), losses := [] }

theorem u17904 : Upper (D 8) (R 8) [320,5,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17905 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 38 25 56 224 224 224 480), lower := (rows 321 7 38 25 56 32 64 128 256), losses := [] }

theorem u17905 : Upper (D 8) (R 8) [320,5,34,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17906 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 321 7 38 25 88 160 224 160 416), lower := (rows 321 7 38 25 88 32 64 128 256), losses := [] }

theorem u17906 : Upper (D 8) (R 8) [320,5,34,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17907 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 25 112 168 232 168 424), lower := (rows 321 7 38 25 112 32 64 128 256), losses := [] }

theorem u17907 : Upper (D 8) (R 8) [320,5,34,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17908 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 38 25 152 224 224 224 480), lower := (rows 321 7 38 25 152 32 64 128 256), losses := [] }

theorem u17908 : Upper (D 8) (R 8) [320,5,34,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17909 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 38 25 176 232 232 232 488), lower := (rows 321 7 38 25 176 32 64 128 256), losses := [] }

theorem u17909 : Upper (D 8) (R 8) [320,5,34,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17910 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 25 208 168 232 168 424), lower := (rows 321 7 38 25 208 32 64 128 256), losses := [] }

theorem u17910 : Upper (D 8) (R 8) [320,5,34,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17911 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 56 240 208 208 464), lower := (rows 321 7 38 41 56 32 64 128 256), losses := [] }

theorem u17911 : Upper (D 8) (R 8) [320,5,34,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17912 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 88 176 240 176 432), lower := (rows 321 7 38 41 88 32 64 128 256), losses := [] }

theorem u17912 : Upper (D 8) (R 8) [320,5,34,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17913 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 112 184 216 152 408), lower := (rows 321 7 38 41 112 32 64 128 256), losses := [] }

theorem u17913 : Upper (D 8) (R 8) [320,5,34,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17914 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 152 240 240 240 496), lower := (rows 321 7 38 41 152 32 64 128 256), losses := [] }

theorem u17914 : Upper (D 8) (R 8) [320,5,34,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17915 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 176 248 216 216 472), lower := (rows 321 7 38 41 176 32 64 128 256), losses := [] }

theorem u17915 : Upper (D 8) (R 8) [320,5,34,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17916 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 208 184 248 184 440), lower := (rows 321 7 38 41 208 32 64 128 256), losses := [] }

theorem u17916 : Upper (D 8) (R 8) [320,5,34,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17917 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 56 56 225 193 193 449), lower := (rows 321 7 38 56 56 32 64 128 256), losses := [] }

theorem u17917 : Upper (D 8) (R 8) [320,5,34,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17918 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 56 81 168 232 168 424), lower := (rows 321 7 38 56 81 32 64 128 256), losses := [] }

theorem u17918 : Upper (D 8) (R 8) [320,5,34,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17919 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 56 88 161 225 161 417), lower := (rows 321 7 38 56 88 32 64 128 256), losses := [] }

theorem u17919 : Upper (D 8) (R 8) [320,5,34,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17920 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 56 112 169 201 137 393), lower := (rows 321 7 38 56 112 32 64 128 256), losses := [] }

theorem u17920 : Upper (D 8) (R 8) [320,5,34,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17921 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 56 145 232 232 232 488), lower := (rows 321 7 38 56 145 32 64 128 256), losses := [] }

theorem u17921 : Upper (D 8) (R 8) [320,5,34,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17922 : Route 9 := (fun mask => (mask,id))

def c17922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17922 : Upper (D 8) (R 8) [320,5,34,48,136] 13 := by
  apply FastRouting.sound _ _ [320,5,34,48,136] 13 (by decide) (choices 1) [1,64,128] r17922 c17922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6628
  · exact u6629
  · exact u6630

def b17923 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 56 176 233 201 201 457), lower := (rows 321 7 38 56 176 32 64 128 256), losses := [] }

theorem u17923 : Upper (D 8) (R 8) [320,5,34,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17924 : Route 9 := (fun mask => (mask,id))

def c17924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17924 : Upper (D 8) (R 8) [320,5,34,48,192] 13 := by
  apply FastRouting.sound _ _ [320,5,34,48,192] 13 (by decide) (choices 1) [1,8,128] r17924 c17924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6631
  · exact u6632
  · exact u6633

def b17925 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 73 152 176 240 176 432), lower := (rows 321 7 38 73 152 32 64 128 256), losses := [] }

theorem u17925 : Upper (D 8) (R 8) [320,5,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17926 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 73 176 184 248 184 440), lower := (rows 321 7 38 73 176 32 64 128 256), losses := [] }

theorem u17926 : Upper (D 8) (R 8) [320,5,34,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17927 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 88 145 168 232 168 424), lower := (rows 321 7 38 88 145 32 64 128 256), losses := [] }

theorem u17927 : Upper (D 8) (R 8) [320,5,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17928 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 88 152 161 225 161 417), lower := (rows 321 7 38 88 152 32 64 128 256), losses := [] }

theorem u17928 : Upper (D 8) (R 8) [320,5,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17929 : Route 9 := (fun mask => (mask,id))

def c17929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17929 : Upper (D 8) (R 8) [320,5,34,80,160] 13 := by
  apply FastRouting.sound _ _ [320,5,34,80,160] 13 (by decide) (choices 1) [1,8,128] r17929 c17929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6634
  · exact u6635
  · exact u6636

def b17930 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 104 145 184 248 184 440), lower := (rows 321 7 38 104 145 32 64 128 256), losses := [] }

theorem u17930 : Upper (D 8) (R 8) [320,5,34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17931 : Route 9 := (fun mask => (mask,id))

def c17931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17931 : Upper (D 8) (R 8) [320,5,34,96,136] 13 := by
  apply FastRouting.sound _ _ [320,5,34,96,136] 13 (by decide) (choices 1) [1,16,128] r17931 c17931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6637
  · exact u6638
  · exact u6639

def r17932 : Route 9 := (fun mask => (mask,id))

def c17932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17932 : Upper (D 8) (R 8) [320,5,34,96,160] 13 := by
  apply FastRouting.sound _ _ [320,5,34,96,160] 13 (by decide) (choices 1) [1,8,16,128] r17932 c17932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6640
  · exact u6641
  · exact u6642
  · exact u6643

def b17933 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 38 137 152 112 112 240 368), lower := (rows 321 7 38 137 152 32 64 128 256), losses := [] }

theorem u17933 : Upper (D 8) (R 8) [320,5,34,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17934 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 38 137 176 120 120 248 376), lower := (rows 321 7 38 137 176 32 64 128 256), losses := [] }

theorem u17934 : Upper (D 8) (R 8) [320,5,34,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17935 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 38 137 208 56 120 184 312), lower := (rows 321 7 38 137 208 32 64 128 256), losses := [] }

theorem u17935 : Upper (D 8) (R 8) [320,5,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17936 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 152 152 97 97 225 353), lower := (rows 321 7 38 152 152 32 64 128 256), losses := [] }

theorem u17936 : Upper (D 8) (R 8) [320,5,34,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17937 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 38 152 176 105 105 233 361), lower := (rows 321 7 38 152 176 32 64 128 256), losses := [] }

theorem u17937 : Upper (D 8) (R 8) [320,5,34,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17938 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 38 152 208 41 105 169 297), lower := (rows 321 7 38 152 208 32 64 128 256), losses := [] }

theorem u17938 : Upper (D 8) (R 8) [320,5,34,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17939 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 38 168 176 121 89 217 345), lower := (rows 321 7 38 168 176 32 64 128 256), losses := [] }

theorem u17939 : Upper (D 8) (R 8) [320,5,34,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17939
end Delivery.IrregularNine14.P08
