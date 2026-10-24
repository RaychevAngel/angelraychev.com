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

def b10980 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 52 432 496 432 432), lower := (rows 67 131 13 104 52 32 64 128 256), losses := [] }

theorem u10980 : Upper (D 8) (R 8) [66,129,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10981 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 148 304 368 432 304), lower := (rows 67 131 13 104 148 32 64 128 256), losses := [] }

theorem u10981 : Upper (D 8) (R 8) [66,129,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10982 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 176 308 372 436 308), lower := (rows 67 131 13 104 176 32 64 128 256), losses := [] }

theorem u10982 : Upper (D 8) (R 8) [66,129,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10983 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 276 176 240 176 432), lower := (rows 67 131 13 104 276 32 64 128 256), losses := [] }

theorem u10983 : Upper (D 8) (R 8) [66,129,9,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10984 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 304 180 244 180 436), lower := (rows 67 131 13 104 304 32 64 128 256), losses := [] }

theorem u10984 : Upper (D 8) (R 8) [66,129,9,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10985 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 400 52 116 180 308), lower := (rows 67 131 13 104 400 32 64 128 256), losses := [] }

theorem u10985 : Upper (D 8) (R 8) [66,129,9,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10986 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 140 112 304 368 432 304), lower := (rows 67 131 13 140 112 32 64 128 256), losses := [] }

theorem u10986 : Upper (D 8) (R 8) [66,129,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10987 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 140 304 112 112 240 368), lower := (rows 67 131 13 140 304 32 64 128 256), losses := [] }

theorem u10987 : Upper (D 8) (R 8) [66,129,9,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10988 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 140 336 48 112 176 304), lower := (rows 67 131 13 140 336 32 64 128 256), losses := [] }

theorem u10988 : Upper (D 8) (R 8) [66,129,9,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10989 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 152 52 352 352 480 352), lower := (rows 67 131 13 152 52 32 64 128 256), losses := [] }

theorem u10989 : Upper (D 8) (R 8) [66,129,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10990 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 152 84 288 352 416 288), lower := (rows 67 131 13 152 84 32 64 128 256), losses := [] }

theorem u10990 : Upper (D 8) (R 8) [66,129,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10991 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 152 112 292 356 420 292), lower := (rows 67 131 13 152 112 32 64 128 256), losses := [] }

theorem u10991 : Upper (D 8) (R 8) [66,129,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10992 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 152 276 96 96 224 352), lower := (rows 67 131 13 152 276 32 64 128 256), losses := [] }

theorem u10992 : Upper (D 8) (R 8) [66,129,9,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10993 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 152 304 100 100 228 356), lower := (rows 67 131 13 152 304 32 64 128 256), losses := [] }

theorem u10993 : Upper (D 8) (R 8) [66,129,9,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10994 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 152 336 36 100 164 292), lower := (rows 67 131 13 152 336 32 64 128 256), losses := [] }

theorem u10994 : Upper (D 8) (R 8) [66,129,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10995 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 52 368 368 496 368), lower := (rows 67 131 13 168 52 32 64 128 256), losses := [] }

theorem u10995 : Upper (D 8) (R 8) [66,129,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10996 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 84 304 368 432 304), lower := (rows 67 131 13 168 84 32 64 128 256), losses := [] }

theorem u10996 : Upper (D 8) (R 8) [66,129,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10997 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 112 308 372 436 308), lower := (rows 67 131 13 168 112 32 64 128 256), losses := [] }

theorem u10997 : Upper (D 8) (R 8) [66,129,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10998 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 276 112 112 240 368), lower := (rows 67 131 13 168 276 32 64 128 256), losses := [] }

theorem u10998 : Upper (D 8) (R 8) [66,129,9,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10999 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 304 116 116 244 372), lower := (rows 67 131 13 168 304 32 64 128 256), losses := [] }

theorem u10999 : Upper (D 8) (R 8) [66,129,9,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11000 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 336 52 116 180 308), lower := (rows 67 131 13 168 336 32 64 128 256), losses := [] }

theorem u11000 : Upper (D 8) (R 8) [66,129,9,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11001 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 268 112 176 240 176 432), lower := (rows 67 131 13 268 112 32 64 128 256), losses := [] }

theorem u11001 : Upper (D 8) (R 8) [66,129,9,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11002 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 268 176 112 112 240 368), lower := (rows 67 131 13 268 176 32 64 128 256), losses := [] }

theorem u11002 : Upper (D 8) (R 8) [66,129,9,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11003 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 280 52 224 224 224 480), lower := (rows 67 131 13 280 52 32 64 128 256), losses := [] }

theorem u11003 : Upper (D 8) (R 8) [66,129,9,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11004 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 280 84 160 224 160 416), lower := (rows 67 131 13 280 84 32 64 128 256), losses := [] }

theorem u11004 : Upper (D 8) (R 8) [66,129,9,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11005 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 280 112 164 228 164 420), lower := (rows 67 131 13 280 112 32 64 128 256), losses := [] }

theorem u11005 : Upper (D 8) (R 8) [66,129,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11006 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 280 148 96 96 224 352), lower := (rows 67 131 13 280 148 32 64 128 256), losses := [] }

theorem u11006 : Upper (D 8) (R 8) [66,129,9,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11007 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 280 176 100 100 228 356), lower := (rows 67 131 13 280 176 32 64 128 256), losses := [] }

theorem u11007 : Upper (D 8) (R 8) [66,129,9,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11008 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 296 52 240 240 240 496), lower := (rows 67 131 13 296 52 32 64 128 256), losses := [] }

theorem u11008 : Upper (D 8) (R 8) [66,129,9,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11009 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 296 84 176 240 176 432), lower := (rows 67 131 13 296 84 32 64 128 256), losses := [] }

theorem u11009 : Upper (D 8) (R 8) [66,129,9,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11010 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 296 112 180 244 180 436), lower := (rows 67 131 13 296 112 32 64 128 256), losses := [] }

theorem u11010 : Upper (D 8) (R 8) [66,129,9,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11011 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 296 148 112 112 240 368), lower := (rows 67 131 13 296 148 32 64 128 256), losses := [] }

theorem u11011 : Upper (D 8) (R 8) [66,129,9,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11012 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 296 176 116 116 244 372), lower := (rows 67 131 13 296 176 32 64 128 256), losses := [] }

theorem u11012 : Upper (D 8) (R 8) [66,129,9,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11013 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 328 52 176 240 176 432), lower := (rows 67 131 13 328 52 32 64 128 256), losses := [] }

theorem u11013 : Upper (D 8) (R 8) [66,129,9,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11014 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 328 148 48 112 176 304), lower := (rows 67 131 13 328 148 32 64 128 256), losses := [] }

theorem u11014 : Upper (D 8) (R 8) [66,129,9,320,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11015 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 328 176 52 116 180 308), lower := (rows 67 131 13 328 176 32 64 128 256), losses := [] }

theorem u11015 : Upper (D 8) (R 8) [66,129,9,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11016 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 392 52 112 112 240 368), lower := (rows 67 131 13 392 52 32 64 128 256), losses := [] }

theorem u11016 : Upper (D 8) (R 8) [66,129,9,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11017 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 392 84 48 112 176 304), lower := (rows 67 131 13 392 84 32 64 128 256), losses := [] }

theorem u11017 : Upper (D 8) (R 8) [66,129,9,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11018 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 392 112 52 116 180 308), lower := (rows 67 131 13 392 112 32 64 128 256), losses := [] }

theorem u11018 : Upper (D 8) (R 8) [66,129,9,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11019 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 131 28 41 52 480 480 480 480), lower := (rows 67 131 28 41 52 32 64 128 256), losses := [] }

theorem u11019 : Upper (D 8) (R 8) [66,129,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11020 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 112 420 484 420 420), lower := (rows 67 131 28 41 112 32 64 128 256), losses := [] }

theorem u11020 : Upper (D 8) (R 8) [66,129,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11021 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 176 356 356 484 356), lower := (rows 67 131 28 41 176 32 64 128 256), losses := [] }

theorem u11021 : Upper (D 8) (R 8) [66,129,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11022 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 276 224 224 224 480), lower := (rows 67 131 28 41 276 32 64 128 256), losses := [] }

theorem u11022 : Upper (D 8) (R 8) [66,129,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11023 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 304 228 228 228 484), lower := (rows 67 131 28 41 304 32 64 128 256), losses := [] }

theorem u11023 : Upper (D 8) (R 8) [66,129,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11024 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 336 164 228 164 420), lower := (rows 67 131 28 41 336 32 64 128 256), losses := [] }

theorem u11024 : Upper (D 8) (R 8) [66,129,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11025 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 400 100 100 228 356), lower := (rows 67 131 28 41 400 32 64 128 256), losses := [] }

theorem u11025 : Upper (D 8) (R 8) [66,129,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11026 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 44 81 416 480 416 416), lower := (rows 67 131 28 44 81 32 64 128 256), losses := [] }

theorem u11026 : Upper (D 8) (R 8) [66,129,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11027 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 44 112 417 481 417 417), lower := (rows 67 131 28 44 112 32 64 128 256), losses := [] }

theorem u11027 : Upper (D 8) (R 8) [66,129,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11028 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 28 44 145 352 352 480 352), lower := (rows 67 131 28 44 145 32 64 128 256), losses := [] }

theorem u11028 : Upper (D 8) (R 8) [66,129,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11029 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 44 176 353 353 481 353), lower := (rows 67 131 28 44 176 32 64 128 256), losses := [] }

theorem u11029 : Upper (D 8) (R 8) [66,129,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11030 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 28 44 208 289 353 417 289), lower := (rows 67 131 28 44 208 32 64 128 256), losses := [] }

theorem u11030 : Upper (D 8) (R 8) [66,129,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11031 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 44 273 224 224 224 480), lower := (rows 67 131 28 44 273 32 64 128 256), losses := [] }

theorem u11031 : Upper (D 8) (R 8) [66,129,24,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11032 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 44 304 225 225 225 481), lower := (rows 67 131 28 44 304 32 64 128 256), losses := [] }

theorem u11032 : Upper (D 8) (R 8) [66,129,24,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11033 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 44 336 161 225 161 417), lower := (rows 67 131 28 44 336 32 64 128 256), losses := [] }

theorem u11033 : Upper (D 8) (R 8) [66,129,24,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11034 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 28 44 400 97 97 225 353), lower := (rows 67 131 28 44 400 32 64 128 256), losses := [] }

theorem u11034 : Upper (D 8) (R 8) [66,129,24,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11035 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 73 176 292 356 420 292), lower := (rows 67 131 28 73 176 32 64 128 256), losses := [] }

theorem u11035 : Upper (D 8) (R 8) [66,129,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11036 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 73 276 160 224 160 416), lower := (rows 67 131 28 73 276 32 64 128 256), losses := [] }

theorem u11036 : Upper (D 8) (R 8) [66,129,24,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11037 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 73 304 164 228 164 420), lower := (rows 67 131 28 73 304 32 64 128 256), losses := [] }

theorem u11037 : Upper (D 8) (R 8) [66,129,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11038 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 73 400 36 100 164 292), lower := (rows 67 131 28 73 400 32 64 128 256), losses := [] }

theorem u11038 : Upper (D 8) (R 8) [66,129,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11039 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 76 176 289 353 417 289), lower := (rows 67 131 28 76 176 32 64 128 256), losses := [] }

theorem u11039 : Upper (D 8) (R 8) [66,129,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11039
end Delivery.IrregularNine14.P08
