import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(4,5),(4,6)], upper := (rows 35 14 196 328 400 33 96 145 273), lower := (rows 35 14 196 328 400 33 96 128 256), losses := [] }

theorem u900 : Upper (D 9) (R 9) [34,12,192,320,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b900 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 67 13 28 176 288 192 448 320), lower := (rows 35 67 13 28 176 288 192 128 256), losses := [] }

theorem u901 : Upper (D 9) (R 9) [34,65,9,20,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b901 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 28 176 288 320 192 448), lower := (rows 35 67 13 28 176 288 320 128 256), losses := [] }

theorem u902 : Upper (D 9) (R 9) [34,65,9,20,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b902 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 28 208 288 96 384 384), lower := (rows 35 67 13 28 208 288 96 128 256), losses := [] }

theorem u903 : Upper (D 9) (R 9) [34,65,9,20,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b903 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,7)], upper := (rows 35 67 13 28 208 288 192 416 288), lower := (rows 35 67 13 28 208 288 192 128 256), losses := [] }

theorem u904 : Upper (D 9) (R 9) [34,65,9,20,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b904 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 28 208 288 320 160 416), lower := (rows 35 67 13 28 208 288 320 128 256), losses := [] }

theorem u905 : Upper (D 9) (R 9) [34,65,9,20,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b905 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b906 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(3,8)], upper := (rows 35 67 13 28 400 160 96 448 320), lower := (rows 35 67 13 28 400 160 96 128 256), losses := [] }

theorem u906 : Upper (D 9) (R 9) [34,65,9,20,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b906 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 323, targets := 128 },{ cop := 6, region := 163, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 28 400 160 320 224 352), lower := (rows 35 67 13 28 400 160 320 128 256), losses := [] }

theorem u907 : Upper (D 9) (R 9) [34,65,9,20,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b907 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 148 288 192 448 320), lower := (rows 35 67 13 56 148 288 192 128 256), losses := [] }

theorem u908 : Upper (D 9) (R 9) [34,65,9,48,132,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b908 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 148 288 320 192 448), lower := (rows 35 67 13 56 148 288 320 128 256), losses := [] }

theorem u909 : Upper (D 9) (R 9) [34,65,9,48,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b909 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 56 208 288 68 384 384), lower := (rows 35 67 13 56 208 288 68 128 256), losses := [] }

theorem u910 : Upper (D 9) (R 9) [34,65,9,48,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b910 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 67 13 56 208 288 192 388 260), lower := (rows 35 67 13 56 208 288 192 128 256), losses := [] }

theorem u911 : Upper (D 9) (R 9) [34,65,9,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b911 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 208 288 320 132 388), lower := (rows 35 67 13 56 208 288 320 128 256), losses := [] }

theorem u912 : Upper (D 9) (R 9) [34,65,9,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b912 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 88 148 288 96 384 384), lower := (rows 35 67 13 88 148 288 96 128 256), losses := [] }

theorem u913 : Upper (D 9) (R 9) [34,65,9,80,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b913 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 35 67 13 88 148 288 192 416 288), lower := (rows 35 67 13 88 148 288 192 128 256), losses := [] }

theorem u914 : Upper (D 9) (R 9) [34,65,9,80,132,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b914 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 88 148 288 320 160 416), lower := (rows 35 67 13 88 148 288 320 128 256), losses := [] }

theorem u915 : Upper (D 9) (R 9) [34,65,9,80,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b915 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 88 176 288 68 384 384), lower := (rows 35 67 13 88 176 288 68 128 256), losses := [] }

theorem u916 : Upper (D 9) (R 9) [34,65,9,80,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b916 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 88 176 288 192 388 260), lower := (rows 35 67 13 88 176 288 192 128 256), losses := [] }

theorem u917 : Upper (D 9) (R 9) [34,65,9,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b917 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 88 176 288 320 132 388), lower := (rows 35 67 13 88 176 288 320 128 256), losses := [] }

theorem u918 : Upper (D 9) (R 9) [34,65,9,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b918 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 140 176 288 80 448 320), lower := (rows 35 67 13 140 176 288 80 128 256), losses := [] }

theorem u919 : Upper (D 9) (R 9) [34,65,9,132,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b919 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 176 288 320 208 336), lower := (rows 35 67 13 140 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 368 144 272), good := (rows 67 67 15 140 464 320 320 128 320) }] }

theorem u920 : Upper (D 9) (R 9) [34,65,9,132,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b920 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 2, region := 424, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(3,6)], upper := (rows 35 67 13 140 208 288 80 416 288), lower := (rows 35 67 13 140 208 288 80 128 256), losses := [] }

theorem u921 : Upper (D 9) (R 9) [34,65,9,132,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b921 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 272, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 140 208 288 96 400 272), lower := (rows 35 67 13 140 208 288 96 128 256), losses := [] }

theorem u922 : Upper (D 9) (R 9) [34,65,9,132,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b922 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 208 288 320 176 304), lower := (rows 35 67 13 140 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 352 128 256), good := (rows 67 67 15 140 208 320 320 128 320) }] }

theorem u923 : Upper (D 9) (R 9) [34,65,9,132,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b923 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 5, region := 83, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 67 13 140 336 288 80 160 416), lower := (rows 35 67 13 140 336 288 80 128 256), losses := [] }

theorem u924 : Upper (D 9) (R 9) [34,65,9,132,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b924 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 140 336 288 96 144 400), lower := (rows 35 67 13 140 336 288 96 128 256), losses := [] }

theorem u925 : Upper (D 9) (R 9) [34,65,9,132,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b925 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 307, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,7)], upper := (rows 35 67 13 140 336 288 192 176 304), lower := (rows 35 67 13 140 336 288 192 128 256), losses := [] }

theorem u926 : Upper (D 9) (R 9) [34,65,9,132,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b926 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 400 288 80 224 352), lower := (rows 35 67 13 140 400 288 80 128 256), losses := [] }

theorem u927 : Upper (D 9) (R 9) [34,65,9,132,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b927 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 140 400 288 96 208 336), lower := (rows 35 67 13 140 400 288 96 128 256), losses := [] }

theorem u928 : Upper (D 9) (R 9) [34,65,9,132,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b928 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b929 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 6, region := 291, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 52 288 192 448 320), lower := (rows 35 67 13 152 52 288 192 128 256), losses := [] }

theorem u929 : Upper (D 9) (R 9) [34,65,9,144,36,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b929 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 52 288 320 192 448), lower := (rows 35 67 13 152 52 288 320 128 256), losses := [] }

theorem u930 : Upper (D 9) (R 9) [34,65,9,144,36,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b930 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 152 84 288 96 384 384), lower := (rows 35 67 13 152 84 288 96 128 256), losses := [] }

theorem u931 : Upper (D 9) (R 9) [34,65,9,144,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b931 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 291, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 84 288 192 416 288), lower := (rows 35 67 13 152 84 288 192 128 256), losses := [] }

theorem u932 : Upper (D 9) (R 9) [34,65,9,144,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b932 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 84 288 320 160 416), lower := (rows 35 67 13 152 84 288 320 128 256), losses := [] }

theorem u933 : Upper (D 9) (R 9) [34,65,9,144,68,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b933 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 2, region := 504, targets := 1 }], pairs := [(2,5),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 152 276 288 96 192 448), lower := (rows 35 67 13 152 276 288 96 128 256), losses := [] }

theorem u934 : Upper (D 9) (R 9) [34,65,9,144,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b934 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 195, targets := 256 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,0),(4,0)], upper := (rows 35 67 13 152 276 288 192 224 352), lower := (rows 35 67 13 152 276 288 192 128 256), losses := [] }

theorem u935 : Upper (D 9) (R 9) [34,65,9,144,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b935 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 13 152 304 160 68 448 320), lower := (rows 35 67 13 152 304 160 68 128 256), losses := [] }

theorem u936 : Upper (D 9) (R 9) [34,65,9,144,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b936 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 67, targets := 128 },{ cop := 2, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 304 160 320 196 324), lower := (rows 35 67 13 152 304 160 320 128 256), losses := [] }

theorem u937 : Upper (D 9) (R 9) [34,65,9,144,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b937 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 103, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 152 336 36 96 384 384), lower := (rows 35 67 13 152 336 36 96 128 256), losses := [] }

theorem u938 : Upper (D 9) (R 9) [34,65,9,144,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b938 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 13 152 336 36 192 416 288), lower := (rows 35 67 13 152 336 36 192 128 256), losses := [] }

theorem u939 : Upper (D 9) (R 9) [34,65,9,144,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b939 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 152 336 36 320 160 416), lower := (rows 35 67 13 152 336 36 320 128 256), losses := [] }

theorem u940 : Upper (D 9) (R 9) [34,65,9,144,320,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b940 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 152 336 160 68 416 288), lower := (rows 35 67 13 152 336 160 68 128 256), losses := [] }

theorem u941 : Upper (D 9) (R 9) [34,65,9,144,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b941 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 152 336 160 96 388 260), lower := (rows 35 67 13 152 336 160 96 128 256), losses := [] }

theorem u942 : Upper (D 9) (R 9) [34,65,9,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b942 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 13 152 336 160 320 164 292), lower := (rows 35 67 13 152 336 160 320 128 256), losses := [] }

theorem u943 : Upper (D 9) (R 9) [34,65,9,144,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b943 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 13 168 208 288 68 400 272), lower := (rows 35 67 13 168 208 288 68 128 256), losses := [] }

theorem u944 : Upper (D 9) (R 9) [34,65,9,160,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b944 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 13 168 208 288 80 388 260), lower := (rows 35 67 13 168 208 288 80 128 256), losses := [] }

theorem u945 : Upper (D 9) (R 9) [34,65,9,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b945 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 208 288 320 148 276), lower := (rows 35 67 13 168 208 288 320 128 256), losses := [] }

theorem u946 : Upper (D 9) (R 9) [34,65,9,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b946 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 276 288 80 192 448), lower := (rows 35 67 13 168 276 288 80 128 256), losses := [] }

theorem u947 : Upper (D 9) (R 9) [34,65,9,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b947 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 35 67 13 168 276 288 192 208 336), lower := (rows 35 67 13 168 276 288 192 128 256), losses := [] }

theorem u948 : Upper (D 9) (R 9) [34,65,9,160,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b948 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 200 52 288 80 384 384), lower := (rows 35 67 13 200 52 288 80 128 256), losses := [] }

theorem u949 : Upper (D 9) (R 9) [34,65,9,192,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b949 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 13 200 52 288 192 400 272), lower := (rows 35 67 13 200 52 288 192 128 256), losses := [] }

theorem u950 : Upper (D 9) (R 9) [34,65,9,192,36,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b950 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 200 52 288 320 144 400), lower := (rows 35 67 13 200 52 288 320 128 256), losses := [] }

theorem u951 : Upper (D 9) (R 9) [34,65,9,192,36,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b951 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 200 176 288 68 400 272), lower := (rows 35 67 13 200 176 288 68 128 256), losses := [] }

theorem u952 : Upper (D 9) (R 9) [34,65,9,192,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b952 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 200 176 288 80 388 260), lower := (rows 35 67 13 200 176 288 80 128 256), losses := [] }

theorem u953 : Upper (D 9) (R 9) [34,65,9,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b953 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 200 176 288 320 148 276), lower := (rows 35 67 13 200 176 288 320 128 256), losses := [] }

theorem u954 : Upper (D 9) (R 9) [34,65,9,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b954 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 200 276 48 96 384 384), lower := (rows 35 67 13 200 276 48 96 128 256), losses := [] }

theorem u955 : Upper (D 9) (R 9) [34,65,9,192,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b955 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 200 276 48 192 416 288), lower := (rows 35 67 13 200 276 48 192 128 256), losses := [] }

theorem u956 : Upper (D 9) (R 9) [34,65,9,192,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b956 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 200 276 48 320 160 416), lower := (rows 35 67 13 200 276 48 320 128 256), losses := [] }

theorem u957 : Upper (D 9) (R 9) [34,65,9,192,260,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b957 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 200 276 288 80 160 416), lower := (rows 35 67 13 200 276 288 80 128 256), losses := [] }

theorem u958 : Upper (D 9) (R 9) [34,65,9,192,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b958 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 200 276 288 96 144 400), lower := (rows 35 67 13 200 276 288 96 128 256), losses := [] }

theorem u959 : Upper (D 9) (R 9) [34,65,9,192,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b959 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P09
