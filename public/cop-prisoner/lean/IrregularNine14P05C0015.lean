import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 276 33 72 162 290), lower := (rows 7 74 164 25 276 33 72 128 256), losses := [] }

theorem u900 : Upper (D 5) (R 5) [6,72,160,17,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 25 276 33 96 138 266), lower := (rows 7 74 164 25 276 33 96 128 256), losses := [] }

theorem u901 : Upper (D 5) (R 5) [6,72,160,17,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 25 276 34 65 168 296), lower := (rows 7 74 164 25 276 34 65 128 256), losses := [] }

theorem u902 : Upper (D 5) (R 5) [6,72,160,17,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b902
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 276 34 72 161 289), lower := (rows 7 74 164 25 276 34 72 128 256), losses := [] }

theorem u903 : Upper (D 5) (R 5) [6,72,160,17,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b903
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 164 25 276 34 96 137 265), lower := (rows 7 74 164 25 276 34 96 128 256), losses := [] }

theorem u904 : Upper (D 5) (R 5) [6,72,160,17,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b904
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 25 276 40 65 162 290), lower := (rows 7 74 164 25 276 40 65 128 256), losses := [] }

theorem u905 : Upper (D 5) (R 5) [6,72,160,17,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b906 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 25 276 40 66 161 289), lower := (rows 7 74 164 25 276 40 66 128 256), losses := [] }

theorem u906 : Upper (D 5) (R 5) [6,72,160,17,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 25 276 40 96 131 259), lower := (rows 7 74 164 25 276 40 96 128 256), losses := [] }

theorem u907 : Upper (D 5) (R 5) [6,72,160,17,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 25 304 33 66 140 268), lower := (rows 7 74 164 25 304 33 66 128 256), losses := [] }

theorem u908 : Upper (D 5) (R 5) [6,72,160,17,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 304 33 68 138 266), lower := (rows 7 74 164 25 304 33 68 128 256), losses := [] }

theorem u909 : Upper (D 5) (R 5) [6,72,160,17,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 304 33 72 134 262), lower := (rows 7 74 164 25 304 33 72 128 256), losses := [] }

theorem u910 : Upper (D 5) (R 5) [6,72,160,17,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 74 164 25 304 34 65 140 268), lower := (rows 7 74 164 25 304 34 65 128 256), losses := [] }

theorem u911 : Upper (D 5) (R 5) [6,72,160,17,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 304 34 68 137 265), lower := (rows 7 74 164 25 304 34 68 128 256), losses := [] }

theorem u912 : Upper (D 5) (R 5) [6,72,160,17,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 304 34 72 133 261), lower := (rows 7 74 164 25 304 34 72 128 256), losses := [] }

theorem u913 : Upper (D 5) (R 5) [6,72,160,17,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 74 164 25 304 40 65 134 262), lower := (rows 7 74 164 25 304 40 65 128 256), losses := [] }

theorem u914 : Upper (D 5) (R 5) [6,72,160,17,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 25 304 40 66 133 261), lower := (rows 7 74 164 25 304 40 66 128 256), losses := [] }

theorem u915 : Upper (D 5) (R 5) [6,72,160,17,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 304 40 68 131 259), lower := (rows 7 74 164 25 304 40 68 128 256), losses := [] }

theorem u916 : Upper (D 5) (R 5) [6,72,160,17,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 74, targets := 4 }], pairs := [(1,2)], upper := (rows 7 74 164 26 49 288 65 140 268), lower := (rows 7 74 164 26 49 288 65 128 256), losses := [] }

theorem u917 : Upper (D 5) (R 5) [6,72,160,18,33,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2)], upper := (rows 7 74 164 26 49 288 68 137 265), lower := (rows 7 74 164 26 49 288 68 128 256), losses := [] }

theorem u918 : Upper (D 5) (R 5) [6,72,160,18,33,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 26 49 288 72 133 261), lower := (rows 7 74 164 26 49 288 72 128 256), losses := [] }

theorem u919 : Upper (D 5) (R 5) [6,72,160,18,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b919
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 26 273 33 68 168 296), lower := (rows 7 74 164 26 273 33 68 128 256), losses := [] }

theorem u920 : Upper (D 5) (R 5) [6,72,160,18,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 26 273 33 72 164 292), lower := (rows 7 74 164 26 273 33 72 128 256), losses := [] }

theorem u921 : Upper (D 5) (R 5) [6,72,160,18,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 26 273 33 96 140 268), lower := (rows 7 74 164 26 273 33 96 128 256), losses := [] }

theorem u922 : Upper (D 5) (R 5) [6,72,160,18,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b922
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 26 276 33 65 168 296), lower := (rows 7 74 164 26 276 33 65 128 256), losses := [] }

theorem u923 : Upper (D 5) (R 5) [6,72,160,18,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 26 276 33 72 161 289), lower := (rows 7 74 164 26 276 33 72 128 256), losses := [] }

theorem u924 : Upper (D 5) (R 5) [6,72,160,18,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 26 276 33 96 137 265), lower := (rows 7 74 164 26 276 33 96 128 256), losses := [] }

theorem u925 : Upper (D 5) (R 5) [6,72,160,18,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 12, camps := [], pairs := [(1,0),(2,0)], upper := (rows 7 74 164 26 304 33 65 140 268), lower := (rows 7 74 164 26 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 52 9 52 32 64 169 297), good := (rows 414 458 436 414 436 444 458 128 256) }] }

theorem u926 : Upper (D 5) (R 5) [6,72,160,18,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 26 304 33 68 137 265), lower := (rows 7 74 164 26 304 33 68 128 256), losses := [] }

theorem u927 : Upper (D 5) (R 5) [6,72,160,18,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 164 26 304 33 72 133 261), lower := (rows 7 74 164 26 304 33 72 128 256), losses := [] }

theorem u928 : Upper (D 5) (R 5) [6,72,160,18,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b929 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 28 273 33 66 168 296), lower := (rows 7 74 164 28 273 33 66 128 256), losses := [] }

theorem u929 : Upper (D 5) (R 5) [6,72,160,20,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b929
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 28 273 33 72 162 290), lower := (rows 7 74 164 28 273 33 72 128 256), losses := [] }

theorem u930 : Upper (D 5) (R 5) [6,72,160,20,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b930
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 28 273 33 96 138 266), lower := (rows 7 74 164 28 273 33 96 128 256), losses := [] }

theorem u931 : Upper (D 5) (R 5) [6,72,160,20,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 28 273 34 65 168 296), lower := (rows 7 74 164 28 273 34 65 128 256), losses := [] }

theorem u932 : Upper (D 5) (R 5) [6,72,160,20,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b932
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 28 273 34 72 161 289), lower := (rows 7 74 164 28 273 34 72 128 256), losses := [] }

theorem u933 : Upper (D 5) (R 5) [6,72,160,20,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 164 28 273 34 96 137 265), lower := (rows 7 74 164 28 273 34 96 128 256), losses := [] }

theorem u934 : Upper (D 5) (R 5) [6,72,160,20,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 28 273 40 65 162 290), lower := (rows 7 74 164 28 273 40 65 128 256), losses := [] }

theorem u935 : Upper (D 5) (R 5) [6,72,160,20,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 28 273 40 66 161 289), lower := (rows 7 74 164 28 273 40 66 128 256), losses := [] }

theorem u936 : Upper (D 5) (R 5) [6,72,160,20,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 28 273 40 96 131 259), lower := (rows 7 74 164 28 273 40 96 128 256), losses := [] }

theorem u937 : Upper (D 5) (R 5) [6,72,160,20,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 28 274 33 65 168 296), lower := (rows 7 74 164 28 274 33 65 128 256), losses := [] }

theorem u938 : Upper (D 5) (R 5) [6,72,160,20,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 28 274 33 72 161 289), lower := (rows 7 74 164 28 274 33 72 128 256), losses := [] }

theorem u939 : Upper (D 5) (R 5) [6,72,160,20,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b939
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 28 274 33 96 137 265), lower := (rows 7 74 164 28 274 33 96 128 256), losses := [] }

theorem u940 : Upper (D 5) (R 5) [6,72,160,20,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 42 273 33 68 152 280), lower := (rows 7 74 164 42 273 33 68 128 256), losses := [] }

theorem u941 : Upper (D 5) (R 5) [6,72,160,34,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 436, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 42 273 33 72 148 276), lower := (rows 7 74 164 42 273 33 72 128 256), losses := [] }

theorem u942 : Upper (D 5) (R 5) [6,72,160,34,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b942
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 42 273 33 80 140 268), lower := (rows 7 74 164 42 273 33 80 128 256), losses := [] }

theorem u943 : Upper (D 5) (R 5) [6,72,160,34,257,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b943
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 42 273 48 65 140 268), lower := (rows 7 74 164 42 273 48 65 128 256), losses := [] }

theorem u944 : Upper (D 5) (R 5) [6,72,160,34,257,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2)], upper := (rows 7 74 164 42 273 48 68 137 265), lower := (rows 7 74 164 42 273 48 68 128 256), losses := [] }

theorem u945 : Upper (D 5) (R 5) [6,72,160,34,257,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b945
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 164 42 273 48 72 133 261), lower := (rows 7 74 164 42 273 48 72 128 256), losses := [] }

theorem u946 : Upper (D 5) (R 5) [6,72,160,34,257,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 42 276 33 65 152 280), lower := (rows 7 74 164 42 276 33 65 128 256), losses := [] }

theorem u947 : Upper (D 5) (R 5) [6,72,160,34,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b947
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 436, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 42 276 33 72 145 273), lower := (rows 7 74 164 42 276 33 72 128 256), losses := [] }

theorem u948 : Upper (D 5) (R 5) [6,72,160,34,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 40, targets := 4 }], pairs := [(3,2)], upper := (rows 7 74 164 42 276 33 80 137 265), lower := (rows 7 74 164 42 276 33 80 128 256), losses := [] }

theorem u949 : Upper (D 5) (R 5) [6,72,160,34,260,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b949
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r950 : Route 9 := (fun mask => (mask,id))

def c950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u950 : Upper (D 5) (R 5) [6,72,160,34,260,16,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,260,16,1] 13 (by decide) (choices 1) [1,8] r950 c950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u52
  · exact u53

def b951 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 164 42 276 48 72 129 257), lower := (rows 7 74 164 42 276 48 72 128 256), losses := [] }

theorem u951 : Upper (D 5) (R 5) [6,72,160,34,260,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 42 280 33 65 148 276), lower := (rows 7 74 164 42 280 33 65 128 256), losses := [] }

theorem u952 : Upper (D 5) (R 5) [6,72,160,34,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b952
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 42 280 33 68 145 273), lower := (rows 7 74 164 42 280 33 68 128 256), losses := [] }

theorem u953 : Upper (D 5) (R 5) [6,72,160,34,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b953
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 42 280 33 80 133 261), lower := (rows 7 74 164 42 280 33 80 128 256), losses := [] }

theorem u954 : Upper (D 5) (R 5) [6,72,160,34,264,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b954
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 56 274 33 65 140 268), lower := (rows 7 74 164 56 274 33 65 128 256), losses := [] }

theorem u955 : Upper (D 5) (R 5) [6,72,160,48,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b955
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 56 274 33 68 137 265), lower := (rows 7 74 164 56 274 33 68 128 256), losses := [] }

theorem u956 : Upper (D 5) (R 5) [6,72,160,48,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 56 274 33 72 133 261), lower := (rows 7 74 164 56 274 33 72 128 256), losses := [] }

theorem u957 : Upper (D 5) (R 5) [6,72,160,48,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 10, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 74 164 56 276 33 65 138 266), lower := (rows 7 74 164 56 276 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 64 131 259), good := (rows 414 458 188 60 284 444 464 128 256) }] }

theorem u958 : Upper (D 5) (R 5) [6,72,160,48,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 56 276 33 66 137 265), lower := (rows 7 74 164 56 276 33 66 128 256), losses := [] }

theorem u959 : Upper (D 5) (R 5) [6,72,160,48,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b959
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P05
