import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9900 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 26 280 33 100 228 356), lower := (rows 7 35 196 26 280 33 64 128 256), losses := [] }

theorem u9900 : Upper (D 6) (R 6) [6,33,192,18,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9900
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9901 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 26 280 36 97 225 353), lower := (rows 7 35 196 26 280 36 64 128 256), losses := [] }

theorem u9901 : Upper (D 6) (R 6) [6,33,192,18,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9901
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9902 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 196 26 280 96 101 165 293), lower := (rows 7 35 196 26 280 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 111 67 131 259), good := (rows 485 485 228 508 316 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 26 280 96 96 128 256) }] }

theorem u9902 : Upper (D 6) (R 6) [6,33,192,18,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9902
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9903 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 26 304 33 76 204 332), lower := (rows 7 35 196 26 304 33 64 128 256), losses := [] }

theorem u9903 : Upper (D 6) (R 6) [6,33,192,18,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9903
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9904 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 26 304 36 73 201 329), lower := (rows 7 35 196 26 304 36 64 128 256), losses := [] }

theorem u9904 : Upper (D 6) (R 6) [6,33,192,18,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9904
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9905 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 35 196 26 304 40 69 197 325), lower := (rows 7 35 196 26 304 40 64 128 256), losses := [] }

theorem u9905 : Upper (D 6) (R 6) [6,33,192,18,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9905
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9906 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 35 196 26 304 96 77 141 269), lower := (rows 7 35 196 26 304 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 26 304 96 96 128 256) }] }

theorem u9906 : Upper (D 6) (R 6) [6,33,192,18,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9906
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9907 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 26 336 33 108 172 300), lower := (rows 7 35 196 26 336 33 64 128 256), losses := [] }

theorem u9907 : Upper (D 6) (R 6) [6,33,192,18,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9907
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9908 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 26 336 36 105 169 297), lower := (rows 7 35 196 26 336 36 64 128 256), losses := [] }

theorem u9908 : Upper (D 6) (R 6) [6,33,192,18,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9908
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9909 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 26 336 40 101 165 293), lower := (rows 7 35 196 26 336 40 64 128 256), losses := [] }

theorem u9909 : Upper (D 6) (R 6) [6,33,192,18,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9909
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9910 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 28 81 34 360 424 296), lower := (rows 7 35 196 28 81 34 64 128 256), losses := [] }

theorem u9910 : Upper (D 6) (R 6) [6,33,192,20,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9910
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9911 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 81 40 354 418 290), lower := (rows 7 35 196 28 81 40 64 128 256), losses := [] }

theorem u9911 : Upper (D 6) (R 6) [6,33,192,20,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9911
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9912 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 81 288 106 170 298), lower := (rows 7 35 196 28 81 288 64 128 256), losses := [] }

theorem u9912 : Upper (D 6) (R 6) [6,33,192,20,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9912
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9913 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 28 82 33 360 424 296), lower := (rows 7 35 196 28 82 33 64 128 256), losses := [] }

theorem u9913 : Upper (D 6) (R 6) [6,33,192,20,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9913
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9914 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 82 40 353 417 289), lower := (rows 7 35 196 28 82 40 64 128 256), losses := [] }

theorem u9914 : Upper (D 6) (R 6) [6,33,192,20,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9914
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9915 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 82 288 105 169 297), lower := (rows 7 35 196 28 82 288 64 128 256), losses := [] }

theorem u9915 : Upper (D 6) (R 6) [6,33,192,20,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9915
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9916 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 28 112 33 330 394 266), lower := (rows 7 35 196 28 112 33 64 128 256), losses := [] }

theorem u9916 : Upper (D 6) (R 6) [6,33,192,20,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9916
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9917 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 28 112 34 329 393 265), lower := (rows 7 35 196 28 112 34 64 128 256), losses := [] }

theorem u9917 : Upper (D 6) (R 6) [6,33,192,20,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9917
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9918 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 28 112 40 323 387 259), lower := (rows 7 35 196 28 112 40 64 128 256), losses := [] }

theorem u9918 : Upper (D 6) (R 6) [6,33,192,20,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9918
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9919 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 112 288 75 139 267), lower := (rows 7 35 196 28 112 288 64 128 256), losses := [] }

theorem u9919 : Upper (D 6) (R 6) [6,33,192,20,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9919
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9920 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 28 273 34 104 232 360), lower := (rows 7 35 196 28 273 34 64 128 256), losses := [] }

theorem u9920 : Upper (D 6) (R 6) [6,33,192,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9920
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9921 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 273 40 98 226 354), lower := (rows 7 35 196 28 273 40 64 128 256), losses := [] }

theorem u9921 : Upper (D 6) (R 6) [6,33,192,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9921
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9922 : PairBound 9 := { available := 42, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 28 273 96 106 170 298), lower := (rows 7 35 196 28 273 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 56 275 96 96 128 256) },{ target := 6, region := (rows 1 2 4 9 19 32 0 130 258), good := (rows 415 443 132 28 281 32 0 128 256) }] }

theorem u9922 : Upper (D 6) (R 6) [6,33,192,20,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9922
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9923 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 28 274 33 104 232 360), lower := (rows 7 35 196 28 274 33 64 128 256), losses := [] }

theorem u9923 : Upper (D 6) (R 6) [6,33,192,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9923
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9924 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 274 40 97 225 353), lower := (rows 7 35 196 28 274 40 64 128 256), losses := [] }

theorem u9924 : Upper (D 6) (R 6) [6,33,192,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9924
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9925 : PairBound 9 := { available := 41, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 28 274 96 105 169 297), lower := (rows 7 35 196 28 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 56 274 96 96 128 256) },{ target := 6, region := (rows 1 2 4 9 19 32 0 130 258), good := (rows 415 443 132 28 402 32 0 128 256) }] }

theorem u9925 : Upper (D 6) (R 6) [6,33,192,20,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9925
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9926 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 28 280 33 98 226 354), lower := (rows 7 35 196 28 280 33 64 128 256), losses := [] }

theorem u9926 : Upper (D 6) (R 6) [6,33,192,20,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9926
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9927 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 28 280 34 97 225 353), lower := (rows 7 35 196 28 280 34 64 128 256), losses := [] }

theorem u9927 : Upper (D 6) (R 6) [6,33,192,20,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9927
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9928 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 28 280 96 99 163 291), lower := (rows 7 35 196 28 280 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 19 32 0 130 258), good := (rows 415 443 132 28 280 32 0 128 256) }] }

theorem u9928 : Upper (D 6) (R 6) [6,33,192,20,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9928
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9929 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 28 304 33 74 202 330), lower := (rows 7 35 196 28 304 33 64 128 256), losses := [] }

theorem u9929 : Upper (D 6) (R 6) [6,33,192,20,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9929
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9930 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 28 304 34 73 201 329), lower := (rows 7 35 196 28 304 34 64 128 256), losses := [] }

theorem u9930 : Upper (D 6) (R 6) [6,33,192,20,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9930
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9931 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 28 304 40 67 195 323), lower := (rows 7 35 196 28 304 40 64 128 256), losses := [] }

theorem u9931 : Upper (D 6) (R 6) [6,33,192,20,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9931
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9932 : PairBound 9 := { available := 11, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 28 304 96 75 139 267), lower := (rows 7 35 196 28 304 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 56 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 9 18 32 0 131 259), good := (rows 415 443 132 28 304 32 0 128 256) }] }

theorem u9932 : Upper (D 6) (R 6) [6,33,192,20,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9932
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9933 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 28 336 33 106 170 298), lower := (rows 7 35 196 28 336 33 64 128 256), losses := [] }

theorem u9933 : Upper (D 6) (R 6) [6,33,192,20,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9933
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9934 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 28 336 34 105 169 297), lower := (rows 7 35 196 28 336 34 64 128 256), losses := [] }

theorem u9934 : Upper (D 6) (R 6) [6,33,192,20,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9934
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9935 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 28 336 40 99 163 291), lower := (rows 7 35 196 28 336 40 64 128 256), losses := [] }

theorem u9935 : Upper (D 6) (R 6) [6,33,192,20,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9935
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9936 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 44 81 34 344 408 280), lower := (rows 7 35 196 44 81 34 64 128 256), losses := [] }

theorem u9936 : Upper (D 6) (R 6) [6,33,192,36,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9936
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9937 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 44 81 40 338 402 274), lower := (rows 7 35 196 44 81 40 64 128 256), losses := [] }

theorem u9937 : Upper (D 6) (R 6) [6,33,192,36,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9937
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9938 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 44 81 48 330 394 266), lower := (rows 7 35 196 44 81 48 64 128 256), losses := [] }

theorem u9938 : Upper (D 6) (R 6) [6,33,192,36,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9938
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9939 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 44 81 288 90 154 282), lower := (rows 7 35 196 44 81 288 64 128 256), losses := [] }

theorem u9939 : Upper (D 6) (R 6) [6,33,192,36,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9939
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9940 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 44 82 33 344 408 280), lower := (rows 7 35 196 44 82 33 64 128 256), losses := [] }

theorem u9940 : Upper (D 6) (R 6) [6,33,192,36,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9940
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9941 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 44 82 40 337 401 273), lower := (rows 7 35 196 44 82 40 64 128 256), losses := [] }

theorem u9941 : Upper (D 6) (R 6) [6,33,192,36,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9941
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9942 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 44 82 48 329 393 265), lower := (rows 7 35 196 44 82 48 64 128 256), losses := [] }

theorem u9942 : Upper (D 6) (R 6) [6,33,192,36,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9942
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9943 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 44 82 288 89 153 281), lower := (rows 7 35 196 44 82 288 64 128 256), losses := [] }

theorem u9943 : Upper (D 6) (R 6) [6,33,192,36,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9943
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9944 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 44 88 33 338 402 274), lower := (rows 7 35 196 44 88 33 64 128 256), losses := [] }

theorem u9944 : Upper (D 6) (R 6) [6,33,192,36,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9944
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9945 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 44 88 34 337 401 273), lower := (rows 7 35 196 44 88 34 64 128 256), losses := [] }

theorem u9945 : Upper (D 6) (R 6) [6,33,192,36,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9945
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9946 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 44 88 48 323 387 259), lower := (rows 7 35 196 44 88 48 64 128 256), losses := [] }

theorem u9946 : Upper (D 6) (R 6) [6,33,192,36,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9946
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9947 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 44 88 288 83 147 275), lower := (rows 7 35 196 44 88 288 64 128 256), losses := [] }

theorem u9947 : Upper (D 6) (R 6) [6,33,192,36,72,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9947
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9948 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 44 273 34 88 216 344), lower := (rows 7 35 196 44 273 34 64 128 256), losses := [] }

theorem u9948 : Upper (D 6) (R 6) [6,33,192,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9948
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9949 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 44 273 40 82 210 338), lower := (rows 7 35 196 44 273 40 64 128 256), losses := [] }

theorem u9949 : Upper (D 6) (R 6) [6,33,192,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9949
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9950 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 44 273 48 74 202 330), lower := (rows 7 35 196 44 273 48 64 128 256), losses := [] }

theorem u9950 : Upper (D 6) (R 6) [6,33,192,36,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9950
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9951 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 196 44 273 96 90 154 282), lower := (rows 7 35 196 44 273 96 64 128 256), losses := [] }

theorem u9951 : Upper (D 6) (R 6) [6,33,192,36,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9951
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9952 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 44 274 33 88 216 344), lower := (rows 7 35 196 44 274 33 64 128 256), losses := [] }

theorem u9952 : Upper (D 6) (R 6) [6,33,192,36,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9952
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9953 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 44 274 40 81 209 337), lower := (rows 7 35 196 44 274 40 64 128 256), losses := [] }

theorem u9953 : Upper (D 6) (R 6) [6,33,192,36,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9953
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9954 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 44 274 48 73 201 329), lower := (rows 7 35 196 44 274 48 64 128 256), losses := [] }

theorem u9954 : Upper (D 6) (R 6) [6,33,192,36,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9954
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9955 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 196 44 274 96 89 153 281), lower := (rows 7 35 196 44 274 96 64 128 256), losses := [] }

theorem u9955 : Upper (D 6) (R 6) [6,33,192,36,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9955
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9956 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 44 280 33 82 210 338), lower := (rows 7 35 196 44 280 33 64 128 256), losses := [] }

theorem u9956 : Upper (D 6) (R 6) [6,33,192,36,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9956
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9957 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 44 280 34 81 209 337), lower := (rows 7 35 196 44 280 34 64 128 256), losses := [] }

theorem u9957 : Upper (D 6) (R 6) [6,33,192,36,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9957
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9958 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 44 280 48 67 195 323), lower := (rows 7 35 196 44 280 48 64 128 256), losses := [] }

theorem u9958 : Upper (D 6) (R 6) [6,33,192,36,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9958
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9959 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 196 44 280 96 83 147 275), lower := (rows 7 35 196 44 280 96 64 128 256), losses := [] }

theorem u9959 : Upper (D 6) (R 6) [6,33,192,36,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9959
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9959
end Delivery.IrregularNine14.P06
