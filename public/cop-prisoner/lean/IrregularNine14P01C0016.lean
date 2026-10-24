import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 274 70 200 144 33 106 170 298), lower := (rows 53 274 70 200 144 33 64 128 256), losses := [] }

theorem u960 : Upper (D 1) (R 1) [52,272,66,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 70 200 144 34 105 169 297), lower := (rows 53 274 70 200 144 34 64 128 256), losses := [] }

theorem u961 : Upper (D 1) (R 1) [52,272,66,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 274 70 200 144 40 99 163 291), lower := (rows 53 274 70 200 144 40 64 128 256), losses := [] }

theorem u962 : Upper (D 1) (R 1) [52,272,66,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 53 322 7 138 24 160 112 240 368), lower := (rows 53 322 7 138 24 160 64 128 256), losses := [] }

theorem u963 : Upper (D 1) (R 1) [52,320,3,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 7 138 48 160 88 216 344), lower := (rows 53 322 7 138 48 160 64 128 256), losses := [] }

theorem u964 : Upper (D 1) (R 1) [52,320,3,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 56, camps := [], pairs := [(3,6)], upper := (rows 53 322 7 138 80 160 120 184 312), lower := (rows 53 322 7 138 80 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 16 173 0 129 257), good := (rows 445 258 431 170 16 160 0 160 256) }] }

theorem u965 : Upper (D 1) (R 1) [52,320,3,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 7 200 18 160 120 184 312), lower := (rows 53 322 7 200 18 160 64 128 256), losses := [] }

theorem u966 : Upper (D 1) (R 1) [52,320,3,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b966
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 322 7 200 24 160 114 178 306), lower := (rows 53 322 7 200 24 160 64 128 256), losses := [] }

theorem u967 : Upper (D 1) (R 1) [52,320,3,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 7 200 48 160 90 154 282), lower := (rows 53 322 7 200 48 160 64 128 256), losses := [] }

theorem u968 : Upper (D 1) (R 1) [52,320,3,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b968
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6)], upper := (rows 53 322 13 138 18 48 224 224 480), lower := (rows 53 322 13 138 18 48 64 128 256), losses := [] }

theorem u969 : Upper (D 1) (R 1) [52,320,9,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b969
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 176, camps := [], pairs := [(0,7)], upper := (rows 53 322 13 138 18 96 240 176 432), lower := (rows 53 322 13 138 18 96 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 26 98 64 0 256), good := (rows 53 370 29 63 50 96 96 0 256) }] }

theorem u970 : Upper (D 1) (R 1) [52,320,9,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b970
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6)], upper := (rows 53 322 13 138 18 160 112 240 368), lower := (rows 53 322 13 138 18 160 64 128 256), losses := [] }

theorem u971 : Upper (D 1) (R 1) [52,320,9,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 13 138 48 96 210 146 402), lower := (rows 53 322 13 138 48 96 64 128 256), losses := [] }

theorem u972 : Upper (D 1) (R 1) [52,320,9,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 13 138 80 160 114 178 306), lower := (rows 53 322 13 138 80 160 64 128 256), losses := [] }

theorem u973 : Upper (D 1) (R 1) [52,320,9,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b973
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 13 200 18 34 240 176 432), lower := (rows 53 322 13 200 18 34 64 128 256), losses := [] }

theorem u974 : Upper (D 1) (R 1) [52,320,9,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b974
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 13 200 18 48 226 162 418), lower := (rows 53 322 13 200 18 48 64 128 256), losses := [] }

theorem u975 : Upper (D 1) (R 1) [52,320,9,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 13 200 18 160 114 178 306), lower := (rows 53 322 13 200 18 160 64 128 256), losses := [] }

theorem u976 : Upper (D 1) (R 1) [52,320,9,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b976
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 14 137 18 96 240 176 432), lower := (rows 53 322 14 137 18 96 64 128 256), losses := [] }

theorem u977 : Upper (D 1) (R 1) [52,320,10,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b977
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 14 137 48 96 210 146 402), lower := (rows 53 322 14 137 48 96 64 128 256), losses := [] }

theorem u978 : Upper (D 1) (R 1) [52,320,10,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b978
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 14 137 80 160 114 178 306), lower := (rows 53 322 14 137 80 160 64 128 256), losses := [] }

theorem u979 : Upper (D 1) (R 1) [52,320,10,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b979
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 322 134 11 24 96 240 176 432), lower := (rows 53 322 134 11 24 96 64 128 256), losses := [] }

theorem u980 : Upper (D 1) (R 1) [52,320,130,3,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 11 48 96 216 152 408), lower := (rows 53 322 134 11 48 96 64 128 256), losses := [] }

theorem u981 : Upper (D 1) (R 1) [52,320,130,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b981
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 134 11 80 160 120 184 312), lower := (rows 53 322 134 11 80 160 64 128 256), losses := [] }

theorem u982 : Upper (D 1) (R 1) [52,320,130,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 176, camps := [], pairs := [(2,1)], upper := (rows 53 322 140 11 18 96 240 176 432), lower := (rows 53 322 140 11 18 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 123 81 145 273), good := (rows 501 352 172 493 496 96 96 128 256) }] }

theorem u983 : Upper (D 1) (R 1) [52,320,136,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b983
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 140 11 48 96 210 146 402), lower := (rows 53 322 140 11 48 96 64 128 256), losses := [] }

theorem u984 : Upper (D 1) (R 1) [52,320,136,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 140 11 80 160 114 178 306), lower := (rows 53 322 140 11 80 160 64 128 256), losses := [] }

theorem u985 : Upper (D 1) (R 1) [52,320,136,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 140 73 18 34 240 176 432), lower := (rows 53 322 140 73 18 34 64 128 256), losses := [] }

theorem u986 : Upper (D 1) (R 1) [52,320,136,65,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 140 73 18 48 226 162 418), lower := (rows 53 322 140 73 18 48 64 128 256), losses := [] }

theorem u987 : Upper (D 1) (R 1) [52,320,136,65,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b987
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 140 73 18 160 114 178 306), lower := (rows 53 322 140 73 18 160 64 128 256), losses := [] }

theorem u988 : Upper (D 1) (R 1) [52,320,136,65,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b988
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 322 196 11 18 40 240 176 432), lower := (rows 53 322 196 11 18 40 64 128 256), losses := [] }

theorem u989 : Upper (D 1) (R 1) [52,320,192,3,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b989
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 196 11 18 48 232 168 424), lower := (rows 53 322 196 11 18 48 64 128 256), losses := [] }

theorem u990 : Upper (D 1) (R 1) [52,320,192,3,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b990
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 196 11 18 160 120 184 312), lower := (rows 53 322 196 11 18 160 64 128 256), losses := [] }

theorem u991 : Upper (D 1) (R 1) [52,320,192,3,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 53 322 196 138 17 34 120 184 312), lower := (rows 53 322 196 138 17 34 64 128 256), losses := [] }

theorem u992 : Upper (D 1) (R 1) [52,320,192,130,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b992
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 53 322 196 138 18 40 113 177 305), lower := (rows 53 322 196 138 18 40 64 128 256), losses := [] }

theorem u993 : Upper (D 1) (R 1) [52,320,192,130,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b993
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 196 138 18 48 105 169 297), lower := (rows 53 322 196 138 18 48 64 128 256), losses := [] }

theorem u994 : Upper (D 1) (R 1) [52,320,192,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b994
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 322 196 152 18 33 106 170 298), lower := (rows 53 322 196 152 18 33 64 128 256), losses := [] }

theorem u995 : Upper (D 1) (R 1) [52,320,192,144,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b995
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b996 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 196 152 18 34 105 169 297), lower := (rows 53 322 196 152 18 34 64 128 256), losses := [] }

theorem u996 : Upper (D 1) (R 1) [52,320,192,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b996
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 322 196 152 18 40 99 163 291), lower := (rows 53 322 196 152 18 40 64 128 256), losses := [] }

theorem u997 : Upper (D 1) (R 1) [52,320,192,144,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 14 280 144 34 224 224 480), lower := (rows 113 7 14 280 144 34 64 128 256), losses := [] }

theorem u998 : Upper (D 1) (R 1) [112,5,10,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b998
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 14 280 144 96 226 162 418), lower := (rows 113 7 14 280 144 96 64 128 256), losses := [] }

theorem u999 : Upper (D 1) (R 1) [112,5,10,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b999
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 7 14 280 144 160 98 226 354), lower := (rows 113 7 14 280 144 160 64 128 256), losses := [] }

theorem u1000 : Upper (D 1) (R 1) [112,5,10,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1000
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 14 392 18 160 112 240 368), lower := (rows 113 7 14 392 18 160 64 128 256), losses := [] }

theorem u1001 : Upper (D 1) (R 1) [112,5,10,384,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1001
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 392 48 160 82 210 338), lower := (rows 113 7 14 392 48 160 64 128 256), losses := [] }

theorem u1002 : Upper (D 1) (R 1) [112,5,10,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1002
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 14 392 80 160 114 178 306), lower := (rows 113 7 14 392 80 160 64 128 256), losses := [] }

theorem u1003 : Upper (D 1) (R 1) [112,5,10,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1003
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 134 280 144 34 104 232 360), lower := (rows 113 7 134 280 144 34 64 128 256), losses := [] }

theorem u1004 : Upper (D 1) (R 1) [112,5,130,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 7 134 280 144 40 98 226 354), lower := (rows 113 7 134 280 144 40 64 128 256), losses := [] }

theorem u1005 : Upper (D 1) (R 1) [112,5,130,272,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1005
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 134 280 144 96 106 170 298), lower := (rows 113 7 134 280 144 96 64 128 256), losses := [] }

theorem u1006 : Upper (D 1) (R 1) [112,5,130,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1006
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 140 266 18 160 112 240 368), lower := (rows 113 7 140 266 18 160 64 128 256), losses := [] }

theorem u1007 : Upper (D 1) (R 1) [112,5,136,258,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 266 48 160 82 210 338), lower := (rows 113 7 140 266 48 160 64 128 256), losses := [] }

theorem u1008 : Upper (D 1) (R 1) [112,5,136,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1008
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 140 266 80 160 114 178 306), lower := (rows 113 7 140 266 80 160 64 128 256), losses := [] }

theorem u1009 : Upper (D 1) (R 1) [112,5,136,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1009
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 98, camps := [], pairs := [(3,7)], upper := (rows 113 7 140 280 144 34 98 226 354), lower := (rows 113 7 140 280 144 34 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 16 34 98 0 290), good := (rows 377 367 12 280 16 354 64 0 256) }] }

theorem u1010 : Upper (D 1) (R 1) [112,5,136,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1010
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 140 280 144 96 98 162 290), lower := (rows 113 7 140 280 144 96 64 128 256), losses := [] }

theorem u1011 : Upper (D 1) (R 1) [112,5,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1011
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 268 138 18 160 112 240 368), lower := (rows 113 7 268 138 18 160 64 128 256), losses := [] }

theorem u1012 : Upper (D 1) (R 1) [112,5,264,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1012
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 138 48 160 82 210 338), lower := (rows 113 7 268 138 48 160 64 128 256), losses := [] }

theorem u1013 : Upper (D 1) (R 1) [112,5,264,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1013
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 268 138 80 160 114 178 306), lower := (rows 113 7 268 138 80 160 64 128 256), losses := [] }

theorem u1014 : Upper (D 1) (R 1) [112,5,264,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 7 388 152 18 34 104 232 360), lower := (rows 113 7 388 152 18 34 64 128 256), losses := [] }

theorem u1015 : Upper (D 1) (R 1) [112,5,384,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1015
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 7 388 152 18 40 98 226 354), lower := (rows 113 7 388 152 18 40 64 128 256), losses := [] }

theorem u1016 : Upper (D 1) (R 1) [112,5,384,144,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 388 152 18 96 106 170 298), lower := (rows 113 7 388 152 18 96 64 128 256), losses := [] }

theorem u1017 : Upper (D 1) (R 1) [112,5,384,144,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 280 144 34 224 224 480), lower := (rows 113 14 7 280 144 34 64 128 256), losses := [] }

theorem u1018 : Upper (D 1) (R 1) [112,12,3,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1018
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 7 280 144 96 226 162 418), lower := (rows 113 14 7 280 144 96 64 128 256), losses := [] }

theorem u1019 : Upper (D 1) (R 1) [112,12,3,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1019
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P01
