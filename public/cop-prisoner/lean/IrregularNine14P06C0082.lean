import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4920 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 265 82 36 65 148 276), lower := (rows 11 162 100 265 82 36 65 128 256), losses := [] }

theorem u4920 : Upper (D 6) (R 6) [10,160,96,257,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4921 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 265, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 265 82 36 68 145 273), lower := (rows 11 162 100 265 82 36 68 128 256), losses := [] }

theorem u4921 : Upper (D 6) (R 6) [10,160,96,257,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4922 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 265 82 36 80 133 261), lower := (rows 11 162 100 265 82 36 80 128 256), losses := [] }

theorem u4922 : Upper (D 6) (R 6) [10,160,96,257,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4922 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 68, targets := 1 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 162 100 268 21 33 66 208 336), lower := (rows 11 162 100 268 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 67 144 272), good := (rows 78 230 100 268 476 100 70 128 256) }] }

theorem u4923 : Upper (D 6) (R 6) [10,160,96,260,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4924 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 162 100 268 21 33 80 194 322), lower := (rows 11 162 100 268 21 33 80 128 256), losses := [] }

theorem u4924 : Upper (D 6) (R 6) [10,160,96,260,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4924 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4925 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 268 22 33 65 208 336), lower := (rows 11 162 100 268 22 33 65 128 256), losses := [] }

theorem u4925 : Upper (D 6) (R 6) [10,160,96,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4926 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 100 268 22 33 80 193 321), lower := (rows 11 162 100 268 22 33 80 128 256), losses := [] }

theorem u4926 : Upper (D 6) (R 6) [10,160,96,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4926 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4927 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 162 100 268 81 33 66 148 276), lower := (rows 11 162 100 268 81 33 66 128 256), losses := [] }

theorem u4927 : Upper (D 6) (R 6) [10,160,96,260,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4928 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 11 162 100 268 81 33 68 146 274), lower := (rows 11 162 100 268 81 33 68 128 256), losses := [] }

theorem u4928 : Upper (D 6) (R 6) [10,160,96,260,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 268 81 33 80 134 262), lower := (rows 11 162 100 268 81 33 80 128 256), losses := [] }

theorem u4929 : Upper (D 6) (R 6) [10,160,96,260,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4929 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4930 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 268 82 33 65 148 276), lower := (rows 11 162 100 268 82 33 65 128 256), losses := [] }

theorem u4930 : Upper (D 6) (R 6) [10,160,96,260,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4931 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 100 268 82 33 68 145 273), lower := (rows 11 162 100 268 82 33 68 128 256), losses := [] }

theorem u4931 : Upper (D 6) (R 6) [10,160,96,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4932 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 268 82 33 80 133 261), lower := (rows 11 162 100 268 82 33 80 128 256), losses := [] }

theorem u4932 : Upper (D 6) (R 6) [10,160,96,260,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4932 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4933 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 100 280 81 36 65 134 262), lower := (rows 11 162 100 280 81 36 65 128 256), losses := [] }

theorem u4933 : Upper (D 6) (R 6) [10,160,96,272,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4934 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 100 280 81 36 66 133 261), lower := (rows 11 162 100 280 81 36 66 128 256), losses := [] }

theorem u4934 : Upper (D 6) (R 6) [10,160,96,272,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4935 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 100 280 81 36 68 131 259), lower := (rows 11 162 100 280 81 36 68 128 256), losses := [] }

theorem u4935 : Upper (D 6) (R 6) [10,160,96,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4936 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 280 82 33 65 132 260), lower := (rows 11 162 100 280 82 33 65 128 256), losses := [] }

theorem u4936 : Upper (D 6) (R 6) [10,160,96,272,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4937 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 100 280 82 33 68 133 261), lower := (rows 11 162 100 280 82 33 68 128 256), losses := [] }

theorem u4937 : Upper (D 6) (R 6) [10,160,96,272,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4938 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 280 82 36 65 133 261), lower := (rows 11 162 100 280 82 36 65 128 256), losses := [] }

theorem u4938 : Upper (D 6) (R 6) [10,160,96,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4939 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 265, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 280 82 36 68 129 257), lower := (rows 11 162 100 280 82 36 68 128 256), losses := [] }

theorem u4939 : Upper (D 6) (R 6) [10,160,96,272,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4940 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 68, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 11 162 100 328 21 33 66 148 276), lower := (rows 11 162 100 328 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 67 144 272), good := (rows 78 230 100 328 476 100 70 128 256) }] }

theorem u4940 : Upper (D 6) (R 6) [10,160,96,320,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4941 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 11 162 100 328 21 33 68 146 274), lower := (rows 11 162 100 328 21 33 68 128 256), losses := [] }

theorem u4941 : Upper (D 6) (R 6) [10,160,96,320,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4942 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 162 100 328 21 33 80 134 262), lower := (rows 11 162 100 328 21 33 80 128 256), losses := [] }

theorem u4942 : Upper (D 6) (R 6) [10,160,96,320,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4942 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4943 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 162 100 328 21 48 65 134 262), lower := (rows 11 162 100 328 21 48 65 128 256), losses := [] }

theorem u4943 : Upper (D 6) (R 6) [10,160,96,320,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4943 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4944 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 68, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,0)], upper := (rows 11 162 100 328 21 48 66 133 261), lower := (rows 11 162 100 328 21 48 66 128 256), losses := [] }

theorem u4944 : Upper (D 6) (R 6) [10,160,96,320,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4944 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4945 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 395, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 100 328 21 48 68 131 259), lower := (rows 11 162 100 328 21 48 68 128 256), losses := [] }

theorem u4945 : Upper (D 6) (R 6) [10,160,96,320,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4945 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4946 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 328 22 33 65 148 276), lower := (rows 11 162 100 328 22 33 65 128 256), losses := [] }

theorem u4946 : Upper (D 6) (R 6) [10,160,96,320,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4947 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 11 162 100 328 22 33 68 145 273), lower := (rows 11 162 100 328 22 33 68 128 256), losses := [] }

theorem u4947 : Upper (D 6) (R 6) [10,160,96,320,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 100 328 22 33 80 133 261), lower := (rows 11 162 100 328 22 33 80 128 256), losses := [] }

theorem u4948 : Upper (D 6) (R 6) [10,160,96,320,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4948 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4949 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 261 25 84 96 66 164 292), lower := (rows 11 162 261 25 84 96 66 128 256), losses := [] }

theorem u4949 : Upper (D 6) (R 6) [10,160,257,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4950 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 261 25 84 96 68 162 290), lower := (rows 11 162 261 25 84 96 68 128 256), losses := [] }

theorem u4950 : Upper (D 6) (R 6) [10,160,257,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4951 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 260, targets := 96 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(2,6)], upper := (rows 11 162 261 25 84 96 96 134 262), lower := (rows 11 162 261 25 84 96 96 128 256), losses := [] }

theorem u4951 : Upper (D 6) (R 6) [10,160,257,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4952 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 261 28 81 96 66 164 292), lower := (rows 11 162 261 28 81 96 66 128 256), losses := [] }

theorem u4952 : Upper (D 6) (R 6) [10,160,257,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4953 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 28 81 96 68 162 290), lower := (rows 11 162 261 28 81 96 68 128 256), losses := [] }

theorem u4953 : Upper (D 6) (R 6) [10,160,257,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4954 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 260, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 162 261 28 81 96 96 134 262), lower := (rows 11 162 261 28 81 96 96 128 256), losses := [] }

theorem u4954 : Upper (D 6) (R 6) [10,160,257,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4955 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 162 261 28 82 33 68 224 352), lower := (rows 11 162 261 28 82 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 32 76 128 256), good := (rows 90 162 348 92 82 48 76 128 256) }] }

theorem u4955 : Upper (D 6) (R 6) [10,160,257,20,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4956 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 261 28 82 33 96 196 324), lower := (rows 11 162 261 28 82 33 96 128 256), losses := [] }

theorem u4956 : Upper (D 6) (R 6) [10,160,257,20,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4957 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 261 28 82 36 65 224 352), lower := (rows 11 162 261 28 82 36 65 128 256), losses := [] }

theorem u4957 : Upper (D 6) (R 6) [10,160,257,20,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4958 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 261 28 82 36 96 193 321), lower := (rows 11 162 261 28 82 36 96 128 256), losses := [] }

theorem u4958 : Upper (D 6) (R 6) [10,160,257,20,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4959 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 261 28 82 96 65 164 292), lower := (rows 11 162 261 28 82 96 65 128 256), losses := [] }

theorem u4959 : Upper (D 6) (R 6) [10,160,257,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4960 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 162 261 28 82 96 68 161 289), lower := (rows 11 162 261 28 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 125 76 128 256), good := (rows 122 162 380 124 114 96 108 128 256) }] }

theorem u4960 : Upper (D 6) (R 6) [10,160,257,20,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4961 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 269, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 162 261 28 82 96 96 133 261), lower := (rows 11 162 261 28 82 96 96 128 256), losses := [] }

theorem u4961 : Upper (D 6) (R 6) [10,160,257,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4962 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 162 261 28 112 33 66 196 324), lower := (rows 11 162 261 28 112 33 66 128 256), losses := [] }

theorem u4962 : Upper (D 6) (R 6) [10,160,257,20,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4963 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 162 261 28 112 33 68 194 322), lower := (rows 11 162 261 28 112 33 68 128 256), losses := [] }

theorem u4963 : Upper (D 6) (R 6) [10,160,257,20,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4964 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 162 261 28 112 36 65 194 322), lower := (rows 11 162 261 28 112 36 65 128 256), losses := [] }

theorem u4964 : Upper (D 6) (R 6) [10,160,257,20,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4965 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 162 261 28 112 36 66 193 321), lower := (rows 11 162 261 28 112 36 66 128 256), losses := [] }

theorem u4965 : Upper (D 6) (R 6) [10,160,257,20,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4966 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 44 22 96 65 208 336), lower := (rows 11 162 261 44 22 96 65 128 256), losses := [] }

theorem u4966 : Upper (D 6) (R 6) [10,160,257,36,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4967 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 261 44 22 96 80 193 321), lower := (rows 11 162 261 44 22 96 80 128 256), losses := [] }

theorem u4967 : Upper (D 6) (R 6) [10,160,257,36,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4967 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4968 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 260, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 261 44 81 96 66 148 276), lower := (rows 11 162 261 44 81 96 66 128 256), losses := [] }

theorem u4968 : Upper (D 6) (R 6) [10,160,257,36,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4969 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 44 81 96 68 146 274), lower := (rows 11 162 261 44 81 96 68 128 256), losses := [] }

theorem u4969 : Upper (D 6) (R 6) [10,160,257,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4970 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 261 44 81 96 80 134 262), lower := (rows 11 162 261 44 81 96 80 128 256), losses := [] }

theorem u4970 : Upper (D 6) (R 6) [10,160,257,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4970 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4971 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,5),(4,2),(4,5)], upper := (rows 11 162 261 44 82 96 65 148 276), lower := (rows 11 162 261 44 82 96 65 128 256), losses := [] }

theorem u4971 : Upper (D 6) (R 6) [10,160,257,36,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4972 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 261 44 82 96 68 145 273), lower := (rows 11 162 261 44 82 96 68 128 256), losses := [] }

theorem u4972 : Upper (D 6) (R 6) [10,160,257,36,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4973 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 261 44 82 96 80 133 261), lower := (rows 11 162 261 44 82 96 80 128 256), losses := [] }

theorem u4973 : Upper (D 6) (R 6) [10,160,257,36,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4973 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4974 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 261 73 22 36 80 224 352), lower := (rows 11 162 261 73 22 36 80 128 256), losses := [] }

theorem u4974 : Upper (D 6) (R 6) [10,160,257,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4974 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4975 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 242, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 162 261 73 22 36 96 208 336), lower := (rows 11 162 261 73 22 36 96 128 256), losses := [] }

theorem u4975 : Upper (D 6) (R 6) [10,160,257,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4976 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 11 162 261 73 22 96 68 176 304), lower := (rows 11 162 261 73 22 96 68 128 256), losses := [] }

theorem u4976 : Upper (D 6) (R 6) [10,160,257,65,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4977 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 261 73 22 96 80 164 292), lower := (rows 11 162 261 73 22 96 80 128 256), losses := [] }

theorem u4977 : Upper (D 6) (R 6) [10,160,257,65,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4977 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4978 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 261 73 22 96 96 148 276), lower := (rows 11 162 261 73 22 96 96 128 256), losses := [] }

theorem u4978 : Upper (D 6) (R 6) [10,160,257,65,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4979 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 261 73 112 36 66 148 276), lower := (rows 11 162 261 73 112 36 66 128 256), losses := [] }

theorem u4979 : Upper (D 6) (R 6) [10,160,257,65,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4979
end Delivery.IrregularNine14.P06
