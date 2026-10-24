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

def b5940 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 280 112 33 68 134 262), lower := (rows 35 67 140 280 112 33 68 128 256), losses := [] }

theorem u5940 : Upper (D 6) (R 6) [34,65,136,272,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5941 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 280 112 34 68 133 261), lower := (rows 35 67 140 280 112 34 68 128 256), losses := [] }

theorem u5941 : Upper (D 6) (R 6) [34,65,136,272,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5942 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 67 140 280 112 36 68 131 259), lower := (rows 35 67 140 280 112 36 68 128 256), losses := [] }

theorem u5942 : Upper (D 6) (R 6) [34,65,136,272,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5943 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 296 21 36 66 208 336), lower := (rows 35 67 140 296 21 36 66 128 256), losses := [] }

theorem u5943 : Upper (D 6) (R 6) [34,65,136,288,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5944 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 296 21 36 80 194 322), lower := (rows 35 67 140 296 21 36 80 128 256), losses := [] }

theorem u5944 : Upper (D 6) (R 6) [34,65,136,288,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5944 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5945 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 296 22 36 65 208 336), lower := (rows 35 67 140 296 22 36 65 128 256), losses := [] }

theorem u5945 : Upper (D 6) (R 6) [34,65,136,288,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5946 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 296 22 36 80 193 321), lower := (rows 35 67 140 296 22 36 80 128 256), losses := [] }

theorem u5946 : Upper (D 6) (R 6) [34,65,136,288,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5946 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5947 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 296 84 36 65 146 274), lower := (rows 35 67 140 296 84 36 65 128 256), losses := [] }

theorem u5947 : Upper (D 6) (R 6) [34,65,136,288,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5948 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 296 84 36 66 145 273), lower := (rows 35 67 140 296 84 36 66 128 256), losses := [] }

theorem u5948 : Upper (D 6) (R 6) [34,65,136,288,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5949 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 140 296 84 36 80 131 259), lower := (rows 35 67 140 296 84 36 80 128 256), losses := [] }

theorem u5949 : Upper (D 6) (R 6) [34,65,136,288,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5949 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5950 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 14 84 288 65 152 280), lower := (rows 35 67 164 14 84 288 65 128 256), losses := [] }

theorem u5950 : Upper (D 6) (R 6) [34,65,160,6,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5950 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5951 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 67 164 14 84 288 72 145 273), lower := (rows 35 67 164 14 84 288 72 128 256), losses := [] }

theorem u5951 : Upper (D 6) (R 6) [34,65,160,6,68,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5951 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5952 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 164 14 84 288 80 137 265), lower := (rows 35 67 164 14 84 288 80 128 256), losses := [] }

theorem u5952 : Upper (D 6) (R 6) [34,65,160,6,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5952 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5953 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 14 88 288 65 148 276), lower := (rows 35 67 164 14 88 288 65 128 256), losses := [] }

theorem u5953 : Upper (D 6) (R 6) [34,65,160,6,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5953 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5954 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 164 14 88 288 68 145 273), lower := (rows 35 67 164 14 88 288 68 128 256), losses := [] }

theorem u5954 : Upper (D 6) (R 6) [34,65,160,6,72,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5954 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5955 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 67 164 14 88 288 80 133 261), lower := (rows 35 67 164 14 88 288 80 128 256), losses := [] }

theorem u5955 : Upper (D 6) (R 6) [34,65,160,6,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5955 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5956 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 14 276 48 65 200 328), lower := (rows 35 67 164 14 276 48 65 128 256), losses := [] }

theorem u5956 : Upper (D 6) (R 6) [34,65,160,6,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5956 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5957 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 164 14 276 48 72 193 321), lower := (rows 35 67 164 14 276 48 72 128 256), losses := [] }

theorem u5957 : Upper (D 6) (R 6) [34,65,160,6,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5957 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5958 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 25 84 288 66 140 268), lower := (rows 35 67 164 25 84 288 66 128 256), losses := [] }

theorem u5958 : Upper (D 6) (R 6) [34,65,160,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5958 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5959 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 164 25 84 288 68 138 266), lower := (rows 35 67 164 25 84 288 68 128 256), losses := [] }

theorem u5959 : Upper (D 6) (R 6) [34,65,160,17,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5959 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5960 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 164 25 84 288 72 134 262), lower := (rows 35 67 164 25 84 288 72 128 256), losses := [] }

theorem u5960 : Upper (D 6) (R 6) [34,65,160,17,68,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5960 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5961 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 28 336 40 65 134 262), lower := (rows 35 67 164 28 336 40 65 128 256), losses := [] }

theorem u5961 : Upper (D 6) (R 6) [34,65,160,20,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5961 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5962 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 28 336 40 66 133 261), lower := (rows 35 67 164 28 336 40 66 128 256), losses := [] }

theorem u5962 : Upper (D 6) (R 6) [34,65,160,20,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5962 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5963 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 67 164 28 336 40 68 131 259), lower := (rows 35 67 164 28 336 40 68 128 256), losses := [] }

theorem u5963 : Upper (D 6) (R 6) [34,65,160,20,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5963 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5964 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 76 276 48 65 138 266), lower := (rows 35 67 164 76 276 48 65 128 256), losses := [] }

theorem u5964 : Upper (D 6) (R 6) [34,65,160,68,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5964 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5965 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 76 276 48 66 137 265), lower := (rows 35 67 164 76 276 48 66 128 256), losses := [] }

theorem u5965 : Upper (D 6) (R 6) [34,65,160,68,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5965 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5966 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 164 76 276 48 72 131 259), lower := (rows 35 67 164 76 276 48 72 128 256), losses := [] }

theorem u5966 : Upper (D 6) (R 6) [34,65,160,68,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5966 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5967 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 76 280 48 65 134 262), lower := (rows 35 67 164 76 280 48 65 128 256), losses := [] }

theorem u5967 : Upper (D 6) (R 6) [34,65,160,68,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5967 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5968 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 76 280 48 66 133 261), lower := (rows 35 67 164 76 280 48 66 128 256), losses := [] }

theorem u5968 : Upper (D 6) (R 6) [34,65,160,68,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5968 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5969 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 164 76 280 48 68 131 259), lower := (rows 35 67 164 76 280 48 68 128 256), losses := [] }

theorem u5969 : Upper (D 6) (R 6) [34,65,160,68,264,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5969 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5970 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 82, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 67 388 13 88 36 66 176 304), lower := (rows 35 67 388 13 88 36 66 128 256), losses := [] }

theorem u5970 : Upper (D 6) (R 6) [34,65,384,5,72,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5971 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 82, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 388 13 88 36 80 162 290), lower := (rows 35 67 388 13 88 36 80 128 256), losses := [] }

theorem u5971 : Upper (D 6) (R 6) [34,65,384,5,72,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5971 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5972 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 388 13 88 36 96 146 274), lower := (rows 35 67 388 13 88 36 96 128 256), losses := [] }

theorem u5972 : Upper (D 6) (R 6) [34,65,384,5,72,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5973 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 13 112 36 66 152 280), lower := (rows 35 67 388 13 112 36 66 128 256), losses := [] }

theorem u5973 : Upper (D 6) (R 6) [34,65,384,5,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5974 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 388 13 112 36 72 146 274), lower := (rows 35 67 388 13 112 36 72 128 256), losses := [] }

theorem u5974 : Upper (D 6) (R 6) [34,65,384,5,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5974 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5975 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 388 13 112 36 80 138 266), lower := (rows 35 67 388 13 112 36 80 128 256), losses := [] }

theorem u5975 : Upper (D 6) (R 6) [34,65,384,5,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5975 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5976 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 25 84 36 66 168 296), lower := (rows 35 67 388 25 84 36 66 128 256), losses := [] }

theorem u5976 : Upper (D 6) (R 6) [34,65,384,17,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5977 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 388 25 84 36 72 162 290), lower := (rows 35 67 388 25 84 36 72 128 256), losses := [] }

theorem u5977 : Upper (D 6) (R 6) [34,65,384,17,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5977 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5978 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 388 25 84 36 96 138 266), lower := (rows 35 67 388 25 84 36 96 128 256), losses := [] }

theorem u5978 : Upper (D 6) (R 6) [34,65,384,17,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5979 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 388 28 112 33 68 138 266), lower := (rows 35 67 388 28 112 33 68 128 256), losses := [] }

theorem u5979 : Upper (D 6) (R 6) [34,65,384,20,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5980 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 28 112 34 68 137 265), lower := (rows 35 67 388 28 112 34 68 128 256), losses := [] }

theorem u5980 : Upper (D 6) (R 6) [34,65,384,20,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5981 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 388 28 112 36 72 131 259), lower := (rows 35 67 388 28 112 36 72 128 256), losses := [] }

theorem u5981 : Upper (D 6) (R 6) [34,65,384,20,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5981 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5982 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 144, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 35 70 44 25 146 288 65 196 324), lower := (rows 35 70 44 25 146 288 65 128 256), losses := [] }

theorem u5982 : Upper (D 6) (R 6) [34,68,40,17,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5982 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5983 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 44 25 146 288 68 193 321), lower := (rows 35 70 44 25 146 288 68 128 256), losses := [] }

theorem u5983 : Upper (D 6) (R 6) [34,68,40,17,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5983 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5984 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 144, targets := 1 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(4,0)], upper := (rows 35 70 44 25 148 288 65 194 322), lower := (rows 35 70 44 25 148 288 65 128 256), losses := [] }

theorem u5984 : Upper (D 6) (R 6) [34,68,40,17,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5984 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5985 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 44 25 148 288 66 193 321), lower := (rows 35 70 44 25 148 288 66 128 256), losses := [] }

theorem u5985 : Upper (D 6) (R 6) [34,68,40,17,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5985 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5986 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(2,1)], upper := (rows 35 70 44 26 145 288 65 196 324), lower := (rows 35 70 44 26 145 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 299 64 130 258), good := (rows 418 486 44 446 176 288 96 128 288) },{ target := 1, region := (rows 1 0 12 8 17 303 81 138 266), good := (rows 497 484 428 508 241 288 113 128 288) }] }

theorem u5986 : Upper (D 6) (R 6) [34,68,40,18,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5986 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5987 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 44 26 145 288 68 193 321), lower := (rows 35 70 44 26 145 288 68 128 256), losses := [] }

theorem u5987 : Upper (D 6) (R 6) [34,68,40,18,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5987 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5988 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(2,1)], upper := (rows 35 70 44 26 148 288 65 193 321), lower := (rows 35 70 44 26 148 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 18 355 65 193 321), good := (rows 497 500 44 60 148 288 481 128 288) }] }

theorem u5988 : Upper (D 6) (R 6) [34,68,40,18,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5988 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5989 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 44 137 81 288 66 148 276), lower := (rows 35 70 44 137 81 288 66 128 256), losses := [] }

theorem u5989 : Upper (D 6) (R 6) [34,68,40,129,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5989 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5990 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 44 137 81 288 68 146 274), lower := (rows 35 70 44 137 81 288 68 128 256), losses := [] }

theorem u5990 : Upper (D 6) (R 6) [34,68,40,129,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5990 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5991 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 35 70 44 137 81 288 80 134 262), lower := (rows 35 70 44 137 81 288 80 128 256), losses := [] }

theorem u5991 : Upper (D 6) (R 6) [34,68,40,129,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5991 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5992 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 44 138 81 288 65 148 276), lower := (rows 35 70 44 138 81 288 65 128 256), losses := [] }

theorem u5992 : Upper (D 6) (R 6) [34,68,40,130,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5992 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5993 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 44 138 81 288 68 145 273), lower := (rows 35 70 44 138 81 288 68 128 256), losses := [] }

theorem u5993 : Upper (D 6) (R 6) [34,68,40,130,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5993 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5994 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 35 70 44 138 81 288 80 133 261), lower := (rows 35 70 44 138 81 288 80 128 256), losses := [] }

theorem u5994 : Upper (D 6) (R 6) [34,68,40,130,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5994 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5995 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 136, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 70 44 138 273 48 65 196 324), lower := (rows 35 70 44 138 273 48 65 128 256), losses := [] }

theorem u5995 : Upper (D 6) (R 6) [34,68,40,130,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5995 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5996 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 44 138 273 48 68 193 321), lower := (rows 35 70 44 138 273 48 68 128 256), losses := [] }

theorem u5996 : Upper (D 6) (R 6) [34,68,40,130,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5996 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5997 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 44 152 81 288 65 134 262), lower := (rows 35 70 44 152 81 288 65 128 256), losses := [] }

theorem u5997 : Upper (D 6) (R 6) [34,68,40,144,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5997 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5998 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 44 152 81 288 66 133 261), lower := (rows 35 70 44 152 81 288 66 128 256), losses := [] }

theorem u5998 : Upper (D 6) (R 6) [34,68,40,144,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5998 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5999 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 44 152 81 288 68 131 259), lower := (rows 35 70 44 152 81 288 68 128 256), losses := [] }

theorem u5999 : Upper (D 6) (R 6) [34,68,40,144,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5999 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5999
end Delivery.IrregularNine14.P06
