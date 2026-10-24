import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0006

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3000 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 76 392 176 36 113 177 305), lower := (rows 67 35 76 392 176 36 64 128 256), losses := [] }

theorem u3000 : Upper (D 8) (R 8) [66,33,72,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3000 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 76 392 176 48 101 165 293), lower := (rows 67 35 76 392 176 48 64 128 256), losses := [] }

theorem u3001 : Upper (D 8) (R 8) [66,33,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3001 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 296 176 33 84 212 340), lower := (rows 67 35 140 296 176 33 64 128 256), losses := [] }

theorem u3002 : Upper (D 8) (R 8) [66,33,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3003 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 35 140 296 176 36 81 209 337), lower := (rows 67 35 140 296 176 36 64 128 256), losses := [] }

theorem u3003 : Upper (D 8) (R 8) [66,33,136,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3003 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3004 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 67 35 140 296 176 48 69 197 325), lower := (rows 67 35 140 296 176 48 64 128 256), losses := [] }

theorem u3004 : Upper (D 8) (R 8) [66,33,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3004 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 140 296 176 96 85 149 277), lower := (rows 67 35 140 296 176 96 64 128 256), losses := [] }

theorem u3005 : Upper (D 8) (R 8) [66,33,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3006 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 296 208 33 116 180 308), lower := (rows 67 35 140 296 208 33 64 128 256), losses := [] }

theorem u3006 : Upper (D 8) (R 8) [66,33,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3007 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 140 296 208 36 113 177 305), lower := (rows 67 35 140 296 208 36 64 128 256), losses := [] }

theorem u3007 : Upper (D 8) (R 8) [66,33,136,288,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3007 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3008 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 140 296 208 48 101 165 293), lower := (rows 67 35 140 296 208 48 64 128 256), losses := [] }

theorem u3008 : Upper (D 8) (R 8) [66,33,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3008 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3009 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 328 176 33 116 180 308), lower := (rows 67 35 140 328 176 33 64 128 256), losses := [] }

theorem u3009 : Upper (D 8) (R 8) [66,33,136,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3010 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 140 328 176 36 113 177 305), lower := (rows 67 35 140 328 176 36 64 128 256), losses := [] }

theorem u3010 : Upper (D 8) (R 8) [66,33,136,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3010 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 140 328 176 48 101 165 293), lower := (rows 67 35 140 328 176 48 64 128 256), losses := [] }

theorem u3011 : Upper (D 8) (R 8) [66,33,136,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3011 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 164 200 276 33 120 184 312), lower := (rows 67 35 164 200 276 33 64 128 256), losses := [] }

theorem u3012 : Upper (D 8) (R 8) [66,33,160,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3013 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 164 200 276 40 113 177 305), lower := (rows 67 35 164 200 276 40 64 128 256), losses := [] }

theorem u3013 : Upper (D 8) (R 8) [66,33,160,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3013 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 35 164 200 276 48 105 169 297), lower := (rows 67 35 164 200 276 48 64 128 256), losses := [] }

theorem u3014 : Upper (D 8) (R 8) [66,33,160,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3014 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 164 200 280 33 116 180 308), lower := (rows 67 35 164 200 280 33 64 128 256), losses := [] }

theorem u3015 : Upper (D 8) (R 8) [66,33,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 164 200 280 36 113 177 305), lower := (rows 67 35 164 200 280 36 64 128 256), losses := [] }

theorem u3016 : Upper (D 8) (R 8) [66,33,160,192,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3016 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 164 200 280 48 101 165 293), lower := (rows 67 35 164 200 280 48 64 128 256), losses := [] }

theorem u3017 : Upper (D 8) (R 8) [66,33,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3017 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 164 200 304 33 92 156 284), lower := (rows 67 35 164 200 304 33 64 128 256), losses := [] }

theorem u3018 : Upper (D 8) (R 8) [66,33,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3019 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 35 164 200 304 36 89 153 281), lower := (rows 67 35 164 200 304 36 64 128 256), losses := [] }

theorem u3019 : Upper (D 8) (R 8) [66,33,160,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3019 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 35 164 200 304 40 85 149 277), lower := (rows 67 35 164 200 304 40 64 128 256), losses := [] }

theorem u3020 : Upper (D 8) (R 8) [66,33,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3020 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 35 164 200 304 48 77 141 269), lower := (rows 67 35 164 200 304 48 64 128 256), losses := [] }

theorem u3021 : Upper (D 8) (R 8) [66,33,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3021 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 56 400 33 224 224 480), lower := (rows 67 38 13 56 400 33 64 128 256), losses := [] }

theorem u3022 : Upper (D 8) (R 8) [66,36,9,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3023 : PairBound 9 := { available := 161, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 56 400 96 225 161 417), lower := (rows 67 38 13 56 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 56 400 96 96 128 256) }] }

theorem u3023 : Upper (D 8) (R 8) [66,36,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 56 400 160 97 225 353), lower := (rows 67 38 13 56 400 160 64 128 256), losses := [] }

theorem u3024 : Upper (D 8) (R 8) [66,36,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3025 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 152 304 33 224 224 480), lower := (rows 67 38 13 152 304 33 64 128 256), losses := [] }

theorem u3025 : Upper (D 8) (R 8) [66,36,9,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3026 : PairBound 9 := { available := 161, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 152 304 96 225 161 417), lower := (rows 67 38 13 152 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 152 304 96 96 128 256) }] }

theorem u3026 : Upper (D 8) (R 8) [66,36,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3027 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 152 304 160 97 225 353), lower := (rows 67 38 13 152 304 160 64 128 256), losses := [] }

theorem u3027 : Upper (D 8) (R 8) [66,36,9,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3028 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 112 33 464 400 400), lower := (rows 67 38 13 168 112 33 64 128 256), losses := [] }

theorem u3028 : Upper (D 8) (R 8) [66,36,9,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3029 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 38 13 168 112 48 449 385 385), lower := (rows 67 38 13 168 112 48 64 128 256), losses := [] }

theorem u3029 : Upper (D 8) (R 8) [66,36,9,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3029 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3030 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 168 112 160 337 401 273), lower := (rows 67 38 13 168 112 160 64 128 256), losses := [] }

theorem u3030 : Upper (D 8) (R 8) [66,36,9,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 38 13 168 112 288 209 145 401), lower := (rows 67 38 13 168 112 288 64 128 256), losses := [] }

theorem u3031 : Upper (D 8) (R 8) [66,36,9,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3031 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 208 33 368 432 304), lower := (rows 67 38 13 168 208 33 64 128 256), losses := [] }

theorem u3032 : Upper (D 8) (R 8) [66,36,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 38 13 168 208 48 353 417 289), lower := (rows 67 38 13 168 208 48 64 128 256), losses := [] }

theorem u3033 : Upper (D 8) (R 8) [66,36,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3033 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 13 168 208 288 113 177 305), lower := (rows 67 38 13 168 208 288 64 128 256), losses := [] }

theorem u3034 : Upper (D 8) (R 8) [66,36,9,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3034 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 304 33 208 208 464), lower := (rows 67 38 13 168 304 33 64 128 256), losses := [] }

theorem u3035 : Upper (D 8) (R 8) [66,36,9,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3036 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 38 13 168 304 48 193 193 449), lower := (rows 67 38 13 168 304 48 64 128 256), losses := [] }

theorem u3036 : Upper (D 8) (R 8) [66,36,9,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3036 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 145, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 168 304 96 209 145 401), lower := (rows 67 38 13 168 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 168 304 96 96 128 256) }] }

theorem u3037 : Upper (D 8) (R 8) [66,36,9,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3038 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 168 304 160 81 209 337), lower := (rows 67 38 13 168 304 160 64 128 256), losses := [] }

theorem u3038 : Upper (D 8) (R 8) [66,36,9,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3039 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 336 33 240 176 432), lower := (rows 67 38 13 168 336 33 64 128 256), losses := [] }

theorem u3039 : Upper (D 8) (R 8) [66,36,9,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 13 168 336 48 225 161 417), lower := (rows 67 38 13 168 336 48 64 128 256), losses := [] }

theorem u3040 : Upper (D 8) (R 8) [66,36,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3040 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 168 336 160 113 177 305), lower := (rows 67 38 13 168 336 160 64 128 256), losses := [] }

theorem u3041 : Upper (D 8) (R 8) [66,36,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3042 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 400 33 112 240 368), lower := (rows 67 38 13 168 400 33 64 128 256), losses := [] }

theorem u3042 : Upper (D 8) (R 8) [66,36,9,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3043 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 13 168 400 48 97 225 353), lower := (rows 67 38 13 168 400 48 64 128 256), losses := [] }

theorem u3043 : Upper (D 8) (R 8) [66,36,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3043 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3044 : PairBound 9 := { available := 49, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 168 400 96 113 177 305), lower := (rows 67 38 13 168 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 168 400 96 96 128 256) }] }

theorem u3044 : Upper (D 8) (R 8) [66,36,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3045 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 280 176 33 224 224 480), lower := (rows 67 38 13 280 176 33 64 128 256), losses := [] }

theorem u3045 : Upper (D 8) (R 8) [66,36,9,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3046 : PairBound 9 := { available := 161, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 280 176 96 225 161 417), lower := (rows 67 38 13 280 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 280 176 96 96 128 256) }] }

theorem u3046 : Upper (D 8) (R 8) [66,36,9,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3047 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 280 176 160 97 225 353), lower := (rows 67 38 13 280 176 160 64 128 256), losses := [] }

theorem u3047 : Upper (D 8) (R 8) [66,36,9,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3048 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 296 112 33 208 144 400), lower := (rows 67 38 13 296 112 33 64 128 256), losses := [] }

theorem u3048 : Upper (D 8) (R 8) [66,36,9,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3049 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 38 13 296 112 48 193 129 385), lower := (rows 67 38 13 296 112 48 64 128 256), losses := [] }

theorem u3049 : Upper (D 8) (R 8) [66,36,9,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3049 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3050 : Route 9 := (fun mask => (mask,id))

def c3050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3050 : Upper (D 8) (R 8) [66,36,9,288,96,128] 13 := by
  apply FastRouting.sound _ _ [66,36,9,288,96,128] 13 (by decide) (choices 1) [1,16,128] r3050 c3050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u393
  · exact u394
  · exact u395

def b3051 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 296 176 33 208 208 464), lower := (rows 67 38 13 296 176 33 64 128 256), losses := [] }

theorem u3051 : Upper (D 8) (R 8) [66,36,9,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 38 13 296 176 48 193 193 449), lower := (rows 67 38 13 296 176 48 64 128 256), losses := [] }

theorem u3052 : Upper (D 8) (R 8) [66,36,9,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3052 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 145, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 296 176 96 209 145 401), lower := (rows 67 38 13 296 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 296 176 96 96 128 256) }] }

theorem u3053 : Upper (D 8) (R 8) [66,36,9,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3054 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 296 176 160 81 209 337), lower := (rows 67 38 13 296 176 160 64 128 256), losses := [] }

theorem u3054 : Upper (D 8) (R 8) [66,36,9,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3055 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 296 208 33 240 176 432), lower := (rows 67 38 13 296 208 33 64 128 256), losses := [] }

theorem u3055 : Upper (D 8) (R 8) [66,36,9,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3056 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 13 296 208 48 225 161 417), lower := (rows 67 38 13 296 208 48 64 128 256), losses := [] }

theorem u3056 : Upper (D 8) (R 8) [66,36,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3056 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3057 : Route 9 := (fun mask => (mask,id))

def c3057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3057 : Upper (D 8) (R 8) [66,36,9,288,192,128] 13 := by
  apply FastRouting.sound _ _ [66,36,9,288,192,128] 13 (by decide) (choices 1) [1,16,32] r3057 c3057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u396
  · exact u397
  · exact u398

def b3058 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 392 112 33 240 176 432), lower := (rows 67 38 13 392 112 33 64 128 256), losses := [] }

theorem u3058 : Upper (D 8) (R 8) [66,36,9,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3059 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 13 392 112 48 225 161 417), lower := (rows 67 38 13 392 112 48 64 128 256), losses := [] }

theorem u3059 : Upper (D 8) (R 8) [66,36,9,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3059 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P08
