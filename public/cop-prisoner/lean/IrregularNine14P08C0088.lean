import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 140 296 145 34 113 177 305), lower := (rows 97 70 140 296 145 34 64 128 256), losses := [] }

theorem u5280 : Upper (D 8) (R 8) [96,68,136,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5280 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5281 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 140 296 145 48 99 163 291), lower := (rows 97 70 140 296 145 48 64 128 256), losses := [] }

theorem u5281 : Upper (D 8) (R 8) [96,68,136,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5281 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5282 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 296 176 33 83 147 275), lower := (rows 97 70 140 296 176 33 64 128 256), losses := [] }

theorem u5282 : Upper (D 8) (R 8) [96,68,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5283 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 70 140 296 176 34 81 145 273), lower := (rows 97 70 140 296 176 34 64 128 256), losses := [] }

theorem u5283 : Upper (D 8) (R 8) [96,68,136,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5283 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5284 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 70 140 296 176 48 67 131 259), lower := (rows 97 70 140 296 176 48 64 128 256), losses := [] }

theorem u5284 : Upper (D 8) (R 8) [96,68,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5284 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5285 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 70 164 137 273 34 120 184 312), lower := (rows 97 70 164 137 273 34 64 128 256), losses := [] }

theorem u5285 : Upper (D 8) (R 8) [96,68,160,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5285 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5286 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 70 164 137 273 40 114 178 306), lower := (rows 97 70 164 137 273 40 64 128 256), losses := [] }

theorem u5286 : Upper (D 8) (R 8) [96,68,160,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5286 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5287 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 70 164 137 273 48 106 170 298), lower := (rows 97 70 164 137 273 48 64 128 256), losses := [] }

theorem u5287 : Upper (D 8) (R 8) [96,68,160,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5287 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5288 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 137 274 33 120 184 312), lower := (rows 97 70 164 137 274 33 64 128 256), losses := [] }

theorem u5288 : Upper (D 8) (R 8) [96,68,160,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5289 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 164 137 274 40 113 177 305), lower := (rows 97 70 164 137 274 40 64 128 256), losses := [] }

theorem u5289 : Upper (D 8) (R 8) [96,68,160,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5289 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 70 164 137 274 48 105 169 297), lower := (rows 97 70 164 137 274 48 64 128 256), losses := [] }

theorem u5290 : Upper (D 8) (R 8) [96,68,160,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5290 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5291 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 137 280 33 114 178 306), lower := (rows 97 70 164 137 280 33 64 128 256), losses := [] }

theorem u5291 : Upper (D 8) (R 8) [96,68,160,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5292 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 164 137 280 34 113 177 305), lower := (rows 97 70 164 137 280 34 64 128 256), losses := [] }

theorem u5292 : Upper (D 8) (R 8) [96,68,160,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5292 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5293 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 164 137 280 48 99 163 291), lower := (rows 97 70 164 137 280 48 64 128 256), losses := [] }

theorem u5293 : Upper (D 8) (R 8) [96,68,160,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5293 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5294 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 137 304 33 90 154 282), lower := (rows 97 70 164 137 304 33 64 128 256), losses := [] }

theorem u5294 : Upper (D 8) (R 8) [96,68,160,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5295 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 70 164 137 304 34 89 153 281), lower := (rows 97 70 164 137 304 34 64 128 256), losses := [] }

theorem u5295 : Upper (D 8) (R 8) [96,68,160,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5295 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5296 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 70 164 137 304 40 83 147 275), lower := (rows 97 70 164 137 304 40 64 128 256), losses := [] }

theorem u5296 : Upper (D 8) (R 8) [96,68,160,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5296 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5297 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 70 164 137 304 48 75 139 267), lower := (rows 97 70 164 137 304 48 64 128 256), losses := [] }

theorem u5297 : Upper (D 8) (R 8) [96,68,160,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5297 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5298 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 152 273 33 106 170 298), lower := (rows 97 70 164 152 273 33 64 128 256), losses := [] }

theorem u5298 : Upper (D 8) (R 8) [96,68,160,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5299 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 70 164 152 273 34 105 169 297), lower := (rows 97 70 164 152 273 34 64 128 256), losses := [] }

theorem u5299 : Upper (D 8) (R 8) [96,68,160,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5299 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5300 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 164 152 273 40 99 163 291), lower := (rows 97 70 164 152 273 40 64 128 256), losses := [] }

theorem u5300 : Upper (D 8) (R 8) [96,68,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5300 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5301 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 164 152 304 33 75 139 267), lower := (rows 97 70 164 152 304 33 64 128 256), losses := [] }

theorem u5301 : Upper (D 8) (R 8) [96,68,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5302 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 70 164 152 304 34 73 137 265), lower := (rows 97 70 164 152 304 34 64 128 256), losses := [] }

theorem u5302 : Upper (D 8) (R 8) [96,68,160,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5302 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5303 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 70 164 152 304 40 67 131 259), lower := (rows 97 70 164 152 304 40 64 128 256), losses := [] }

theorem u5303 : Upper (D 8) (R 8) [96,68,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5303 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5304 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 70 261 137 146 40 112 176 304), lower := (rows 97 70 261 137 146 40 64 128 256), losses := [] }

theorem u5304 : Upper (D 8) (R 8) [96,68,257,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5304 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5305 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 70 261 137 146 48 104 168 296), lower := (rows 97 70 261 137 146 48 64 128 256), losses := [] }

theorem u5305 : Upper (D 8) (R 8) [96,68,257,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5305 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 70 261 137 176 34 120 184 312), lower := (rows 97 70 261 137 176 34 64 128 256), losses := [] }

theorem u5306 : Upper (D 8) (R 8) [96,68,257,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5306 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5307 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 70 261 137 176 40 114 178 306), lower := (rows 97 70 261 137 176 40 64 128 256), losses := [] }

theorem u5307 : Upper (D 8) (R 8) [96,68,257,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5307 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5308 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 70 261 137 176 48 106 170 298), lower := (rows 97 70 261 137 176 48 64 128 256), losses := [] }

theorem u5308 : Upper (D 8) (R 8) [96,68,257,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5308 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5309 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 261 138 176 33 120 184 312), lower := (rows 97 70 261 138 176 33 64 128 256), losses := [] }

theorem u5309 : Upper (D 8) (R 8) [96,68,257,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5310 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 261 138 176 40 113 177 305), lower := (rows 97 70 261 138 176 40 64 128 256), losses := [] }

theorem u5310 : Upper (D 8) (R 8) [96,68,257,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5310 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5311 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 70 261 138 176 48 105 169 297), lower := (rows 97 70 261 138 176 48 64 128 256), losses := [] }

theorem u5311 : Upper (D 8) (R 8) [96,68,257,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5311 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5312 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 137 176 33 114 178 306), lower := (rows 97 70 268 137 176 33 64 128 256), losses := [] }

theorem u5312 : Upper (D 8) (R 8) [96,68,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 268 137 176 34 113 177 305), lower := (rows 97 70 268 137 176 34 64 128 256), losses := [] }

theorem u5313 : Upper (D 8) (R 8) [96,68,264,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5313 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5314 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 268 137 176 48 99 163 291), lower := (rows 97 70 268 137 176 48 64 128 256), losses := [] }

theorem u5314 : Upper (D 8) (R 8) [96,68,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5314 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5315 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 168 145 33 114 178 306), lower := (rows 97 70 268 168 145 33 64 128 256), losses := [] }

theorem u5315 : Upper (D 8) (R 8) [96,68,264,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 268 168 145 34 113 177 305), lower := (rows 97 70 268 168 145 34 64 128 256), losses := [] }

theorem u5316 : Upper (D 8) (R 8) [96,68,264,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5316 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5317 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 268 168 145 48 99 163 291), lower := (rows 97 70 268 168 145 48 64 128 256), losses := [] }

theorem u5317 : Upper (D 8) (R 8) [96,68,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5317 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5318 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 292 137 146 33 120 184 312), lower := (rows 97 70 292 137 146 33 64 128 256), losses := [] }

theorem u5318 : Upper (D 8) (R 8) [96,68,288,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 292 137 146 40 113 177 305), lower := (rows 97 70 292 137 146 40 64 128 256), losses := [] }

theorem u5319 : Upper (D 8) (R 8) [96,68,288,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5319 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 70 292 137 146 48 105 169 297), lower := (rows 97 70 292 137 146 48 64 128 256), losses := [] }

theorem u5320 : Upper (D 8) (R 8) [96,68,288,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5320 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 292 137 176 33 90 154 282), lower := (rows 97 70 292 137 176 33 64 128 256), losses := [] }

theorem u5321 : Upper (D 8) (R 8) [96,68,288,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 70 292 137 176 34 89 153 281), lower := (rows 97 70 292 137 176 34 64 128 256), losses := [] }

theorem u5322 : Upper (D 8) (R 8) [96,68,288,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5322 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 70 292 137 176 40 83 147 275), lower := (rows 97 70 292 137 176 40 64 128 256), losses := [] }

theorem u5323 : Upper (D 8) (R 8) [96,68,288,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5323 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5324 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 70 292 137 176 48 75 139 267), lower := (rows 97 70 292 137 176 48 64 128 256), losses := [] }

theorem u5324 : Upper (D 8) (R 8) [96,68,288,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5324 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5325 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 292 138 176 33 89 153 281), lower := (rows 97 70 292 138 176 33 64 128 256), losses := [] }

theorem u5325 : Upper (D 8) (R 8) [96,68,288,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5326 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 70 292 138 176 40 81 145 273), lower := (rows 97 70 292 138 176 40 64 128 256), losses := [] }

theorem u5326 : Upper (D 8) (R 8) [96,68,288,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5326 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 70 292 138 176 48 73 137 265), lower := (rows 97 70 292 138 176 48 64 128 256), losses := [] }

theorem u5327 : Upper (D 8) (R 8) [96,68,288,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5327 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5328 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 56 336 33 224 160 416), lower := (rows 193 7 14 56 336 33 64 128 256), losses := [] }

theorem u5328 : Upper (D 8) (R 8) [192,5,10,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5329 : Route 9 := (fun mask => (mask,id))

def c5329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5329 : Upper (D 8) (R 8) [192,5,10,48,320,128] 13 := by
  apply FastRouting.sound _ _ [192,5,10,48,320,128] 13 (by decide) (choices 1) [1,32] r5329 c5329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u696
  · exact u697

def b5330 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 280 112 33 224 160 416), lower := (rows 193 7 14 280 112 33 64 128 256), losses := [] }

theorem u5330 : Upper (D 8) (R 8) [192,5,10,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5331 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 14 280 112 160 97 161 289), lower := (rows 193 7 14 280 112 160 64 128 256), losses := [] }

theorem u5331 : Upper (D 8) (R 8) [192,5,10,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 296 112 33 240 176 432), lower := (rows 193 7 14 296 112 33 64 128 256), losses := [] }

theorem u5332 : Upper (D 8) (R 8) [192,5,10,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5333 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 14 296 112 48 225 161 417), lower := (rows 193 7 14 296 112 48 64 128 256), losses := [] }

theorem u5333 : Upper (D 8) (R 8) [192,5,10,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5333 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5334 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 14 296 112 160 113 177 305), lower := (rows 193 7 14 296 112 160 64 128 256), losses := [] }

theorem u5334 : Upper (D 8) (R 8) [192,5,10,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5335 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 28 42 304 33 224 224 480), lower := (rows 193 7 28 42 304 33 64 128 256), losses := [] }

theorem u5335 : Upper (D 8) (R 8) [192,5,24,34,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5336 : PairBound 9 := { available := 161, camps := [], pairs := [(3,0)], upper := (rows 193 7 28 42 304 96 225 161 417), lower := (rows 193 7 28 42 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 97 64 128 256), good := (rows 224 46 28 42 304 96 96 128 256) }] }

theorem u5336 : Upper (D 8) (R 8) [192,5,24,34,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5337 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 56 280 33 224 224 480), lower := (rows 193 7 38 56 280 33 64 128 256), losses := [] }

theorem u5337 : Upper (D 8) (R 8) [192,5,34,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5338 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 193 7 38 56 280 96 225 161 417), lower := (rows 193 7 38 56 280 96 64 128 256), losses := [] }

theorem u5338 : Upper (D 8) (R 8) [192,5,34,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5339 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 56 336 33 232 168 424), lower := (rows 193 7 38 56 336 33 64 128 256), losses := [] }

theorem u5339 : Upper (D 8) (R 8) [192,5,34,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5339
end Delivery.IrregularNine14.P08
