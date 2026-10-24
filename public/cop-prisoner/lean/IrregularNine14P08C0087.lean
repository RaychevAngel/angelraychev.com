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

def b5220 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 168 82 160 81 145 273), lower := (rows 97 38 268 168 82 160 64 128 256), losses := [] }

theorem u5220 : Upper (D 8) (R 8) [96,36,264,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5221 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 38 268 168 145 33 82 210 338), lower := (rows 97 38 268 168 145 33 64 128 256), losses := [] }

theorem u5221 : Upper (D 8) (R 8) [96,36,264,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5222 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 268 168 145 34 81 209 337), lower := (rows 97 38 268 168 145 34 64 128 256), losses := [] }

theorem u5222 : Upper (D 8) (R 8) [96,36,264,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5222 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5223 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 268 168 145 48 67 195 323), lower := (rows 97 38 268 168 145 48 64 128 256), losses := [] }

theorem u5223 : Upper (D 8) (R 8) [96,36,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5223 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5224 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 168 145 96 83 147 275), lower := (rows 97 38 268 168 145 96 64 128 256), losses := [] }

theorem u5224 : Upper (D 8) (R 8) [96,36,264,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5225 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 168 208 33 83 147 275), lower := (rows 97 38 268 168 208 33 64 128 256), losses := [] }

theorem u5225 : Upper (D 8) (R 8) [96,36,264,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5226 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 268 168 208 34 81 145 273), lower := (rows 97 38 268 168 208 34 64 128 256), losses := [] }

theorem u5226 : Upper (D 8) (R 8) [96,36,264,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5226 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5227 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 268 168 208 48 67 131 259), lower := (rows 97 38 268 168 208 48 64 128 256), losses := [] }

theorem u5227 : Upper (D 8) (R 8) [96,36,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5227 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5228 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 200 145 33 114 178 306), lower := (rows 97 38 268 200 145 33 64 128 256), losses := [] }

theorem u5228 : Upper (D 8) (R 8) [96,36,264,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5229 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 268 200 145 34 113 177 305), lower := (rows 97 38 268 200 145 34 64 128 256), losses := [] }

theorem u5229 : Upper (D 8) (R 8) [96,36,264,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5229 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5230 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 268 200 145 48 99 163 291), lower := (rows 97 38 268 200 145 48 64 128 256), losses := [] }

theorem u5230 : Upper (D 8) (R 8) [96,36,264,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5230 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5231 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 200 176 33 83 147 275), lower := (rows 97 38 268 200 176 33 64 128 256), losses := [] }

theorem u5231 : Upper (D 8) (R 8) [96,36,264,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5232 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 268 200 176 34 81 145 273), lower := (rows 97 38 268 200 176 34 64 128 256), losses := [] }

theorem u5232 : Upper (D 8) (R 8) [96,36,264,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5232 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5233 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 268 200 176 48 67 131 259), lower := (rows 97 38 268 200 176 48 64 128 256), losses := [] }

theorem u5233 : Upper (D 8) (R 8) [96,36,264,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5233 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 324 137 146 33 120 184 312), lower := (rows 97 38 324 137 146 33 64 128 256), losses := [] }

theorem u5234 : Upper (D 8) (R 8) [96,36,320,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5235 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 324 137 146 40 113 177 305), lower := (rows 97 38 324 137 146 40 64 128 256), losses := [] }

theorem u5235 : Upper (D 8) (R 8) [96,36,320,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5235 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5236 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 324 137 146 48 105 169 297), lower := (rows 97 38 324 137 146 48 64 128 256), losses := [] }

theorem u5236 : Upper (D 8) (R 8) [96,36,320,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5236 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5237 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 324 137 176 33 90 154 282), lower := (rows 97 38 324 137 176 33 64 128 256), losses := [] }

theorem u5237 : Upper (D 8) (R 8) [96,36,320,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 324 137 176 34 89 153 281), lower := (rows 97 38 324 137 176 34 64 128 256), losses := [] }

theorem u5238 : Upper (D 8) (R 8) [96,36,320,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5238 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5239 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 324 137 176 40 83 147 275), lower := (rows 97 38 324 137 176 40 64 128 256), losses := [] }

theorem u5239 : Upper (D 8) (R 8) [96,36,320,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5239 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5240 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 324 137 176 48 75 139 267), lower := (rows 97 38 324 137 176 48 64 128 256), losses := [] }

theorem u5240 : Upper (D 8) (R 8) [96,36,320,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5240 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 324 138 176 33 89 153 281), lower := (rows 97 38 324 138 176 33 64 128 256), losses := [] }

theorem u5241 : Upper (D 8) (R 8) [96,36,320,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5242 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 324 138 176 40 81 145 273), lower := (rows 97 38 324 138 176 40 64 128 256), losses := [] }

theorem u5242 : Upper (D 8) (R 8) [96,36,320,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5242 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5243 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 324 138 176 48 73 137 265), lower := (rows 97 38 324 138 176 48 64 128 256), losses := [] }

theorem u5243 : Upper (D 8) (R 8) [96,36,320,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5243 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 388 74 145 33 120 184 312), lower := (rows 97 38 388 74 145 33 64 128 256), losses := [] }

theorem u5244 : Upper (D 8) (R 8) [96,36,384,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 388 74 145 40 113 177 305), lower := (rows 97 38 388 74 145 40 64 128 256), losses := [] }

theorem u5245 : Upper (D 8) (R 8) [96,36,384,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5245 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5246 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 388 74 145 48 105 169 297), lower := (rows 97 38 388 74 145 48 64 128 256), losses := [] }

theorem u5246 : Upper (D 8) (R 8) [96,36,384,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5246 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5247 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 388 74 176 33 89 153 281), lower := (rows 97 38 388 74 176 33 64 128 256), losses := [] }

theorem u5247 : Upper (D 8) (R 8) [96,36,384,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5248 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 388 74 176 40 81 145 273), lower := (rows 97 38 388 74 176 40 64 128 256), losses := [] }

theorem u5248 : Upper (D 8) (R 8) [96,36,384,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5248 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5249 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 388 74 176 48 73 137 265), lower := (rows 97 38 388 74 176 48 64 128 256), losses := [] }

theorem u5249 : Upper (D 8) (R 8) [96,36,384,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5249 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5250 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 388 88 145 33 106 170 298), lower := (rows 97 38 388 88 145 33 64 128 256), losses := [] }

theorem u5250 : Upper (D 8) (R 8) [96,36,384,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5251 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 388 88 145 34 105 169 297), lower := (rows 97 38 388 88 145 34 64 128 256), losses := [] }

theorem u5251 : Upper (D 8) (R 8) [96,36,384,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5251 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5252 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 388 88 145 40 99 163 291), lower := (rows 97 38 388 88 145 40 64 128 256), losses := [] }

theorem u5252 : Upper (D 8) (R 8) [96,36,384,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5252 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5253 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 388 88 176 33 75 139 267), lower := (rows 97 38 388 88 176 33 64 128 256), losses := [] }

theorem u5253 : Upper (D 8) (R 8) [96,36,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5254 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 388 88 176 34 73 137 265), lower := (rows 97 38 388 88 176 34 64 128 256), losses := [] }

theorem u5254 : Upper (D 8) (R 8) [96,36,384,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5254 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5255 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 388 88 176 40 67 131 259), lower := (rows 97 38 388 88 176 40 64 128 256), losses := [] }

theorem u5255 : Upper (D 8) (R 8) [96,36,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5255 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5256 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 70 133 152 273 34 104 168 296), lower := (rows 97 70 133 152 273 34 64 128 256), losses := [] }

theorem u5256 : Upper (D 8) (R 8) [96,68,129,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5256 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5257 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 70 133 152 273 40 98 162 290), lower := (rows 97 70 133 152 273 40 64 128 256), losses := [] }

theorem u5257 : Upper (D 8) (R 8) [96,68,129,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5257 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5258 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 152 304 33 106 170 298), lower := (rows 97 70 133 152 304 33 64 128 256), losses := [] }

theorem u5258 : Upper (D 8) (R 8) [96,68,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5259 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 70 133 152 304 34 105 169 297), lower := (rows 97 70 133 152 304 34 64 128 256), losses := [] }

theorem u5259 : Upper (D 8) (R 8) [96,68,129,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5259 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 133 152 304 40 99 163 291), lower := (rows 97 70 133 152 304 40 64 128 256), losses := [] }

theorem u5260 : Upper (D 8) (R 8) [96,68,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5260 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5261 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 70 133 168 273 34 120 184 312), lower := (rows 97 70 133 168 273 34 64 128 256), losses := [] }

theorem u5261 : Upper (D 8) (R 8) [96,68,129,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5261 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5262 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 70 133 168 273 40 114 178 306), lower := (rows 97 70 133 168 273 40 64 128 256), losses := [] }

theorem u5262 : Upper (D 8) (R 8) [96,68,129,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5262 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5263 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 70 133 168 273 48 106 170 298), lower := (rows 97 70 133 168 273 48 64 128 256), losses := [] }

theorem u5263 : Upper (D 8) (R 8) [96,68,129,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5263 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5264 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 168 274 33 120 184 312), lower := (rows 97 70 133 168 274 33 64 128 256), losses := [] }

theorem u5264 : Upper (D 8) (R 8) [96,68,129,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5265 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 133 168 274 40 113 177 305), lower := (rows 97 70 133 168 274 40 64 128 256), losses := [] }

theorem u5265 : Upper (D 8) (R 8) [96,68,129,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5265 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5266 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 70 133 168 274 48 105 169 297), lower := (rows 97 70 133 168 274 48 64 128 256), losses := [] }

theorem u5266 : Upper (D 8) (R 8) [96,68,129,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5266 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5267 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 168 280 33 114 178 306), lower := (rows 97 70 133 168 280 33 64 128 256), losses := [] }

theorem u5267 : Upper (D 8) (R 8) [96,68,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 133 168 280 34 113 177 305), lower := (rows 97 70 133 168 280 34 64 128 256), losses := [] }

theorem u5268 : Upper (D 8) (R 8) [96,68,129,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5268 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5269 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 133 168 280 48 99 163 291), lower := (rows 97 70 133 168 280 48 64 128 256), losses := [] }

theorem u5269 : Upper (D 8) (R 8) [96,68,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5269 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5270 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 168 304 33 90 154 282), lower := (rows 97 70 133 168 304 33 64 128 256), losses := [] }

theorem u5270 : Upper (D 8) (R 8) [96,68,129,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5271 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 70 133 168 304 34 89 153 281), lower := (rows 97 70 133 168 304 34 64 128 256), losses := [] }

theorem u5271 : Upper (D 8) (R 8) [96,68,129,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5271 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5272 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 70 133 168 304 40 83 147 275), lower := (rows 97 70 133 168 304 40 64 128 256), losses := [] }

theorem u5272 : Upper (D 8) (R 8) [96,68,129,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5272 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 70 133 168 304 48 75 139 267), lower := (rows 97 70 133 168 304 48 64 128 256), losses := [] }

theorem u5273 : Upper (D 8) (R 8) [96,68,129,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5273 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 70 140 265 145 34 112 176 304), lower := (rows 97 70 140 265 145 34 64 128 256), losses := [] }

theorem u5274 : Upper (D 8) (R 8) [96,68,136,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5274 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5275 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 70 140 265 145 48 98 162 290), lower := (rows 97 70 140 265 145 48 64 128 256), losses := [] }

theorem u5275 : Upper (D 8) (R 8) [96,68,136,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5275 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5276 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 265 176 33 114 178 306), lower := (rows 97 70 140 265 176 33 64 128 256), losses := [] }

theorem u5276 : Upper (D 8) (R 8) [96,68,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5277 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 70 140 265 176 34 113 177 305), lower := (rows 97 70 140 265 176 34 64 128 256), losses := [] }

theorem u5277 : Upper (D 8) (R 8) [96,68,136,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5277 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5278 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 70 140 265 176 48 99 163 291), lower := (rows 97 70 140 265 176 48 64 128 256), losses := [] }

theorem u5278 : Upper (D 8) (R 8) [96,68,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5278 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5279 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 140 296 145 33 114 178 306), lower := (rows 97 70 140 296 145 33 64 128 256), losses := [] }

theorem u5279 : Upper (D 8) (R 8) [96,68,136,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5279
end Delivery.IrregularNine14.P08
