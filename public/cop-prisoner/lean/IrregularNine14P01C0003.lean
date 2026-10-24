import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 275 35 84 168 144 96 68 138 266), lower := (rows 275 35 84 168 144 96 68 128 256), losses := [] }

theorem u180 : Upper (D 1) (R 1) [274,33,80,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 275 35 84 168 144 96 72 134 262), lower := (rows 275 35 84 168 144 96 72 128 256), losses := [] }

theorem u181 : Upper (D 1) (R 1) [274,33,80,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 13 74 144 160 80 224 352), lower := (rows 275 38 13 74 144 160 80 128 256), losses := [] }

theorem u182 : Upper (D 1) (R 1) [274,36,9,66,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 72, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 13 74 144 160 96 208 336), lower := (rows 275 38 13 74 144 160 96 128 256), losses := [] }

theorem u183 : Upper (D 1) (R 1) [274,36,9,66,128,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 88 144 160 66 168 296), lower := (rows 275 38 69 88 144 160 66 128 256), losses := [] }

theorem u184 : Upper (D 1) (R 1) [274,36,65,80,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 275 38 69 88 144 160 72 162 290), lower := (rows 275 38 69 88 144 160 72 128 256), losses := [] }

theorem u185 : Upper (D 1) (R 1) [274,36,65,80,128,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 104, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 69 88 144 160 96 138 266), lower := (rows 275 38 69 88 144 160 96 128 256), losses := [] }

theorem u186 : Upper (D 1) (R 1) [274,36,65,80,128,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 16 }], pairs := [(2,4)], upper := (rows 275 38 69 104 144 160 66 152 280), lower := (rows 275 38 69 104 144 160 66 128 256), losses := [] }

theorem u187 : Upper (D 1) (R 1) [274,36,65,96,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 18, camps := [], pairs := [], upper := (rows 275 38 69 104 144 160 72 146 274), lower := (rows 275 38 69 104 144 160 72 128 256), losses := [] }

theorem u188 : Upper (D 1) (R 1) [274,36,65,96,128,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 104 144 160 80 138 266), lower := (rows 275 38 69 104 144 160 80 128 256), losses := [] }

theorem u189 : Upper (D 1) (R 1) [274,36,65,96,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 70 200 48 160 66 152 280), lower := (rows 277 35 70 200 48 160 66 128 256), losses := [] }

theorem u190 : Upper (D 1) (R 1) [276,33,66,192,32,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 18, camps := [], pairs := [], upper := (rows 277 35 70 200 48 160 72 146 274), lower := (rows 277 35 70 200 48 160 72 128 256), losses := [] }

theorem u191 : Upper (D 1) (R 1) [276,33,66,192,32,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 277 35 70 200 48 160 80 138 266), lower := (rows 277 35 70 200 48 160 80 128 256), losses := [] }

theorem u192 : Upper (D 1) (R 1) [276,33,66,192,32,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 277 42 196 88 18 160 65 162 290), lower := (rows 277 42 196 88 18 160 65 128 256), losses := [] }

theorem u193 : Upper (D 1) (R 1) [276,40,192,80,2,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 88, targets := 32 }], pairs := [(3,5)], upper := (rows 277 42 196 88 18 160 66 161 289), lower := (rows 277 42 196 88 18 160 66 128 256), losses := [] }

theorem u194 : Upper (D 1) (R 1) [276,40,192,80,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b194
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 277 42 196 88 18 160 96 131 259), lower := (rows 277 42 196 88 18 160 96 128 256), losses := [] }

theorem u195 : Upper (D 1) (R 1) [276,40,192,80,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 66, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 73 144 160 66 146 274), lower := (rows 277 98 44 73 144 160 66 128 256), losses := [] }

theorem u196 : Upper (D 1) (R 1) [276,96,40,65,128,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 44 73 144 160 80 130 258), lower := (rows 277 98 44 73 144 160 80 128 256), losses := [] }

theorem u197 : Upper (D 1) (R 1) [276,96,40,65,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 78, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 88 144 96 66 160 416), lower := (rows 305 7 14 88 144 96 66 128 256), losses := [] }

theorem u198 : Upper (D 1) (R 1) [304,5,10,80,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b198
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 7 14 88 144 96 96 130 386), lower := (rows 305 7 14 88 144 96 96 128 256), losses := [] }

theorem u199 : Upper (D 1) (R 1) [304,5,10,80,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b199
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 14 88 144 96 192 162 290), lower := (rows 305 7 14 88 144 96 192 128 256), losses := [] }

theorem u200 : Upper (D 1) (R 1) [304,5,10,80,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 417, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 14 200 80 160 66 176 304), lower := (rows 305 7 14 200 80 160 66 128 256), losses := [] }

theorem u201 : Upper (D 1) (R 1) [304,5,10,192,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 14 200 80 160 80 162 290), lower := (rows 305 7 14 200 80 160 80 128 256), losses := [] }

theorem u202 : Upper (D 1) (R 1) [304,5,10,192,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 14 200 80 160 96 146 274), lower := (rows 305 7 14 200 80 160 96 128 256), losses := [] }

theorem u203 : Upper (D 1) (R 1) [304,5,10,192,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 152 80 160 66 168 296), lower := (rows 305 7 70 152 80 160 66 128 256), losses := [] }

theorem u204 : Upper (D 1) (R 1) [304,5,66,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 7 70 152 80 160 72 162 290), lower := (rows 305 7 70 152 80 160 72 128 256), losses := [] }

theorem u205 : Upper (D 1) (R 1) [304,5,66,144,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 70, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 70 152 80 160 96 138 266), lower := (rows 305 7 70 152 80 160 96 128 256), losses := [] }

theorem u206 : Upper (D 1) (R 1) [304,5,66,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 305 7 76 138 80 160 66 176 304), lower := (rows 305 7 76 138 80 160 66 128 256), losses := [] }

theorem u207 : Upper (D 1) (R 1) [304,5,72,130,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 168, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 76 138 80 160 80 162 290), lower := (rows 305 7 76 138 80 160 80 128 256), losses := [] }

theorem u208 : Upper (D 1) (R 1) [304,5,72,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 100, targets := 2 }], pairs := [(2,1)], upper := (rows 305 7 76 138 80 160 96 146 274), lower := (rows 305 7 76 138 80 160 96 128 256), losses := [] }

theorem u209 : Upper (D 1) (R 1) [304,5,72,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b209
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 34, camps := [], pairs := [(0,6)], upper := (rows 305 7 76 152 80 160 66 162 290), lower := (rows 305 7 76 152 80 160 66 128 256), losses := [{ target := 6, region := (rows 17 2 4 24 16 254 0 194 322), good := (rows 313 423 428 185 441 160 418 160 256) }] }

theorem u210 : Upper (D 1) (R 1) [304,5,72,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 92, targets := 2 }], pairs := [(2,1)], upper := (rows 305 7 76 152 80 160 96 130 258), lower := (rows 305 7 76 152 80 160 96 128 256), losses := [] }

theorem u211 : Upper (D 1) (R 1) [304,5,72,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 88, targets := 32 }], pairs := [(3,5)], upper := (rows 305 7 196 88 18 160 66 168 296), lower := (rows 305 7 196 88 18 160 66 128 256), losses := [] }

theorem u212 : Upper (D 1) (R 1) [304,5,192,80,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 7 196 88 18 160 72 162 290), lower := (rows 305 7 196 88 18 160 72 128 256), losses := [] }

theorem u213 : Upper (D 1) (R 1) [304,5,192,80,2,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b213
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 196 88 18 160 96 138 266), lower := (rows 305 7 196 88 18 160 96 128 256), losses := [] }

theorem u214 : Upper (D 1) (R 1) [304,5,192,80,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b214
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 78, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 7 88 144 96 66 160 416), lower := (rows 305 14 7 88 144 96 66 128 256), losses := [] }

theorem u215 : Upper (D 1) (R 1) [304,12,3,80,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 14 7 88 144 96 96 130 386), lower := (rows 305 14 7 88 144 96 96 128 256), losses := [] }

theorem u216 : Upper (D 1) (R 1) [304,12,3,80,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 7 88 144 96 192 162 290), lower := (rows 305 14 7 88 144 96 192 128 256), losses := [] }

theorem u217 : Upper (D 1) (R 1) [304,12,3,80,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 417, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 7 200 80 160 66 176 304), lower := (rows 305 14 7 200 80 160 66 128 256), losses := [] }

theorem u218 : Upper (D 1) (R 1) [304,12,3,192,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b218
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 305 14 7 200 80 160 80 162 290), lower := (rows 305 14 7 200 80 160 80 128 256), losses := [] }

theorem u219 : Upper (D 1) (R 1) [304,12,3,192,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b219
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 305 14 7 200 80 160 96 146 274), lower := (rows 305 14 7 200 80 160 96 128 256), losses := [] }

theorem u220 : Upper (D 1) (R 1) [304,12,3,192,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 78, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 73 144 96 66 160 416), lower := (rows 305 14 22 73 144 96 66 128 256), losses := [] }

theorem u221 : Upper (D 1) (R 1) [304,12,18,65,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 22 73 144 96 96 130 386), lower := (rows 305 14 22 73 144 96 96 128 256), losses := [] }

theorem u222 : Upper (D 1) (R 1) [304,12,18,65,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b222
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 34, camps := [], pairs := [(3,1)], upper := (rows 305 14 22 73 144 96 192 162 290), lower := (rows 305 14 22 73 144 96 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 208 253 208 128 256), good := (rows 377 44 116 121 240 112 240 240 256) }] }

theorem u223 : Upper (D 1) (R 1) [304,12,18,65,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b223
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 417, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 69 138 80 160 66 176 304), lower := (rows 305 14 69 138 80 160 66 128 256), losses := [] }

theorem u224 : Upper (D 1) (R 1) [304,12,65,130,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b224
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 170, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 69 138 80 160 80 162 290), lower := (rows 305 14 69 138 80 160 80 128 256), losses := [] }

theorem u225 : Upper (D 1) (R 1) [304,12,65,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b225
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 69 138 80 160 96 146 274), lower := (rows 305 14 69 138 80 160 96 128 256), losses := [] }

theorem u226 : Upper (D 1) (R 1) [304,12,65,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b226
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 34, camps := [], pairs := [(0,6)], upper := (rows 305 14 69 152 80 160 66 162 290), lower := (rows 305 14 69 152 80 160 66 128 256), losses := [{ target := 6, region := (rows 17 2 4 24 16 254 0 194 322), good := (rows 313 430 421 185 441 160 418 160 256) }] }

theorem u227 : Upper (D 1) (R 1) [304,12,65,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b227
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 69 152 80 160 96 130 258), lower := (rows 305 14 69 152 80 160 96 128 256), losses := [] }

theorem u228 : Upper (D 1) (R 1) [304,12,65,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b228
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 14 70 152 80 160 65 162 290), lower := (rows 305 14 70 152 80 160 65 128 256), losses := [] }

theorem u229 : Upper (D 1) (R 1) [304,12,66,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 70 152 80 160 66 161 289), lower := (rows 305 14 70 152 80 160 66 128 256), losses := [] }

theorem u230 : Upper (D 1) (R 1) [304,12,66,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b230
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 102, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 70 152 80 160 96 131 259), lower := (rows 305 14 70 152 80 160 96 128 256), losses := [] }

theorem u231 : Upper (D 1) (R 1) [304,12,66,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 14 84 168 18 96 65 130 386), lower := (rows 305 14 84 168 18 96 65 128 256), losses := [] }

theorem u232 : Upper (D 1) (R 1) [304,12,80,160,2,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 305 14 84 168 18 96 66 129 385), lower := (rows 305 14 84 168 18 96 66 128 256), losses := [] }

theorem u233 : Upper (D 1) (R 1) [304,12,80,160,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 84 168 18 96 192 131 259), lower := (rows 305 14 84 168 18 96 192 128 256), losses := [] }

theorem u234 : Upper (D 1) (R 1) [304,12,80,160,2,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 2, camps := [], pairs := [], upper := (rows 305 14 84 168 144 96 65 130 258), lower := (rows 305 14 84 168 144 96 65 128 256), losses := [] }

theorem u235 : Upper (D 1) (R 1) [304,12,80,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 84 168 144 96 66 131 259), lower := (rows 305 14 84 168 144 96 66 128 256), losses := [] }

theorem u236 : Upper (D 1) (R 1) [304,12,80,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 78, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 73 144 96 66 160 416), lower := (rows 305 22 14 73 144 96 66 128 256), losses := [] }

theorem u237 : Upper (D 1) (R 1) [304,20,10,65,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 73 144 96 96 130 386), lower := (rows 305 22 14 73 144 96 96 128 256), losses := [] }

theorem u238 : Upper (D 1) (R 1) [304,20,10,65,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 34, camps := [], pairs := [(3,1)], upper := (rows 305 22 14 73 144 96 192 162 290), lower := (rows 305 22 14 73 144 96 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 208 251 208 128 256), good := (rows 377 116 44 121 240 112 240 240 256) }] }

theorem u239 : Upper (D 1) (R 1) [304,20,10,65,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b239
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P01
