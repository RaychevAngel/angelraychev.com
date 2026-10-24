import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4200 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 14 296 80 167 199 135 391), lower := (rows 113 146 14 296 80 32 64 128 256), losses := [] }

theorem u4200 : Upper (D 1) (R 1) [112,144,10,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4201 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 14 296 144 103 71 199 327), lower := (rows 113 146 14 296 144 32 64 128 256), losses := [] }

theorem u4201 : Upper (D 1) (R 1) [112,144,10,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4202 : PairBound 9 := { available := 396, camps := [], pairs := [], upper := (rows 113 146 38 74 17 428 460 396 396), lower := (rows 113 146 38 74 17 32 64 128 256), losses := [] }

theorem u4202 : Upper (D 1) (R 1) [112,144,34,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4203 : PairBound 9 := { available := 393, camps := [], pairs := [], upper := (rows 113 146 38 74 20 425 457 393 393), lower := (rows 113 146 38 74 20 32 64 128 256), losses := [] }

theorem u4203 : Upper (D 1) (R 1) [112,144,34,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4204 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 38 74 144 301 333 397 269), lower := (rows 113 146 38 74 144 32 64 128 256), losses := [] }

theorem u4204 : Upper (D 1) (R 1) [112,144,34,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4205 : PairBound 9 := { available := 141, camps := [], pairs := [], upper := (rows 113 146 38 74 272 173 205 141 397), lower := (rows 113 146 38 74 272 32 64 128 256), losses := [] }

theorem u4205 : Upper (D 1) (R 1) [112,144,34,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4206 : PairBound 9 := { available := 394, camps := [], pairs := [], upper := (rows 113 146 38 76 17 426 458 394 394), lower := (rows 113 146 38 76 17 32 64 128 256), losses := [] }

theorem u4206 : Upper (D 1) (R 1) [112,144,34,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 393, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 76 18 425 457 393 393), lower := (rows 113 146 38 76 18 32 64 128 256), losses := [] }

theorem u4207 : Upper (D 1) (R 1) [112,144,34,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4208 : PairBound 9 := { available := 387, camps := [], pairs := [], upper := (rows 113 146 38 76 24 419 451 387 387), lower := (rows 113 146 38 76 24 32 64 128 256), losses := [] }

theorem u4208 : Upper (D 1) (R 1) [112,144,34,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4209 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 38 76 144 299 331 395 267), lower := (rows 113 146 38 76 144 32 64 128 256), losses := [] }

theorem u4209 : Upper (D 1) (R 1) [112,144,34,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4209
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4210 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 113 146 38 76 272 171 203 139 395), lower := (rows 113 146 38 76 272 32 64 128 256), losses := [] }

theorem u4210 : Upper (D 1) (R 1) [112,144,34,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 332, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 137 18 364 332 460 332), lower := (rows 113 146 38 137 18 32 64 128 256), losses := [] }

theorem u4211 : Upper (D 1) (R 1) [112,144,34,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4212 : PairBound 9 := { available := 330, camps := [], pairs := [], upper := (rows 113 146 38 137 20 362 330 458 330), lower := (rows 113 146 38 137 20 32 64 128 256), losses := [] }

theorem u4212 : Upper (D 1) (R 1) [112,144,34,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4213 : PairBound 9 := { available := 326, camps := [], pairs := [], upper := (rows 113 146 38 137 24 358 326 454 326), lower := (rows 113 146 38 137 24 32 64 128 256), losses := [] }

theorem u4213 : Upper (D 1) (R 1) [112,144,34,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4213
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 38 137 80 302 334 398 270), lower := (rows 113 146 38 137 80 32 64 128 256), losses := [] }

theorem u4214 : Upper (D 1) (R 1) [112,144,34,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4214
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 113 146 38 137 272 110 78 206 334), lower := (rows 113 146 38 137 272 32 64 128 256), losses := [] }

theorem u4215 : Upper (D 1) (R 1) [112,144,34,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4216 : PairBound 9 := { available := 330, camps := [], pairs := [], upper := (rows 113 146 38 140 17 362 330 458 330), lower := (rows 113 146 38 140 17 32 64 128 256), losses := [] }

theorem u4216 : Upper (D 1) (R 1) [112,144,34,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4217 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 140 18 361 329 457 329), lower := (rows 113 146 38 140 18 32 64 128 256), losses := [] }

theorem u4217 : Upper (D 1) (R 1) [112,144,34,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 323, camps := [], pairs := [], upper := (rows 113 146 38 140 24 355 323 451 323), lower := (rows 113 146 38 140 24 32 64 128 256), losses := [] }

theorem u4218 : Upper (D 1) (R 1) [112,144,34,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4218
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 38 140 80 299 331 395 267), lower := (rows 113 146 38 140 80 32 64 128 256), losses := [] }

theorem u4219 : Upper (D 1) (R 1) [112,144,34,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4219
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 146 38 140 272 107 75 203 331), lower := (rows 113 146 38 140 272 32 64 128 256), losses := [] }

theorem u4220 : Upper (D 1) (R 1) [112,144,34,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4221 : PairBound 9 := { available := 270, camps := [], pairs := [], upper := (rows 113 146 38 200 17 302 334 398 270), lower := (rows 113 146 38 200 17 32 64 128 256), losses := [] }

theorem u4221 : Upper (D 1) (R 1) [112,144,34,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4222 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 200 18 301 333 397 269), lower := (rows 113 146 38 200 18 32 64 128 256), losses := [] }

theorem u4222 : Upper (D 1) (R 1) [112,144,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4222
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4223 : PairBound 9 := { available := 267, camps := [], pairs := [], upper := (rows 113 146 38 200 20 299 331 395 267), lower := (rows 113 146 38 200 20 32 64 128 256), losses := [] }

theorem u4223 : Upper (D 1) (R 1) [112,144,34,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4223
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 263, camps := [], pairs := [], upper := (rows 113 146 38 200 24 295 327 391 263), lower := (rows 113 146 38 200 24 32 64 128 256), losses := [] }

theorem u4224 : Upper (D 1) (R 1) [112,144,34,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4224
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4225 : PairBound 9 := { available := 15, camps := [], pairs := [], upper := (rows 113 146 38 200 272 47 79 143 271), lower := (rows 113 146 38 200 272 32 64 128 256), losses := [] }

theorem u4225 : Upper (D 1) (R 1) [112,144,34,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4225
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4226 : PairBound 9 := { available := 204, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 265 18 236 204 204 460), lower := (rows 113 146 38 265 18 32 64 128 256), losses := [] }

theorem u4226 : Upper (D 1) (R 1) [112,144,34,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4226
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4227 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 146 38 265 20 234 202 202 458), lower := (rows 113 146 38 265 20 32 64 128 256), losses := [] }

theorem u4227 : Upper (D 1) (R 1) [112,144,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4227
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 113 146 38 265 24 230 198 198 454), lower := (rows 113 146 38 265 24 32 64 128 256), losses := [] }

theorem u4228 : Upper (D 1) (R 1) [112,144,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4228
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4229 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 38 265 80 174 206 142 398), lower := (rows 113 146 38 265 80 32 64 128 256), losses := [] }

theorem u4229 : Upper (D 1) (R 1) [112,144,34,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4230 : PairBound 9 := { available := 78, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 38 265 144 110 78 206 334), lower := (rows 113 146 38 265 144 32 64 128 256), losses := [] }

theorem u4230 : Upper (D 1) (R 1) [112,144,34,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4230
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4231 : PairBound 9 := { available := 204, camps := [], pairs := [], upper := (rows 113 146 38 266 17 236 204 204 460), lower := (rows 113 146 38 266 17 32 64 128 256), losses := [] }

theorem u4231 : Upper (D 1) (R 1) [112,144,34,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4232 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 146 38 266 20 233 201 201 457), lower := (rows 113 146 38 266 20 32 64 128 256), losses := [] }

theorem u4232 : Upper (D 1) (R 1) [112,144,34,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4233 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 113 146 38 266 24 229 197 197 453), lower := (rows 113 146 38 266 24 32 64 128 256), losses := [] }

theorem u4233 : Upper (D 1) (R 1) [112,144,34,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 38 266 80 173 205 141 397), lower := (rows 113 146 38 266 80 32 64 128 256), losses := [] }

theorem u4234 : Upper (D 1) (R 1) [112,144,34,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 38 266 144 109 77 205 333), lower := (rows 113 146 38 266 144 32 64 128 256), losses := [] }

theorem u4235 : Upper (D 1) (R 1) [112,144,34,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4236 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 146 38 268 17 234 202 202 458), lower := (rows 113 146 38 268 17 32 64 128 256), losses := [] }

theorem u4236 : Upper (D 1) (R 1) [112,144,34,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4237 : PairBound 9 := { available := 201, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 268 18 233 201 201 457), lower := (rows 113 146 38 268 18 32 64 128 256), losses := [] }

theorem u4237 : Upper (D 1) (R 1) [112,144,34,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 146 38 268 24 227 195 195 451), lower := (rows 113 146 38 268 24 32 64 128 256), losses := [] }

theorem u4238 : Upper (D 1) (R 1) [112,144,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4239 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 38 268 80 171 203 139 395), lower := (rows 113 146 38 268 80 32 64 128 256), losses := [] }

theorem u4239 : Upper (D 1) (R 1) [112,144,34,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4239
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4240 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 38 268 144 107 75 203 331), lower := (rows 113 146 38 268 144 32 64 128 256), losses := [] }

theorem u4240 : Upper (D 1) (R 1) [112,144,34,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4241 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 113 146 38 328 17 174 206 142 398), lower := (rows 113 146 38 328 17 32 64 128 256), losses := [] }

theorem u4241 : Upper (D 1) (R 1) [112,144,34,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4242 : PairBound 9 := { available := 141, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 328 18 173 205 141 397), lower := (rows 113 146 38 328 18 32 64 128 256), losses := [] }

theorem u4242 : Upper (D 1) (R 1) [112,144,34,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4243 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 113 146 38 328 20 171 203 139 395), lower := (rows 113 146 38 328 20 32 64 128 256), losses := [] }

theorem u4243 : Upper (D 1) (R 1) [112,144,34,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4244 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 113 146 38 328 24 167 199 135 391), lower := (rows 113 146 38 328 24 32 64 128 256), losses := [] }

theorem u4244 : Upper (D 1) (R 1) [112,144,34,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4245 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 38 328 144 47 79 143 271), lower := (rows 113 146 38 328 144 32 64 128 256), losses := [] }

theorem u4245 : Upper (D 1) (R 1) [112,144,34,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4246 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 113 146 38 392 17 110 78 206 334), lower := (rows 113 146 38 392 17 32 64 128 256), losses := [] }

theorem u4246 : Upper (D 1) (R 1) [112,144,34,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4247 : PairBound 9 := { available := 77, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 38 392 18 109 77 205 333), lower := (rows 113 146 38 392 18 32 64 128 256), losses := [] }

theorem u4247 : Upper (D 1) (R 1) [112,144,34,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4248 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 146 38 392 20 107 75 203 331), lower := (rows 113 146 38 392 20 32 64 128 256), losses := [] }

theorem u4248 : Upper (D 1) (R 1) [112,144,34,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4248
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4249 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 113 146 38 392 24 103 71 199 327), lower := (rows 113 146 38 392 24 32 64 128 256), losses := [] }

theorem u4249 : Upper (D 1) (R 1) [112,144,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4250 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 38 392 80 47 79 143 271), lower := (rows 113 146 38 392 80 32 64 128 256), losses := [] }

theorem u4250 : Upper (D 1) (R 1) [112,144,34,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4251 : PairBound 9 := { available := 262, camps := [], pairs := [], upper := (rows 113 146 44 200 17 294 326 390 262), lower := (rows 113 146 44 200 17 32 64 128 256), losses := [] }

theorem u4251 : Upper (D 1) (R 1) [112,144,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4252 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 200 18 295 327 391 263), lower := (rows 113 146 44 200 18 32 64 128 256), losses := [] }

theorem u4252 : Upper (D 1) (R 1) [112,144,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4253 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 113 146 44 200 20 291 323 387 259), lower := (rows 113 146 44 200 20 32 64 128 256), losses := [] }

theorem u4253 : Upper (D 1) (R 1) [112,144,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4254 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 113 146 44 200 272 39 71 135 263), lower := (rows 113 146 44 200 272 32 64 128 256), losses := [] }

theorem u4254 : Upper (D 1) (R 1) [112,144,40,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4255 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 113 146 44 266 17 230 198 198 454), lower := (rows 113 146 44 266 17 32 64 128 256), losses := [] }

theorem u4255 : Upper (D 1) (R 1) [112,144,40,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4256 : PairBound 9 := { available := 197, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 266 18 229 197 197 453), lower := (rows 113 146 44 266 18 32 64 128 256), losses := [] }

theorem u4256 : Upper (D 1) (R 1) [112,144,40,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 146 44 266 20 227 195 195 451), lower := (rows 113 146 44 266 20 32 64 128 256), losses := [] }

theorem u4257 : Upper (D 1) (R 1) [112,144,40,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4257
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4258 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 44 266 80 167 199 135 391), lower := (rows 113 146 44 266 80 32 64 128 256), losses := [] }

theorem u4258 : Upper (D 1) (R 1) [112,144,40,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4259 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 44 266 144 103 71 199 327), lower := (rows 113 146 44 266 144 32 64 128 256), losses := [] }

theorem u4259 : Upper (D 1) (R 1) [112,144,40,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4259
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4259
end Delivery.IrregularNine14.P01
