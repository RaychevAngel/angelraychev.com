import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0019

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4260 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 113 146 44 328 17 166 198 134 390), lower := (rows 113 146 44 328 17 32 64 128 256), losses := [] }

theorem u4260 : Upper (D 1) (R 1) [112,144,40,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4261 : PairBound 9 := { available := 135, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 328 18 167 199 135 391), lower := (rows 113 146 44 328 18 32 64 128 256), losses := [] }

theorem u4261 : Upper (D 1) (R 1) [112,144,40,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4262 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 146 44 328 20 163 195 131 387), lower := (rows 113 146 44 328 20 32 64 128 256), losses := [] }

theorem u4262 : Upper (D 1) (R 1) [112,144,40,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4263 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 44 328 144 39 71 135 263), lower := (rows 113 146 44 328 144 32 64 128 256), losses := [] }

theorem u4263 : Upper (D 1) (R 1) [112,144,40,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4264 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 146 44 392 17 102 70 198 326), lower := (rows 113 146 44 392 17 32 64 128 256), losses := [] }

theorem u4264 : Upper (D 1) (R 1) [112,144,40,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4265 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 392 18 103 71 199 327), lower := (rows 113 146 44 392 18 32 64 128 256), losses := [] }

theorem u4265 : Upper (D 1) (R 1) [112,144,40,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4266 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 146 44 392 20 99 67 195 323), lower := (rows 113 146 44 392 20 32 64 128 256), losses := [] }

theorem u4266 : Upper (D 1) (R 1) [112,144,40,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4266
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4267 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 44 392 80 39 71 135 263), lower := (rows 113 146 44 392 80 32 64 128 256), losses := [] }

theorem u4267 : Upper (D 1) (R 1) [112,144,40,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4268 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 133 266 18 108 108 236 364), lower := (rows 113 146 133 266 18 32 64 128 256), losses := [] }

theorem u4268 : Upper (D 1) (R 1) [112,144,129,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4269 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 146 133 266 20 106 106 234 362), lower := (rows 113 146 133 266 20 32 64 128 256), losses := [] }

theorem u4269 : Upper (D 1) (R 1) [112,144,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4270 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 146 133 266 24 102 102 230 358), lower := (rows 113 146 133 266 24 32 64 128 256), losses := [] }

theorem u4270 : Upper (D 1) (R 1) [112,144,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 133 266 48 110 78 206 334), lower := (rows 113 146 133 266 48 32 64 128 256), losses := [] }

theorem u4271 : Upper (D 1) (R 1) [112,144,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 133 268 18 106 106 234 362), lower := (rows 113 146 133 268 18 32 64 128 256), losses := [] }

theorem u4272 : Upper (D 1) (R 1) [112,144,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4273 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 146 133 268 24 98 98 226 354), lower := (rows 113 146 133 268 24 32 64 128 256), losses := [] }

theorem u4273 : Upper (D 1) (R 1) [112,144,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4274 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 133 268 48 106 74 202 330), lower := (rows 113 146 133 268 48 32 64 128 256), losses := [] }

theorem u4274 : Upper (D 1) (R 1) [112,144,129,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4275 : PairBound 9 := { available := 78, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 133 296 18 110 78 206 334), lower := (rows 113 146 133 296 18 32 64 128 256), losses := [] }

theorem u4275 : Upper (D 1) (R 1) [112,144,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4276 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 146 133 296 20 106 74 202 330), lower := (rows 113 146 133 296 20 32 64 128 256), losses := [] }

theorem u4276 : Upper (D 1) (R 1) [112,144,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 146 133 296 24 102 70 198 326), lower := (rows 113 146 133 296 24 32 64 128 256), losses := [] }

theorem u4277 : Upper (D 1) (R 1) [112,144,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 133 296 80 46 78 142 270), lower := (rows 113 146 133 296 80 32 64 128 256), losses := [] }

theorem u4278 : Upper (D 1) (R 1) [112,144,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 140 265 18 102 102 230 358), lower := (rows 113 146 140 265 18 32 64 128 256), losses := [] }

theorem u4279 : Upper (D 1) (R 1) [112,144,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4279
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 146 140 265 20 98 98 226 354), lower := (rows 113 146 140 265 20 32 64 128 256), losses := [] }

theorem u4280 : Upper (D 1) (R 1) [112,144,136,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 140 265 48 102 70 198 326), lower := (rows 113 146 140 265 48 32 64 128 256), losses := [] }

theorem u4281 : Upper (D 1) (R 1) [112,144,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 146 140 266 17 102 102 230 358), lower := (rows 113 146 140 266 17 32 64 128 256), losses := [] }

theorem u4282 : Upper (D 1) (R 1) [112,144,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 140 266 18 101 101 229 357), lower := (rows 113 146 140 266 18 32 64 128 256), losses := [] }

theorem u4283 : Upper (D 1) (R 1) [112,144,136,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 146 140 266 20 99 99 227 355), lower := (rows 113 146 140 266 20 32 64 128 256), losses := [] }

theorem u4284 : Upper (D 1) (R 1) [112,144,136,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 140 266 48 103 71 199 327), lower := (rows 113 146 140 266 48 32 64 128 256), losses := [] }

theorem u4285 : Upper (D 1) (R 1) [112,144,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4286 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 146 140 296 17 102 70 198 326), lower := (rows 113 146 140 296 17 32 64 128 256), losses := [] }

theorem u4286 : Upper (D 1) (R 1) [112,144,136,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4286
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4287 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 140 296 18 103 71 199 327), lower := (rows 113 146 140 296 18 32 64 128 256), losses := [] }

theorem u4287 : Upper (D 1) (R 1) [112,144,136,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4287
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4288 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 146 140 296 20 99 67 195 323), lower := (rows 113 146 140 296 20 32 64 128 256), losses := [] }

theorem u4288 : Upper (D 1) (R 1) [112,144,136,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4289 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 140 296 80 39 71 135 263), lower := (rows 113 146 140 296 80 32 64 128 256), losses := [] }

theorem u4289 : Upper (D 1) (R 1) [112,144,136,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4289
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4290 : PairBound 9 := { available := 78, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 265 18 110 78 206 334), lower := (rows 113 146 164 265 18 32 64 128 256), losses := [] }

theorem u4290 : Upper (D 1) (R 1) [112,144,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4291 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 146 164 265 20 106 74 202 330), lower := (rows 113 146 164 265 20 32 64 128 256), losses := [] }

theorem u4291 : Upper (D 1) (R 1) [112,144,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4292 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 146 164 265 24 102 70 198 326), lower := (rows 113 146 164 265 24 32 64 128 256), losses := [] }

theorem u4292 : Upper (D 1) (R 1) [112,144,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 265 80 46 78 142 270), lower := (rows 113 146 164 265 80 32 64 128 256), losses := [] }

theorem u4293 : Upper (D 1) (R 1) [112,144,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4294 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 113 146 164 266 17 110 78 206 334), lower := (rows 113 146 164 266 17 32 64 128 256), losses := [] }

theorem u4294 : Upper (D 1) (R 1) [112,144,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4294
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4295 : PairBound 9 := { available := 77, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 266 18 109 77 205 333), lower := (rows 113 146 164 266 18 32 64 128 256), losses := [] }

theorem u4295 : Upper (D 1) (R 1) [112,144,160,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4296 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 146 164 266 20 107 75 203 331), lower := (rows 113 146 164 266 20 32 64 128 256), losses := [] }

theorem u4296 : Upper (D 1) (R 1) [112,144,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4296
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4297 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 113 146 164 266 24 103 71 199 327), lower := (rows 113 146 164 266 24 32 64 128 256), losses := [] }

theorem u4297 : Upper (D 1) (R 1) [112,144,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4298 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 266 80 47 79 143 271), lower := (rows 113 146 164 266 80 32 64 128 256), losses := [] }

theorem u4298 : Upper (D 1) (R 1) [112,144,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4299 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 146 164 268 17 106 74 202 330), lower := (rows 113 146 164 268 17 32 64 128 256), losses := [] }

theorem u4299 : Upper (D 1) (R 1) [112,144,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4299
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4300 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 268 18 107 75 203 331), lower := (rows 113 146 164 268 18 32 64 128 256), losses := [] }

theorem u4300 : Upper (D 1) (R 1) [112,144,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4301 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 146 164 268 24 99 67 195 323), lower := (rows 113 146 164 268 24 32 64 128 256), losses := [] }

theorem u4301 : Upper (D 1) (R 1) [112,144,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4302 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 268 80 43 75 139 267), lower := (rows 113 146 164 268 80 32 64 128 256), losses := [] }

theorem u4302 : Upper (D 1) (R 1) [112,144,160,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 113 146 164 328 17 46 78 142 270), lower := (rows 113 146 164 328 17 32 64 128 256), losses := [] }

theorem u4303 : Upper (D 1) (R 1) [112,144,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4304 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 328 18 47 79 143 271), lower := (rows 113 146 164 328 18 32 64 128 256), losses := [] }

theorem u4304 : Upper (D 1) (R 1) [112,144,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4305 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 146 164 328 20 43 75 139 267), lower := (rows 113 146 164 328 20 32 64 128 256), losses := [] }

theorem u4305 : Upper (D 1) (R 1) [112,144,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4306 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 113 146 164 328 24 39 71 135 263), lower := (rows 113 146 164 328 24 32 64 128 256), losses := [] }

theorem u4306 : Upper (D 1) (R 1) [112,144,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4307 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 259 14 140 18 240 240 240 496), lower := (rows 113 259 14 140 18 32 64 128 256), losses := [] }

theorem u4307 : Upper (D 1) (R 1) [112,257,10,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4308 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 259 14 140 48 242 210 210 466), lower := (rows 113 259 14 140 48 32 64 128 256), losses := [] }

theorem u4308 : Upper (D 1) (R 1) [112,257,10,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4309 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 113 259 14 140 144 114 114 242 370), lower := (rows 113 259 14 140 144 32 64 128 256), losses := [] }

theorem u4309 : Upper (D 1) (R 1) [112,257,10,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4310 : Route 9 := (fun mask => (mask,id))

def c4310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4310 : Upper (D 1) (R 1) [112,257,10,144,2] 13 := by
  apply FastRouting.sound _ _ [112,257,10,144,2] 13 (by decide) (choices 1) [4,64,128] r4310 c4310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1154
  · exact u1155
  · exact u1156

def b4311 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 259 14 152 20 226 226 226 482), lower := (rows 113 259 14 152 20 32 64 128 256), losses := [] }

theorem u4311 : Upper (D 1) (R 1) [112,257,10,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4312 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 259 14 152 48 230 198 198 454), lower := (rows 113 259 14 152 48 32 64 128 256), losses := [] }

theorem u4312 : Upper (D 1) (R 1) [112,257,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4312
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4313 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 259 14 152 144 102 102 230 358), lower := (rows 113 259 14 152 144 32 64 128 256), losses := [] }

theorem u4313 : Upper (D 1) (R 1) [112,257,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4314 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 259 28 138 18 228 228 228 484), lower := (rows 113 259 28 138 18 32 64 128 256), losses := [] }

theorem u4314 : Upper (D 1) (R 1) [112,257,24,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 259 28 138 20 226 226 226 482), lower := (rows 113 259 28 138 20 32 64 128 256), losses := [] }

theorem u4315 : Upper (D 1) (R 1) [112,257,24,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 259 28 138 48 230 198 198 454), lower := (rows 113 259 28 138 48 32 64 128 256), losses := [] }

theorem u4316 : Upper (D 1) (R 1) [112,257,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 28 138 144 102 102 230 358), lower := (rows 113 259 28 138 144 32 64 128 256), losses := [] }

theorem u4317 : Upper (D 1) (R 1) [112,257,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4317
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4318 : Route 9 := (fun mask => (mask,id))

def c4318 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4318 : Upper (D 1) (R 1) [112,257,24,160,2] 13 := by
  apply FastRouting.sound _ _ [112,257,24,160,2] 13 (by decide) (choices 1) [2,4,64,128] r4318 c4318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1157
  · exact u1158
  · exact u1159
  · exact u1160

def b4319 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 259 28 168 20 226 194 194 450), lower := (rows 113 259 28 168 20 32 64 128 256), losses := [] }

theorem u4319 : Upper (D 1) (R 1) [112,257,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4319
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4319
end Delivery.IrregularNine14.P01
