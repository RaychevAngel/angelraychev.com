import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4260 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 200 146 305 337 401 273), lower := (rows 97 7 44 200 146 32 64 128 256), losses := [] }

theorem u4260 : Upper (D 3) (R 3) [96,5,40,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4260
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4261 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 200 273 179 211 147 403), lower := (rows 97 7 44 200 273 32 64 128 256), losses := [] }

theorem u4261 : Upper (D 3) (R 3) [96,5,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4261
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4262 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 200 274 177 209 145 401), lower := (rows 97 7 44 200 274 32 64 128 256), losses := [] }

theorem u4262 : Upper (D 3) (R 3) [96,5,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4262
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4263 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 200 400 51 83 147 275), lower := (rows 97 7 44 200 400 32 64 128 256), losses := [] }

theorem u4263 : Upper (D 3) (R 3) [96,5,40,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4263
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4264 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 265 82 177 209 145 401), lower := (rows 97 7 44 265 82 32 64 128 256), losses := [] }

theorem u4264 : Upper (D 3) (R 3) [96,5,40,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4264
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4265 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 265 145 242 210 210 466), lower := (rows 97 7 44 265 145 32 64 128 256), losses := [] }

theorem u4265 : Upper (D 3) (R 3) [96,5,40,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4265
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4266 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 265 146 241 209 209 465), lower := (rows 97 7 44 265 146 32 64 128 256), losses := [] }

theorem u4266 : Upper (D 3) (R 3) [96,5,40,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4266
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4267 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 265 208 179 211 147 403), lower := (rows 97 7 44 265 208 32 64 128 256), losses := [] }

theorem u4267 : Upper (D 3) (R 3) [96,5,40,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4267
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4268 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 266 145 241 209 209 465), lower := (rows 97 7 44 266 145 32 64 128 256), losses := [] }

theorem u4268 : Upper (D 3) (R 3) [96,5,40,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4268
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4269 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 266 208 177 209 145 401), lower := (rows 97 7 44 266 208 32 64 128 256), losses := [] }

theorem u4269 : Upper (D 3) (R 3) [96,5,40,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4269
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4270 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 280 82 161 193 129 385), lower := (rows 97 7 44 280 82 32 64 128 256), losses := [] }

theorem u4270 : Upper (D 3) (R 3) [96,5,40,272,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4270
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 280 145 227 195 195 451), lower := (rows 97 7 44 280 145 32 64 128 256), losses := [] }

theorem u4271 : Upper (D 3) (R 3) [96,5,40,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4271
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 280 146 225 193 193 449), lower := (rows 97 7 44 280 146 32 64 128 256), losses := [] }

theorem u4272 : Upper (D 3) (R 3) [96,5,40,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4273 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 280 208 163 195 131 387), lower := (rows 97 7 44 280 208 32 64 128 256), losses := [] }

theorem u4273 : Upper (D 3) (R 3) [96,5,40,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4274 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 328 145 179 211 147 403), lower := (rows 97 7 44 328 145 32 64 128 256), losses := [] }

theorem u4274 : Upper (D 3) (R 3) [96,5,40,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4275 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 328 146 177 209 145 401), lower := (rows 97 7 44 328 146 32 64 128 256), losses := [] }

theorem u4275 : Upper (D 3) (R 3) [96,5,40,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4276 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 392 82 177 209 145 401), lower := (rows 97 7 44 392 82 32 64 128 256), losses := [] }

theorem u4276 : Upper (D 3) (R 3) [96,5,40,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 392 145 115 83 211 339), lower := (rows 97 7 44 392 145 32 64 128 256), losses := [] }

theorem u4277 : Upper (D 3) (R 3) [96,5,40,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 392 146 113 81 209 337), lower := (rows 97 7 44 392 146 32 64 128 256), losses := [] }

theorem u4278 : Upper (D 3) (R 3) [96,5,40,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 392 208 51 83 147 275), lower := (rows 97 7 44 392 208 32 64 128 256), losses := [] }

theorem u4279 : Upper (D 3) (R 3) [96,5,40,384,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4279
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 146 425 457 393 393), lower := (rows 97 7 100 25 146 32 64 128 256), losses := [] }

theorem u4280 : Upper (D 3) (R 3) [96,5,96,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 152 419 451 387 387), lower := (rows 97 7 100 25 152 32 64 128 256), losses := [] }

theorem u4281 : Upper (D 3) (R 3) [96,5,96,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4281
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 274 169 201 137 393), lower := (rows 97 7 100 25 274 32 64 128 256), losses := [] }

theorem u4282 : Upper (D 3) (R 3) [96,5,96,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4282
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 280 163 195 131 387), lower := (rows 97 7 100 25 280 32 64 128 256), losses := [] }

theorem u4283 : Upper (D 3) (R 3) [96,5,96,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4283
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 400 171 203 139 395), lower := (rows 97 7 100 25 400 32 64 128 256), losses := [] }

theorem u4284 : Upper (D 3) (R 3) [96,5,96,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 145 425 457 393 393), lower := (rows 97 7 100 26 145 32 64 128 256), losses := [] }

theorem u4285 : Upper (D 3) (R 3) [96,5,96,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4285
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4286 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 152 417 449 385 385), lower := (rows 97 7 100 26 152 32 64 128 256), losses := [] }

theorem u4286 : Upper (D 3) (R 3) [96,5,96,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4287 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 273 169 201 137 393), lower := (rows 97 7 100 26 273 32 64 128 256), losses := [] }

theorem u4287 : Upper (D 3) (R 3) [96,5,96,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4287
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4288 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 280 161 193 129 385), lower := (rows 97 7 100 26 280 32 64 128 256), losses := [] }

theorem u4288 : Upper (D 3) (R 3) [96,5,96,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4288
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4289 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 400 169 201 137 393), lower := (rows 97 7 100 26 400 32 64 128 256), losses := [] }

theorem u4289 : Upper (D 3) (R 3) [96,5,96,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4289
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4290 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 146 313 345 409 281), lower := (rows 97 7 100 137 146 32 64 128 256), losses := [] }

theorem u4290 : Upper (D 3) (R 3) [96,5,96,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4290
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4291 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 273 186 218 154 410), lower := (rows 97 7 100 137 273 32 64 128 256), losses := [] }

theorem u4291 : Upper (D 3) (R 3) [96,5,96,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4291
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4292 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 274 185 217 153 409), lower := (rows 97 7 100 137 274 32 64 128 256), losses := [] }

theorem u4292 : Upper (D 3) (R 3) [96,5,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4292
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 280 179 211 147 403), lower := (rows 97 7 100 137 280 32 64 128 256), losses := [] }

theorem u4293 : Upper (D 3) (R 3) [96,5,96,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4294 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 400 59 91 155 283), lower := (rows 97 7 100 137 400 32 64 128 256), losses := [] }

theorem u4294 : Upper (D 3) (R 3) [96,5,96,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4295 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 273 185 217 153 409), lower := (rows 97 7 100 138 273 32 64 128 256), losses := [] }

theorem u4295 : Upper (D 3) (R 3) [96,5,96,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4295
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4296 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 280 177 209 145 401), lower := (rows 97 7 100 138 280 32 64 128 256), losses := [] }

theorem u4296 : Upper (D 3) (R 3) [96,5,96,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4296
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4297 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 400 57 89 153 281), lower := (rows 97 7 100 138 400 32 64 128 256), losses := [] }

theorem u4297 : Upper (D 3) (R 3) [96,5,96,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4297
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4298 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 273 171 203 139 395), lower := (rows 97 7 100 152 273 32 64 128 256), losses := [] }

theorem u4298 : Upper (D 3) (R 3) [96,5,96,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4298
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4299 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 274 169 201 137 393), lower := (rows 97 7 100 152 274 32 64 128 256), losses := [] }

theorem u4299 : Upper (D 3) (R 3) [96,5,96,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4299
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4300 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 280 163 195 131 387), lower := (rows 97 7 100 152 280 32 64 128 256), losses := [] }

theorem u4300 : Upper (D 3) (R 3) [96,5,96,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4300
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4301 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 25 146 360 360 488 360), lower := (rows 97 7 133 25 146 32 64 128 256), losses := [] }

theorem u4301 : Upper (D 3) (R 3) [96,5,129,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4301
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4302 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 25 152 354 354 482 354), lower := (rows 97 7 133 25 152 32 64 128 256), losses := [] }

theorem u4302 : Upper (D 3) (R 3) [96,5,129,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4302
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 25 274 232 232 232 488), lower := (rows 97 7 133 25 274 32 64 128 256), losses := [] }

theorem u4303 : Upper (D 3) (R 3) [96,5,129,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4303
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4304 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 25 280 226 226 226 482), lower := (rows 97 7 133 25 280 32 64 128 256), losses := [] }

theorem u4304 : Upper (D 3) (R 3) [96,5,129,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4304
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4305 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 25 400 106 106 234 362), lower := (rows 97 7 133 25 400 32 64 128 256), losses := [] }

theorem u4305 : Upper (D 3) (R 3) [96,5,129,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4306 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 145 360 360 488 360), lower := (rows 97 7 133 26 145 32 64 128 256), losses := [] }

theorem u4306 : Upper (D 3) (R 3) [96,5,129,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4306
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4307 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 152 353 353 481 353), lower := (rows 97 7 133 26 152 32 64 128 256), losses := [] }

theorem u4307 : Upper (D 3) (R 3) [96,5,129,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4307
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4308 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 176 361 329 457 329), lower := (rows 97 7 133 26 176 32 64 128 256), losses := [] }

theorem u4308 : Upper (D 3) (R 3) [96,5,129,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4308
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4309 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 273 232 232 232 488), lower := (rows 97 7 133 26 273 32 64 128 256), losses := [] }

theorem u4309 : Upper (D 3) (R 3) [96,5,129,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4309
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4310 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 280 225 225 225 481), lower := (rows 97 7 133 26 280 32 64 128 256), losses := [] }

theorem u4310 : Upper (D 3) (R 3) [96,5,129,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4310
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4311 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 304 233 201 201 457), lower := (rows 97 7 133 26 304 32 64 128 256), losses := [] }

theorem u4311 : Upper (D 3) (R 3) [96,5,129,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4312 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 400 105 105 233 361), lower := (rows 97 7 133 26 400 32 64 128 256), losses := [] }

theorem u4312 : Upper (D 3) (R 3) [96,5,129,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4312
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4313 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 88 433 465 401 401), lower := (rows 97 7 133 42 88 32 64 128 256), losses := [] }

theorem u4313 : Upper (D 3) (R 3) [96,5,129,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4313
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4314 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 145 376 344 472 344), lower := (rows 97 7 133 42 145 32 64 128 256), losses := [] }

theorem u4314 : Upper (D 3) (R 3) [96,5,129,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4314
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 152 369 337 465 337), lower := (rows 97 7 133 42 152 32 64 128 256), losses := [] }

theorem u4315 : Upper (D 3) (R 3) [96,5,129,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4315
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 208 313 345 409 281), lower := (rows 97 7 133 42 208 32 64 128 256), losses := [] }

theorem u4316 : Upper (D 3) (R 3) [96,5,129,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4316
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 273 248 216 216 472), lower := (rows 97 7 133 42 273 32 64 128 256), losses := [] }

theorem u4317 : Upper (D 3) (R 3) [96,5,129,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4317
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4318 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 280 241 209 209 465), lower := (rows 97 7 133 42 280 32 64 128 256), losses := [] }

theorem u4318 : Upper (D 3) (R 3) [96,5,129,34,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4318
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4319 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 336 185 217 153 409), lower := (rows 97 7 133 42 336 32 64 128 256), losses := [] }

theorem u4319 : Upper (D 3) (R 3) [96,5,129,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4319
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4319
end Delivery.IrregularNine14.P03
