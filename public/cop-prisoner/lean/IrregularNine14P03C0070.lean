import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4200 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 336 185 217 153 409), lower := (rows 97 7 37 138 336 32 64 128 256), losses := [] }

theorem u4200 : Upper (D 3) (R 3) [96,5,33,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4200
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4201 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 400 121 89 217 345), lower := (rows 97 7 37 138 400 32 64 128 256), losses := [] }

theorem u4201 : Upper (D 3) (R 3) [96,5,33,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4201
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4202 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 273 234 202 202 458), lower := (rows 97 7 37 152 273 32 64 128 256), losses := [] }

theorem u4202 : Upper (D 3) (R 3) [96,5,33,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4202
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4203 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 274 233 201 201 457), lower := (rows 97 7 37 152 274 32 64 128 256), losses := [] }

theorem u4203 : Upper (D 3) (R 3) [96,5,33,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4203
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4204 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 280 227 195 195 451), lower := (rows 97 7 37 152 280 32 64 128 256), losses := [] }

theorem u4204 : Upper (D 3) (R 3) [96,5,33,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4204
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4205 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 336 171 203 139 395), lower := (rows 97 7 37 152 336 32 64 128 256), losses := [] }

theorem u4205 : Upper (D 3) (R 3) [96,5,33,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4205
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4206 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 273 186 218 154 410), lower := (rows 97 7 37 200 273 32 64 128 256), losses := [] }

theorem u4206 : Upper (D 3) (R 3) [96,5,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 274 185 217 153 409), lower := (rows 97 7 37 200 274 32 64 128 256), losses := [] }

theorem u4207 : Upper (D 3) (R 3) [96,5,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4208 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 280 179 211 147 403), lower := (rows 97 7 37 200 280 32 64 128 256), losses := [] }

theorem u4208 : Upper (D 3) (R 3) [96,5,33,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4209 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 400 59 91 155 283), lower := (rows 97 7 37 200 400 32 64 128 256), losses := [] }

theorem u4209 : Upper (D 3) (R 3) [96,5,33,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4210 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 152 481 449 449 449), lower := (rows 97 7 38 25 152 32 64 128 256), losses := [] }

theorem u4210 : Upper (D 3) (R 3) [96,5,34,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4210
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 280 225 193 193 449), lower := (rows 97 7 38 25 280 32 64 128 256), losses := [] }

theorem u4211 : Upper (D 3) (R 3) [96,5,34,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4211
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4212 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 400 233 201 201 457), lower := (rows 97 7 38 25 400 32 64 128 256), losses := [] }

theorem u4212 : Upper (D 3) (R 3) [96,5,34,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4212
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4213 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 145 425 457 393 393), lower := (rows 97 7 38 88 145 32 64 128 256), losses := [] }

theorem u4213 : Upper (D 3) (R 3) [96,5,34,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4213
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 273 169 201 137 393), lower := (rows 97 7 38 88 273 32 64 128 256), losses := [] }

theorem u4214 : Upper (D 3) (R 3) [96,5,34,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 400 169 201 137 393), lower := (rows 97 7 38 88 400 32 64 128 256), losses := [] }

theorem u4215 : Upper (D 3) (R 3) [96,5,34,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4215
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4216 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 208 313 345 409 281), lower := (rows 97 7 38 137 208 32 64 128 256), losses := [] }

theorem u4216 : Upper (D 3) (R 3) [96,5,34,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4217 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 273 248 216 216 472), lower := (rows 97 7 38 137 273 32 64 128 256), losses := [] }

theorem u4217 : Upper (D 3) (R 3) [96,5,34,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4217
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 280 241 209 209 465), lower := (rows 97 7 38 137 280 32 64 128 256), losses := [] }

theorem u4218 : Upper (D 3) (R 3) [96,5,34,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 336 185 217 153 409), lower := (rows 97 7 38 137 336 32 64 128 256), losses := [] }

theorem u4219 : Upper (D 3) (R 3) [96,5,34,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4219
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 400 121 89 217 345), lower := (rows 97 7 38 137 400 32 64 128 256), losses := [] }

theorem u4220 : Upper (D 3) (R 3) [96,5,34,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4220
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4221 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 273 233 201 201 457), lower := (rows 97 7 38 152 273 32 64 128 256), losses := [] }

theorem u4221 : Upper (D 3) (R 3) [96,5,34,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4221
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4222 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 280 225 193 193 449), lower := (rows 97 7 38 152 280 32 64 128 256), losses := [] }

theorem u4222 : Upper (D 3) (R 3) [96,5,34,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4223 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 336 169 201 137 393), lower := (rows 97 7 38 152 336 32 64 128 256), losses := [] }

theorem u4223 : Upper (D 3) (R 3) [96,5,34,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4223
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 273 185 217 153 409), lower := (rows 97 7 38 200 273 32 64 128 256), losses := [] }

theorem u4224 : Upper (D 3) (R 3) [96,5,34,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4224
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4225 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 280 177 209 145 401), lower := (rows 97 7 38 200 280 32 64 128 256), losses := [] }

theorem u4225 : Upper (D 3) (R 3) [96,5,34,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4226 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 400 57 89 153 281), lower := (rows 97 7 38 200 400 32 64 128 256), losses := [] }

theorem u4226 : Upper (D 3) (R 3) [96,5,34,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4226
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4227 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 25 146 481 449 449 449), lower := (rows 97 7 44 25 146 32 64 128 256), losses := [] }

theorem u4227 : Upper (D 3) (R 3) [96,5,40,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 25 274 225 193 193 449), lower := (rows 97 7 44 25 274 32 64 128 256), losses := [] }

theorem u4228 : Upper (D 3) (R 3) [96,5,40,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4229 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 25 400 227 195 195 451), lower := (rows 97 7 44 25 400 32 64 128 256), losses := [] }

theorem u4229 : Upper (D 3) (R 3) [96,5,40,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4229
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4230 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 26 145 481 449 449 449), lower := (rows 97 7 44 26 145 32 64 128 256), losses := [] }

theorem u4230 : Upper (D 3) (R 3) [96,5,40,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4230
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4231 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 26 208 417 449 385 385), lower := (rows 97 7 44 26 208 32 64 128 256), losses := [] }

theorem u4231 : Upper (D 3) (R 3) [96,5,40,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4231
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4232 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 26 273 225 193 193 449), lower := (rows 97 7 44 26 273 32 64 128 256), losses := [] }

theorem u4232 : Upper (D 3) (R 3) [96,5,40,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4232
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4233 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 26 336 161 193 129 385), lower := (rows 97 7 44 26 336 32 64 128 256), losses := [] }

theorem u4233 : Upper (D 3) (R 3) [96,5,40,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4233
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 26 400 225 193 193 449), lower := (rows 97 7 44 26 400 32 64 128 256), losses := [] }

theorem u4234 : Upper (D 3) (R 3) [96,5,40,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4234
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 145 433 465 401 401), lower := (rows 97 7 44 74 145 32 64 128 256), losses := [] }

theorem u4235 : Upper (D 3) (R 3) [96,5,40,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4235
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4236 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 273 177 209 145 401), lower := (rows 97 7 44 74 273 32 64 128 256), losses := [] }

theorem u4236 : Upper (D 3) (R 3) [96,5,40,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4236
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4237 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 400 177 209 145 401), lower := (rows 97 7 44 74 400 32 64 128 256), losses := [] }

theorem u4237 : Upper (D 3) (R 3) [96,5,40,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4237
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 88 145 419 451 387 387), lower := (rows 97 7 44 88 145 32 64 128 256), losses := [] }

theorem u4238 : Upper (D 3) (R 3) [96,5,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4239 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 88 146 417 449 385 385), lower := (rows 97 7 44 88 146 32 64 128 256), losses := [] }

theorem u4239 : Upper (D 3) (R 3) [96,5,40,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4239
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4240 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 88 273 163 195 131 387), lower := (rows 97 7 44 88 273 32 64 128 256), losses := [] }

theorem u4240 : Upper (D 3) (R 3) [96,5,40,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4240
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4241 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 88 274 161 193 129 385), lower := (rows 97 7 44 88 274 32 64 128 256), losses := [] }

theorem u4241 : Upper (D 3) (R 3) [96,5,40,80,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4241
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4242 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 88 400 163 195 131 387), lower := (rows 97 7 44 88 400 32 64 128 256), losses := [] }

theorem u4242 : Upper (D 3) (R 3) [96,5,40,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4242
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4243 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 82 433 465 401 401), lower := (rows 97 7 44 137 82 32 64 128 256), losses := [] }

theorem u4243 : Upper (D 3) (R 3) [96,5,40,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4243
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4244 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 146 369 337 465 337), lower := (rows 97 7 44 137 146 32 64 128 256), losses := [] }

theorem u4244 : Upper (D 3) (R 3) [96,5,40,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4245 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 208 307 339 403 275), lower := (rows 97 7 44 137 208 32 64 128 256), losses := [] }

theorem u4245 : Upper (D 3) (R 3) [96,5,40,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4246 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 273 242 210 210 466), lower := (rows 97 7 44 137 273 32 64 128 256), losses := [] }

theorem u4246 : Upper (D 3) (R 3) [96,5,40,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4247 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 274 241 209 209 465), lower := (rows 97 7 44 137 274 32 64 128 256), losses := [] }

theorem u4247 : Upper (D 3) (R 3) [96,5,40,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4248 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 336 179 211 147 403), lower := (rows 97 7 44 137 336 32 64 128 256), losses := [] }

theorem u4248 : Upper (D 3) (R 3) [96,5,40,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4249 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 400 115 83 211 339), lower := (rows 97 7 44 137 400 32 64 128 256), losses := [] }

theorem u4249 : Upper (D 3) (R 3) [96,5,40,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4250 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 138 145 369 337 465 337), lower := (rows 97 7 44 138 145 32 64 128 256), losses := [] }

theorem u4250 : Upper (D 3) (R 3) [96,5,40,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4250
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4251 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 138 208 305 337 401 273), lower := (rows 97 7 44 138 208 32 64 128 256), losses := [] }

theorem u4251 : Upper (D 3) (R 3) [96,5,40,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4252 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 138 273 241 209 209 465), lower := (rows 97 7 44 138 273 32 64 128 256), losses := [] }

theorem u4252 : Upper (D 3) (R 3) [96,5,40,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4252
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4253 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 138 336 177 209 145 401), lower := (rows 97 7 44 138 336 32 64 128 256), losses := [] }

theorem u4253 : Upper (D 3) (R 3) [96,5,40,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4254 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 138 400 113 81 209 337), lower := (rows 97 7 44 138 400 32 64 128 256), losses := [] }

theorem u4254 : Upper (D 3) (R 3) [96,5,40,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4254
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4255 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 152 82 417 449 385 385), lower := (rows 97 7 44 152 82 32 64 128 256), losses := [] }

theorem u4255 : Upper (D 3) (R 3) [96,5,40,144,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4256 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 152 273 227 195 195 451), lower := (rows 97 7 44 152 273 32 64 128 256), losses := [] }

theorem u4256 : Upper (D 3) (R 3) [96,5,40,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4256
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 152 274 225 193 193 449), lower := (rows 97 7 44 152 274 32 64 128 256), losses := [] }

theorem u4257 : Upper (D 3) (R 3) [96,5,40,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4257
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4258 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 152 336 163 195 131 387), lower := (rows 97 7 44 152 336 32 64 128 256), losses := [] }

theorem u4258 : Upper (D 3) (R 3) [96,5,40,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4258
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4259 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 200 145 307 339 403 275), lower := (rows 97 7 44 200 145 32 64 128 256), losses := [] }

theorem u4259 : Upper (D 3) (R 3) [96,5,40,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4259
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4259
end Delivery.IrregularNine14.P03
