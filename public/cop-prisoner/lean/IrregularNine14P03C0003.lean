import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 68, camps := [], pairs := [], upper := (rows 35 67 44 265 145 160 80 196 324), lower := (rows 35 67 44 265 145 160 80 128 256), losses := [] }

theorem u180 : Upper (D 3) (R 3) [34,65,40,257,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 265 148 160 65 208 336), lower := (rows 35 67 44 265 148 160 65 128 256), losses := [] }

theorem u181 : Upper (D 3) (R 3) [34,65,40,257,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b181
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 67 44 265 148 160 80 193 321), lower := (rows 35 67 44 265 148 160 80 128 256), losses := [] }

theorem u182 : Upper (D 3) (R 3) [34,65,40,257,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b182
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 265 208 160 65 148 276), lower := (rows 35 67 44 265 208 160 65 128 256), losses := [] }

theorem u183 : Upper (D 3) (R 3) [34,65,40,257,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b183
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 44 265 208 160 68 145 273), lower := (rows 35 67 44 265 208 160 68 128 256), losses := [] }

theorem u184 : Upper (D 3) (R 3) [34,65,40,257,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 44 265 208 160 80 133 261), lower := (rows 35 67 44 265 208 160 80 128 256), losses := [] }

theorem u185 : Upper (D 3) (R 3) [34,65,40,257,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b185
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 328 145 160 65 148 276), lower := (rows 35 67 44 328 145 160 65 128 256), losses := [] }

theorem u186 : Upper (D 3) (R 3) [34,65,40,320,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b186
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 44 328 145 160 68 145 273), lower := (rows 35 67 44 328 145 160 68 128 256), losses := [] }

theorem u187 : Upper (D 3) (R 3) [34,65,40,320,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b187
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 44 328 145 160 80 133 261), lower := (rows 35 67 44 328 145 160 80 128 256), losses := [] }

theorem u188 : Upper (D 3) (R 3) [34,65,40,320,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b188
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 328 148 160 65 145 273), lower := (rows 35 67 44 328 148 160 65 128 256), losses := [] }

theorem u189 : Upper (D 3) (R 3) [34,65,40,320,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b189
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 67 44 328 148 160 80 129 257), lower := (rows 35 67 44 328 148 160 80 128 256), losses := [] }

theorem u190 : Upper (D 3) (R 3) [34,65,40,320,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b190
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 35 67 76 137 273 160 68 176 304), lower := (rows 35 67 76 137 273 160 68 128 256), losses := [] }

theorem u191 : Upper (D 3) (R 3) [34,65,72,129,257,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 35 67 76 137 273 160 80 164 292), lower := (rows 35 67 76 137 273 160 80 128 256), losses := [] }

theorem u192 : Upper (D 3) (R 3) [34,65,72,129,257,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b192
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 76 137 273 160 96 148 276), lower := (rows 35 67 76 137 273 160 96 128 256), losses := [] }

theorem u193 : Upper (D 3) (R 3) [34,65,72,129,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 76 137 276 160 65 176 304), lower := (rows 35 67 76 137 276 160 65 128 256), losses := [] }

theorem u194 : Upper (D 3) (R 3) [34,65,72,129,260,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b194
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 76 137 276 160 80 161 289), lower := (rows 35 67 76 137 276 160 80 128 256), losses := [] }

theorem u195 : Upper (D 3) (R 3) [34,65,72,129,260,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 76 137 276 160 96 145 273), lower := (rows 35 67 76 137 276 160 96 128 256), losses := [] }

theorem u196 : Upper (D 3) (R 3) [34,65,72,129,260,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b196
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 76 137 304 160 65 148 276), lower := (rows 35 67 76 137 304 160 65 128 256), losses := [] }

theorem u197 : Upper (D 3) (R 3) [34,65,72,129,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b197
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 76 137 304 160 68 145 273), lower := (rows 35 67 76 137 304 160 68 128 256), losses := [] }

theorem u198 : Upper (D 3) (R 3) [34,65,72,129,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b198
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 76 137 304 160 80 133 261), lower := (rows 35 67 76 137 304 160 80 128 256), losses := [] }

theorem u199 : Upper (D 3) (R 3) [34,65,72,129,288,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b199
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 76 152 273 160 65 164 292), lower := (rows 35 67 76 152 273 160 65 128 256), losses := [] }

theorem u200 : Upper (D 3) (R 3) [34,65,72,144,257,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b200
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 76 152 273 160 68 161 289), lower := (rows 35 67 76 152 273 160 68 128 256), losses := [] }

theorem u201 : Upper (D 3) (R 3) [34,65,72,144,257,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b201
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 76 152 273 160 96 133 261), lower := (rows 35 67 76 152 273 160 96 128 256), losses := [] }

theorem u202 : Upper (D 3) (R 3) [34,65,72,144,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b202
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 76 152 304 160 65 133 261), lower := (rows 35 67 76 152 304 160 65 128 256), losses := [] }

theorem u203 : Upper (D 3) (R 3) [34,65,72,144,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b203
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 67 76 152 304 160 68 129 257), lower := (rows 35 67 76 152 304 160 68 128 256), losses := [] }

theorem u204 : Upper (D 3) (R 3) [34,65,72,144,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b204
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 35 67 76 265 145 160 68 176 304), lower := (rows 35 67 76 265 145 160 68 128 256), losses := [] }

theorem u205 : Upper (D 3) (R 3) [34,65,72,257,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b205
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 35 67 76 265 145 160 80 164 292), lower := (rows 35 67 76 265 145 160 80 128 256), losses := [] }

theorem u206 : Upper (D 3) (R 3) [34,65,72,257,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 76 265 145 160 96 148 276), lower := (rows 35 67 76 265 145 160 96 128 256), losses := [] }

theorem u207 : Upper (D 3) (R 3) [34,65,72,257,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 76 265 148 160 65 176 304), lower := (rows 35 67 76 265 148 160 65 128 256), losses := [] }

theorem u208 : Upper (D 3) (R 3) [34,65,72,257,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 76 265 148 160 80 161 289), lower := (rows 35 67 76 265 148 160 80 128 256), losses := [] }

theorem u209 : Upper (D 3) (R 3) [34,65,72,257,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 76 265 148 160 96 145 273), lower := (rows 35 67 76 265 148 160 96 128 256), losses := [] }

theorem u210 : Upper (D 3) (R 3) [34,65,72,257,132,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b210
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 76 280 145 160 65 164 292), lower := (rows 35 67 76 280 145 160 65 128 256), losses := [] }

theorem u211 : Upper (D 3) (R 3) [34,65,72,272,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b211
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 76 280 145 160 68 161 289), lower := (rows 35 67 76 280 145 160 68 128 256), losses := [] }

theorem u212 : Upper (D 3) (R 3) [34,65,72,272,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b212
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 76 280 145 160 96 133 261), lower := (rows 35 67 76 280 145 160 96 128 256), losses := [] }

theorem u213 : Upper (D 3) (R 3) [34,65,72,272,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b213
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 296 145 160 65 148 276), lower := (rows 35 67 76 296 145 160 65 128 256), losses := [] }

theorem u214 : Upper (D 3) (R 3) [34,65,72,288,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 76 296 145 160 68 145 273), lower := (rows 35 67 76 296 145 160 68 128 256), losses := [] }

theorem u215 : Upper (D 3) (R 3) [34,65,72,288,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b215
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 76 296 145 160 80 133 261), lower := (rows 35 67 76 296 145 160 80 128 256), losses := [] }

theorem u216 : Upper (D 3) (R 3) [34,65,72,288,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 296 148 160 65 145 273), lower := (rows 35 67 76 296 148 160 65 128 256), losses := [] }

theorem u217 : Upper (D 3) (R 3) [34,65,72,288,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b217
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 67 76 296 148 160 80 129 257), lower := (rows 35 67 76 296 148 160 80 128 256), losses := [] }

theorem u218 : Upper (D 3) (R 3) [34,65,72,288,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 88 145 160 65 168 296), lower := (rows 35 70 261 88 145 160 65 128 256), losses := [] }

theorem u219 : Upper (D 3) (R 3) [34,68,257,80,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b219
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 261 88 145 160 72 161 289), lower := (rows 35 70 261 88 145 160 72 128 256), losses := [] }

theorem u220 : Upper (D 3) (R 3) [34,68,257,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b220
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 88 145 160 96 137 265), lower := (rows 35 70 261 88 145 160 96 128 256), losses := [] }

theorem u221 : Upper (D 3) (R 3) [34,68,257,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b221
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 104 145 160 65 152 280), lower := (rows 35 70 261 104 145 160 65 128 256), losses := [] }

theorem u222 : Upper (D 3) (R 3) [34,68,257,96,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 261 104 145 160 72 145 273), lower := (rows 35 70 261 104 145 160 72 128 256), losses := [] }

theorem u223 : Upper (D 3) (R 3) [34,68,257,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b223
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 261 104 145 160 80 137 265), lower := (rows 35 70 261 104 145 160 80 128 256), losses := [] }

theorem u224 : Upper (D 3) (R 3) [34,68,257,96,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b224
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 104 152 160 65 145 273), lower := (rows 35 70 261 104 152 160 65 128 256), losses := [] }

theorem u225 : Upper (D 3) (R 3) [34,68,257,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 70 261 104 152 160 80 129 257), lower := (rows 35 70 261 104 152 160 80 128 256), losses := [] }

theorem u226 : Upper (D 3) (R 3) [34,68,257,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b226
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 259 13 76 145 160 80 224 352), lower := (rows 35 259 13 76 145 160 80 128 256), losses := [] }

theorem u227 : Upper (D 3) (R 3) [34,257,9,68,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 35 259 13 76 145 160 96 208 336), lower := (rows 35 259 13 76 145 160 96 128 256), losses := [] }

theorem u228 : Upper (D 3) (R 3) [34,257,9,68,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 35 259 13 88 145 96 68 160 416), lower := (rows 35 259 13 88 145 96 68 128 256), losses := [] }

theorem u229 : Upper (D 3) (R 3) [34,257,9,80,129,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b229
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 88 145 96 96 132 388), lower := (rows 35 259 13 88 145 96 96 128 256), losses := [] }

theorem u230 : Upper (D 3) (R 3) [34,257,9,80,129,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b230
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 13 88 145 96 192 164 292), lower := (rows 35 259 13 88 145 96 192 128 256), losses := [] }

theorem u231 : Upper (D 3) (R 3) [34,257,9,80,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b231
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 259 13 88 145 160 68 224 352), lower := (rows 35 259 13 88 145 160 68 128 256), losses := [] }

theorem u232 : Upper (D 3) (R 3) [34,257,9,80,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b232
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 88 145 160 96 196 324), lower := (rows 35 259 13 88 145 160 96 128 256), losses := [] }

theorem u233 : Upper (D 3) (R 3) [34,257,9,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b233
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 35 259 13 200 81 160 68 176 304), lower := (rows 35 259 13 200 81 160 68 128 256), losses := [] }

theorem u234 : Upper (D 3) (R 3) [34,257,9,192,65,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b234
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 35 259 13 200 81 160 80 164 292), lower := (rows 35 259 13 200 81 160 80 128 256), losses := [] }

theorem u235 : Upper (D 3) (R 3) [34,257,9,192,65,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b235
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 200 81 160 96 148 276), lower := (rows 35 259 13 200 81 160 96 128 256), losses := [] }

theorem u236 : Upper (D 3) (R 3) [34,257,9,192,65,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b236
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 35 259 28 73 145 96 68 160 416), lower := (rows 35 259 28 73 145 96 68 128 256), losses := [] }

theorem u237 : Upper (D 3) (R 3) [34,257,24,65,129,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b237
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 73 145 96 96 132 388), lower := (rows 35 259 28 73 145 96 96 128 256), losses := [] }

theorem u238 : Upper (D 3) (R 3) [34,257,24,65,129,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 76, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 28 73 145 96 192 164 292), lower := (rows 35 259 28 73 145 96 192 128 256), losses := [] }

theorem u239 : Upper (D 3) (R 3) [34,257,24,65,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b239
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P03
