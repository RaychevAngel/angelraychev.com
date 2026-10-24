import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 35 7 324 25 208 160 65 136 288), lower := (rows 35 7 324 25 208 160 65 136 256), losses := [] }

theorem u0 : Upper (D 3) (R 3) [34,5,320,17,192,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b0
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 326, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 25 208 160 65 160 264), lower := (rows 35 7 324 25 208 160 65 160 256), losses := [] }

theorem u1 : Upper (D 3) (R 3) [34,5,320,17,192,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 21 104 304 160 65 192 448), lower := (rows 7 11 21 104 304 160 65 128 256), losses := [] }

theorem u2 : Upper (D 3) (R 3) [6,9,17,96,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 21 104 304 160 192 193 321), lower := (rows 7 11 21 104 304 160 192 128 256), losses := [] }

theorem u3 : Upper (D 3) (R 3) [6,9,17,96,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 104 400 33 192 224 352), lower := (rows 7 11 21 104 400 33 192 128 256), losses := [] }

theorem u4 : Upper (D 3) (R 3) [6,9,17,96,384,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 21 104 400 96 192 161 289), lower := (rows 7 11 21 104 400 96 192 128 256), losses := [] }

theorem u5 : Upper (D 3) (R 3) [6,9,17,96,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 88 304 160 65 192 448), lower := (rows 7 11 37 88 304 160 65 128 256), losses := [] }

theorem u6 : Upper (D 3) (R 3) [6,9,33,80,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 65, camps := [], pairs := [(3,0)], upper := (rows 7 11 37 88 304 160 192 193 321), lower := (rows 7 11 37 88 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 6 10 100 120 376 224 224 224 256) }] }

theorem u7 : Upper (D 3) (R 3) [6,9,33,80,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 280 112 160 65 192 448), lower := (rows 7 11 37 280 112 160 65 128 256), losses := [] }

theorem u8 : Upper (D 3) (R 3) [6,9,33,272,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b8
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 280 112 160 192 193 321), lower := (rows 7 11 37 280 112 160 192 128 256), losses := [] }

theorem u9 : Upper (D 3) (R 3) [6,9,33,272,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b9
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 328 112 160 65 144 400), lower := (rows 7 11 37 328 112 160 65 128 256), losses := [] }

theorem u10 : Upper (D 3) (R 3) [6,9,33,320,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b10
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 11 37 328 112 160 80 129 385), lower := (rows 7 11 37 328 112 160 80 128 256), losses := [] }

theorem u11 : Upper (D 3) (R 3) [6,9,33,320,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b11
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 328 112 160 192 145 273), lower := (rows 7 11 37 328 112 160 192 128 256), losses := [] }

theorem u12 : Upper (D 3) (R 3) [6,9,33,320,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b12
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 328 208 160 65 176 304), lower := (rows 7 11 37 328 208 160 65 128 256), losses := [] }

theorem u13 : Upper (D 3) (R 3) [6,9,33,320,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b13
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 11 37 328 208 160 80 161 289), lower := (rows 7 11 37 328 208 160 80 128 256), losses := [] }

theorem u14 : Upper (D 3) (R 3) [6,9,33,320,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b14
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 37 328 208 160 96 145 273), lower := (rows 7 11 37 328 208 160 96 128 256), losses := [] }

theorem u15 : Upper (D 3) (R 3) [6,9,33,320,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b15
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 7 11 52 200 273 96 65 160 416), lower := (rows 7 11 52 200 273 96 65 128 256), losses := [] }

theorem u16 : Upper (D 3) (R 3) [6,9,48,192,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b16
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 52 200 273 96 96 129 385), lower := (rows 7 11 52 200 273 96 96 128 256), losses := [] }

theorem u17 : Upper (D 3) (R 3) [6,9,48,192,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b17
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 200 273 96 192 161 289), lower := (rows 7 11 52 200 273 96 192 128 256), losses := [] }

theorem u18 : Upper (D 3) (R 3) [6,9,48,192,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b18
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 160, camps := [], pairs := [(2,6)], upper := (rows 7 11 52 200 336 33 65 160 416), lower := (rows 7 11 52 200 336 33 65 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 99 0 255 383), good := (rows 423 427 436 424 436 417 417 128 256) }] }

theorem u19 : Upper (D 3) (R 3) [6,9,48,192,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b19
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 129, camps := [], pairs := [(3,5)], upper := (rows 7 11 52 200 336 33 96 129 385), lower := (rows 7 11 52 200 336 33 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 72 80 0 64 163 291), good := (rows 391 395 404 216 344 385 472 128 256) }] }

theorem u20 : Upper (D 3) (R 3) [6,9,48,192,320,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b20
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 200 336 33 192 161 289), lower := (rows 7 11 52 200 336 33 192 128 256), losses := [] }

theorem u21 : Upper (D 3) (R 3) [6,9,48,192,320,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b21
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 33, camps := [], pairs := [(2,6)], upper := (rows 7 11 52 200 336 160 65 161 289), lower := (rows 7 11 52 200 336 160 65 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 251 0 195 323), good := (rows 423 427 52 424 436 160 417 160 256) }] }

theorem u22 : Upper (D 3) (R 3) [6,9,48,192,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b22
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 200 336 160 96 129 257), lower := (rows 7 11 52 200 336 160 96 128 256), losses := [] }

theorem u23 : Upper (D 3) (R 3) [6,9,48,192,320,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b23
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 7 11 52 328 145 96 65 160 416), lower := (rows 7 11 52 328 145 96 65 128 256), losses := [] }

theorem u24 : Upper (D 3) (R 3) [6,9,48,320,129,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b24
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 52 328 145 96 96 129 385), lower := (rows 7 11 52 328 145 96 96 128 256), losses := [] }

theorem u25 : Upper (D 3) (R 3) [6,9,48,320,129,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b25
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 145 96 192 161 289), lower := (rows 7 11 52 328 145 96 192 128 256), losses := [] }

theorem u26 : Upper (D 3) (R 3) [6,9,48,320,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b26
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 160, camps := [], pairs := [(2,6)], upper := (rows 7 11 52 328 208 33 65 160 416), lower := (rows 7 11 52 328 208 33 65 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 99 0 255 383), good := (rows 423 427 436 424 436 417 417 128 256) }] }

theorem u27 : Upper (D 3) (R 3) [6,9,48,320,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b27
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 129, camps := [], pairs := [(3,5)], upper := (rows 7 11 52 328 208 33 96 129 385), lower := (rows 7 11 52 328 208 33 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 72 80 0 64 163 291), good := (rows 391 395 404 344 216 385 472 128 256) }] }

theorem u28 : Upper (D 3) (R 3) [6,9,48,320,192,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b28
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 328 208 33 192 161 289), lower := (rows 7 11 52 328 208 33 192 128 256), losses := [] }

theorem u29 : Upper (D 3) (R 3) [6,9,48,320,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b29
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 273 33 192 224 352), lower := (rows 7 11 100 152 273 33 192 128 256), losses := [] }

theorem u30 : Upper (D 3) (R 3) [6,9,96,144,257,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b30
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 152 273 96 192 161 289), lower := (rows 7 11 100 152 273 96 192 128 256), losses := [] }

theorem u31 : Upper (D 3) (R 3) [6,9,96,144,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b31
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 65, camps := [], pairs := [(4,7)], upper := (rows 7 11 100 152 304 160 65 193 321), lower := (rows 7 11 100 152 304 160 65 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 20 32 67 0 323), good := (rows 343 331 372 24 304 32 321 0 256) }] }

theorem u32 : Upper (D 3) (R 3) [6,9,96,144,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b32
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 145 33 192 224 352), lower := (rows 7 11 100 280 145 33 192 128 256), losses := [] }

theorem u33 : Upper (D 3) (R 3) [6,9,96,272,129,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b33
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 280 145 96 192 161 289), lower := (rows 7 11 100 280 145 96 192 128 256), losses := [] }

theorem u34 : Upper (D 3) (R 3) [6,9,96,272,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b34
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 392 176 33 65 208 336), lower := (rows 7 11 100 392 176 33 65 128 256), losses := [] }

theorem u35 : Upper (D 3) (R 3) [6,9,96,384,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b35
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 11 100 392 176 33 80 193 321), lower := (rows 7 11 100 392 176 33 80 128 256), losses := [] }

theorem u36 : Upper (D 3) (R 3) [6,9,96,384,160,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b36
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 276 104 145 33 192 224 352), lower := (rows 7 11 276 104 145 33 192 128 256), losses := [] }

theorem u37 : Upper (D 3) (R 3) [6,9,272,96,129,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b37
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 276 104 145 96 192 161 289), lower := (rows 7 11 276 104 145 96 192 128 256), losses := [] }

theorem u38 : Upper (D 3) (R 3) [6,9,272,96,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b38
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 88 145 96 65 160 416), lower := (rows 7 11 292 88 145 96 65 128 256), losses := [] }

theorem u39 : Upper (D 3) (R 3) [6,9,288,80,129,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b39
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 292 88 145 96 96 129 385), lower := (rows 7 11 292 88 145 96 96 128 256), losses := [] }

theorem u40 : Upper (D 3) (R 3) [6,9,288,80,129,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b40
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 88 145 96 192 161 289), lower := (rows 7 11 292 88 145 96 192 128 256), losses := [] }

theorem u41 : Upper (D 3) (R 3) [6,9,288,80,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b41
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 88 145 160 65 224 352), lower := (rows 7 11 292 88 145 160 65 128 256), losses := [] }

theorem u42 : Upper (D 3) (R 3) [6,9,288,80,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b42
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 292 88 145 160 96 193 321), lower := (rows 7 11 292 88 145 160 96 128 256), losses := [] }

theorem u43 : Upper (D 3) (R 3) [6,9,288,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b43
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 129, camps := [], pairs := [(2,6)], upper := (rows 7 11 292 88 176 96 65 129 385), lower := (rows 7 11 292 88 176 96 65 128 256), losses := [{ target := 6, region := (rows 1 2 36 8 48 32 0 195 323), good := (rows 391 395 308 408 180 436 385 128 256) }] }

theorem u44 : Upper (D 3) (R 3) [6,9,288,80,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b44
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 88 176 96 192 129 257), lower := (rows 7 11 292 88 176 96 192 128 256), losses := [] }

theorem u45 : Upper (D 3) (R 3) [6,9,288,80,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b45
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 200 112 33 65 144 400), lower := (rows 7 11 292 200 112 33 65 128 256), losses := [] }

theorem u46 : Upper (D 3) (R 3) [6,9,288,192,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b46
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 11 292 200 112 33 80 129 385), lower := (rows 7 11 292 200 112 33 80 128 256), losses := [] }

theorem u47 : Upper (D 3) (R 3) [6,9,288,192,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b47
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 200 112 33 192 145 273), lower := (rows 7 11 292 200 112 33 192 128 256), losses := [] }

theorem u48 : Upper (D 3) (R 3) [6,9,288,192,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b48
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 402, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 37 73 273 160 96 192 448), lower := (rows 7 26 37 73 273 160 96 128 256), losses := [] }

theorem u49 : Upper (D 3) (R 3) [6,24,33,65,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b49
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 96, camps := [], pairs := [(3,5)], upper := (rows 7 26 37 73 273 160 192 224 352), lower := (rows 7 26 37 73 273 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 16 0 224 128 256), good := (rows 15 26 77 73 273 192 192 192 256) }] }

theorem u50 : Upper (D 3) (R 3) [6,24,33,65,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b50
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 273 33 192 224 352), lower := (rows 7 26 100 137 273 33 192 128 256), losses := [] }

theorem u51 : Upper (D 3) (R 3) [6,24,96,129,257,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b51
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 137 273 96 192 161 289), lower := (rows 7 26 100 137 273 96 192 128 256), losses := [] }

theorem u52 : Upper (D 3) (R 3) [6,24,96,129,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b52
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7)], upper := (rows 7 26 261 41 81 96 192 160 416), lower := (rows 7 26 261 41 81 96 192 128 256), losses := [] }

theorem u53 : Upper (D 3) (R 3) [6,24,257,33,65,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b53
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 96, camps := [], pairs := [(1,5)], upper := (rows 7 26 261 41 81 160 192 224 352), lower := (rows 7 26 261 41 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 24 0 224 128 256), good := (rows 7 26 261 91 81 192 192 192 256) }] }

theorem u54 : Upper (D 3) (R 3) [6,24,257,33,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b54
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 73 145 96 65 160 416), lower := (rows 7 26 292 73 145 96 65 128 256), losses := [] }

theorem u55 : Upper (D 3) (R 3) [6,24,288,65,129,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b55
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 146, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 73 145 96 96 129 385), lower := (rows 7 26 292 73 145 96 96 128 256), losses := [] }

theorem u56 : Upper (D 3) (R 3) [6,24,288,65,129,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b56
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 73 145 96 192 161 289), lower := (rows 7 26 292 73 145 96 192 128 256), losses := [] }

theorem u57 : Upper (D 3) (R 3) [6,24,288,65,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b57
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 69 56 336 160 65 136 392), lower := (rows 7 35 69 56 336 160 65 128 256), losses := [] }

theorem u58 : Upper (D 3) (R 3) [6,33,65,48,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b58
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 69 56 336 160 72 129 385), lower := (rows 7 35 69 56 336 160 72 128 256), losses := [] }

theorem u59 : Upper (D 3) (R 3) [6,33,65,48,320,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b59
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P03
