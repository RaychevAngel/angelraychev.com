import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 296 144 48 65 192 448), lower := (rows 23 11 100 296 144 48 65 128 256), losses := [] }

theorem u0 : Upper (D 0) (R 0) [22,9,96,288,128,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b0
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 296 144 48 192 193 321), lower := (rows 23 11 100 296 144 48 192 128 256), losses := [] }

theorem u1 : Upper (D 0) (R 0) [22,9,96,288,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 296 144 160 65 208 336), lower := (rows 23 11 100 296 144 160 65 128 256), losses := [] }

theorem u2 : Upper (D 0) (R 0) [22,9,96,288,128,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 296 144 160 80 193 321), lower := (rows 23 11 100 296 144 160 80 128 256), losses := [] }

theorem u3 : Upper (D 0) (R 0) [22,9,96,288,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 23 11 292 104 144 48 65 192 448), lower := (rows 23 11 292 104 144 48 65 128 256), losses := [] }

theorem u4 : Upper (D 0) (R 0) [22,9,288,96,128,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b4
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 23 11 292 104 144 48 192 193 321), lower := (rows 23 11 292 104 144 48 192 128 256), losses := [] }

theorem u5 : Upper (D 0) (R 0) [22,9,288,96,128,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b5
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 292 104 144 160 65 208 336), lower := (rows 23 11 292 104 144 160 65 128 256), losses := [] }

theorem u6 : Upper (D 0) (R 0) [22,9,288,96,128,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b6
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 23 11 292 104 144 160 80 193 321), lower := (rows 23 11 292 104 144 160 80 128 256), losses := [] }

theorem u7 : Upper (D 0) (R 0) [22,9,288,96,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b7
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 160, camps := [], pairs := [(1,0)], upper := (rows 23 42 196 328 17 33 80 160 416), lower := (rows 23 42 196 328 17 33 80 128 256), losses := [{ target := 0, region := (rows 0 34 37 41 16 32 81 162 290), good := (rows 478 430 196 328 92 494 80 128 256) }] }

theorem u8 : Upper (D 0) (R 0) [22,40,192,320,1,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b8
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 144, camps := [], pairs := [(1,0)], upper := (rows 23 42 196 328 17 33 96 144 400), lower := (rows 23 42 196 328 17 33 96 128 256), losses := [{ target := 0, region := (rows 0 98 37 41 16 32 98 145 273), good := (rows 478 110 198 330 412 494 110 128 256) }] }

theorem u9 : Upper (D 0) (R 0) [22,40,192,320,1,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b9
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7)], upper := (rows 23 42 196 328 17 33 192 176 304), lower := (rows 23 42 196 328 17 33 192 128 256), losses := [] }

theorem u10 : Upper (D 0) (R 0) [22,40,192,320,1,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b10
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 160, camps := [], pairs := [(1,0)], upper := (rows 23 42 196 328 17 48 65 160 416), lower := (rows 23 42 196 328 17 48 65 128 256), losses := [{ target := 0, region := (rows 0 67 76 76 16 49 64 243 371), good := (rows 446 430 462 462 434 432 494 128 256) }] }

theorem u11 : Upper (D 0) (R 0) [22,40,192,320,1,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b11
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 129, camps := [], pairs := [(1,4)], upper := (rows 23 42 196 328 17 48 96 129 385), lower := (rows 23 42 196 328 17 48 96 128 256), losses := [{ target := 4, region := (rows 1 98 37 41 0 32 98 145 273), good := (rows 463 110 198 330 397 494 110 128 256) }] }

theorem u12 : Upper (D 0) (R 0) [22,40,192,320,1,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b12
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7)], upper := (rows 23 42 196 328 17 48 192 161 289), lower := (rows 23 42 196 328 17 48 192 128 256), losses := [] }

theorem u13 : Upper (D 0) (R 0) [22,40,192,320,1,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b13
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 48, camps := [], pairs := [(1,0)], upper := (rows 23 42 196 328 17 160 65 176 304), lower := (rows 23 42 196 328 17 160 65 128 256), losses := [{ target := 0, region := (rows 0 78 68 72 16 245 64 145 273), good := (rows 438 42 238 366 432 160 494 160 256) }] }

theorem u14 : Upper (D 0) (R 0) [22,40,192,320,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b14
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 33, camps := [], pairs := [(1,4)], upper := (rows 23 42 196 328 17 160 80 161 289), lower := (rows 23 42 196 328 17 160 80 128 256), losses := [{ target := 4, region := (rows 1 78 68 72 0 245 64 145 273), good := (rows 423 42 238 366 417 160 494 160 256) }] }

theorem u15 : Upper (D 0) (R 0) [22,40,192,320,1,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b15
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 23 42 196 328 17 160 96 145 273), lower := (rows 23 42 196 328 17 160 96 128 256), losses := [] }

theorem u16 : Upper (D 0) (R 0) [22,40,192,320,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b16
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 160, camps := [], pairs := [(1,0)], upper := (rows 23 42 324 200 17 33 80 160 416), lower := (rows 23 42 324 200 17 33 80 128 256), losses := [{ target := 0, region := (rows 0 34 37 41 16 32 81 162 290), good := (rows 478 430 324 200 92 494 80 128 256) }] }

theorem u17 : Upper (D 0) (R 0) [22,40,320,192,1,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b17
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 144, camps := [], pairs := [(1,0)], upper := (rows 23 42 324 200 17 33 96 144 400), lower := (rows 23 42 324 200 17 33 96 128 256), losses := [{ target := 0, region := (rows 0 98 37 41 16 32 98 145 273), good := (rows 478 110 326 202 412 494 110 128 256) }] }

theorem u18 : Upper (D 0) (R 0) [22,40,320,192,1,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b18
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 23 42 324 200 17 33 192 176 304), lower := (rows 23 42 324 200 17 33 192 128 256), losses := [] }

theorem u19 : Upper (D 0) (R 0) [22,40,320,192,1,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b19
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 160, camps := [], pairs := [(1,0)], upper := (rows 23 42 324 200 17 48 65 160 416), lower := (rows 23 42 324 200 17 48 65 128 256), losses := [{ target := 0, region := (rows 0 67 76 76 16 49 64 243 371), good := (rows 446 430 462 462 434 432 494 128 256) }] }

theorem u20 : Upper (D 0) (R 0) [22,40,320,192,1,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b20
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 129, camps := [], pairs := [(1,4)], upper := (rows 23 42 324 200 17 48 96 129 385), lower := (rows 23 42 324 200 17 48 96 128 256), losses := [{ target := 4, region := (rows 1 98 37 41 0 32 98 145 273), good := (rows 463 110 326 202 397 494 110 128 256) }] }

theorem u21 : Upper (D 0) (R 0) [22,40,320,192,1,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b21
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 23 42 324 200 17 48 192 161 289), lower := (rows 23 42 324 200 17 48 192 128 256), losses := [] }

theorem u22 : Upper (D 0) (R 0) [22,40,320,192,1,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b22
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 23 98 388 168 17 48 65 200 328), lower := (rows 23 98 388 168 17 48 65 128 256), losses := [] }

theorem u23 : Upper (D 0) (R 0) [22,96,384,160,1,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b23
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 23 98 388 168 17 48 72 193 321), lower := (rows 23 98 388 168 17 48 72 128 256), losses := [] }

theorem u24 : Upper (D 0) (R 0) [22,96,384,160,1,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b24
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 88 144 96 65 160 416), lower := (rows 51 7 268 88 144 96 65 128 256), losses := [] }

theorem u25 : Upper (D 0) (R 0) [50,5,264,80,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b25
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 51 7 268 88 144 96 96 129 385), lower := (rows 51 7 268 88 144 96 96 128 256), losses := [] }

theorem u26 : Upper (D 0) (R 0) [50,5,264,80,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b26
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 268 88 144 96 192 161 289), lower := (rows 51 7 268 88 144 96 192 128 256), losses := [] }

theorem u27 : Upper (D 0) (R 0) [50,5,264,80,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b27
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 200 80 160 65 176 304), lower := (rows 51 7 268 200 80 160 65 128 256), losses := [] }

theorem u28 : Upper (D 0) (R 0) [50,5,264,192,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b28
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 51 7 268 200 80 160 80 161 289), lower := (rows 51 7 268 200 80 160 80 128 256), losses := [] }

theorem u29 : Upper (D 0) (R 0) [50,5,264,192,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b29
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 51 7 268 200 80 160 96 145 273), lower := (rows 51 7 268 200 80 160 96 128 256), losses := [] }

theorem u30 : Upper (D 0) (R 0) [50,5,264,192,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b30
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 152 80 160 65 164 292), lower := (rows 51 259 76 152 80 160 65 128 256), losses := [] }

theorem u31 : Upper (D 0) (R 0) [50,257,72,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b31
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 51 259 76 152 80 160 68 161 289), lower := (rows 51 259 76 152 80 160 68 128 256), losses := [] }

theorem u32 : Upper (D 0) (R 0) [50,257,72,144,64,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b32
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 92, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 152 80 160 96 133 261), lower := (rows 51 259 76 152 80 160 96 128 256), losses := [] }

theorem u33 : Upper (D 0) (R 0) [50,257,72,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b33
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 156, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 168 144 96 65 140 268), lower := (rows 51 259 84 168 144 96 65 128 256), losses := [] }

theorem u34 : Upper (D 0) (R 0) [50,257,80,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b34
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 51 259 84 168 144 96 68 137 265), lower := (rows 51 259 84 168 144 96 68 128 256), losses := [] }

theorem u35 : Upper (D 0) (R 0) [50,257,80,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b35
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 51 259 84 168 144 96 72 133 261), lower := (rows 51 259 84 168 144 96 72 128 256), losses := [] }

theorem u36 : Upper (D 0) (R 0) [50,257,80,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b36
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 51 322 13 200 17 160 68 176 304), lower := (rows 51 322 13 200 17 160 68 128 256), losses := [] }

theorem u37 : Upper (D 0) (R 0) [50,320,9,192,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b37
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 36, camps := [], pairs := [(1,0)], upper := (rows 51 322 13 200 17 160 80 164 292), lower := (rows 51 322 13 200 17 160 80 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 172 81 132 260), good := (rows 114 322 494 232 80 160 80 160 256) }] }

theorem u38 : Upper (D 0) (R 0) [50,320,9,192,1,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b38
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 51 322 13 200 17 160 96 148 276), lower := (rows 51 322 13 200 17 160 96 128 256), losses := [] }

theorem u39 : Upper (D 0) (R 0) [50,320,9,192,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b39
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 51 322 28 104 17 160 65 132 388), lower := (rows 51 322 28 104 17 160 65 128 256), losses := [] }

theorem u40 : Upper (D 0) (R 0) [50,320,24,96,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b40
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 51 322 28 104 17 160 68 129 385), lower := (rows 51 322 28 104 17 160 68 128 256), losses := [] }

theorem u41 : Upper (D 0) (R 0) [50,320,24,96,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b41
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 28 104 17 160 192 133 261), lower := (rows 51 322 28 104 17 160 192 128 256), losses := [] }

theorem u42 : Upper (D 0) (R 0) [50,320,24,96,1,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b42
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 28 104 144 33 65 132 388), lower := (rows 51 322 28 104 144 33 65 128 256), losses := [] }

theorem u43 : Upper (D 0) (R 0) [50,320,24,96,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b43
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 51 322 28 104 144 33 68 129 385), lower := (rows 51 322 28 104 144 33 68 128 256), losses := [] }

theorem u44 : Upper (D 0) (R 0) [50,320,24,96,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b44
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0)], upper := (rows 51 322 28 104 144 33 192 133 261), lower := (rows 51 322 28 104 144 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 13 9 208 32 208 128 256), good := (rows 126 338 92 124 208 44 208 208 256) }] }

theorem u45 : Upper (D 0) (R 0) [50,320,24,96,128,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b45
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 36, camps := [], pairs := [(1,0)], upper := (rows 51 322 28 200 17 160 65 164 292), lower := (rows 51 322 28 200 17 160 65 128 256), losses := [{ target := 0, region := (rows 0 74 5 74 16 255 64 213 341), good := (rows 446 490 446 490 436 160 494 160 256) }] }

theorem u46 : Upper (D 0) (R 0) [50,320,24,192,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b46
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 51 322 28 200 17 160 68 161 289), lower := (rows 51 322 28 200 17 160 68 128 256), losses := [] }

theorem u47 : Upper (D 0) (R 0) [50,320,24,192,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b47
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 51 322 28 200 17 160 96 133 261), lower := (rows 51 322 28 200 17 160 96 128 256), losses := [] }

theorem u48 : Upper (D 0) (R 0) [50,320,24,192,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b48
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 51 322 76 137 17 160 68 176 304), lower := (rows 51 322 76 137 17 160 68 128 256), losses := [] }

theorem u49 : Upper (D 0) (R 0) [50,320,72,129,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b49
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 76 137 17 160 80 164 292), lower := (rows 51 322 76 137 17 160 80 128 256), losses := [] }

theorem u50 : Upper (D 0) (R 0) [50,320,72,129,1,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b50
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 76 137 17 160 96 148 276), lower := (rows 51 322 76 137 17 160 96 128 256), losses := [] }

theorem u51 : Upper (D 0) (R 0) [50,320,72,129,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b51
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 76 152 17 160 65 164 292), lower := (rows 51 322 76 152 17 160 65 128 256), losses := [] }

theorem u52 : Upper (D 0) (R 0) [50,320,72,144,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b52
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 51 322 76 152 17 160 68 161 289), lower := (rows 51 322 76 152 17 160 68 128 256), losses := [] }

theorem u53 : Upper (D 0) (R 0) [50,320,72,144,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b53
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 76 152 17 160 96 133 261), lower := (rows 51 322 76 152 17 160 96 128 256), losses := [] }

theorem u54 : Upper (D 0) (R 0) [50,320,72,144,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b54
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 51 322 84 137 17 160 68 168 296), lower := (rows 51 322 84 137 17 160 68 128 256), losses := [] }

theorem u55 : Upper (D 0) (R 0) [50,320,80,129,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b55
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 51 322 84 137 17 160 72 164 292), lower := (rows 51 322 84 137 17 160 72 128 256), losses := [] }

theorem u56 : Upper (D 0) (R 0) [50,320,80,129,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b56
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 84 137 17 160 96 140 268), lower := (rows 51 322 84 137 17 160 96 128 256), losses := [] }

theorem u57 : Upper (D 0) (R 0) [50,320,80,129,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b57
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 51 322 84 137 144 33 68 168 296), lower := (rows 51 322 84 137 144 33 68 128 256), losses := [] }

theorem u58 : Upper (D 0) (R 0) [50,320,80,129,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b58
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 51 322 84 137 144 33 72 164 292), lower := (rows 51 322 84 137 144 33 72 128 256), losses := [] }

theorem u59 : Upper (D 0) (R 0) [50,320,80,129,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b59
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P00
