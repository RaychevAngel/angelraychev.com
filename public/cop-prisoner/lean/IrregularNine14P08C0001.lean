import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 324 104 152 160 80 161 289), lower := (rows 7 35 324 104 152 160 80 128 256), losses := [] }

theorem u60 : Upper (D 8) (R 8) [6,33,320,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b60 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 104 152 160 96 145 273), lower := (rows 7 35 324 104 152 160 96 128 256), losses := [] }

theorem u61 : Upper (D 8) (R 8) [6,33,320,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b61 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 160, camps := [], pairs := [(1,6)], upper := (rows 7 42 52 200 336 33 65 160 416), lower := (rows 7 42 52 200 336 33 65 128 256), losses := [{ target := 6, region := (rows 1 10 20 8 16 97 0 255 383), good := (rows 423 426 436 426 436 417 417 128 256) }] }

theorem u62 : Upper (D 8) (R 8) [6,40,48,192,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b62 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 129, camps := [], pairs := [(3,5)], upper := (rows 7 42 52 200 336 33 96 129 385), lower := (rows 7 42 52 200 336 33 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 72 80 0 64 161 289), good := (rows 391 394 404 216 344 385 472 128 256) }] }

theorem u63 : Upper (D 8) (R 8) [6,40,48,192,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b63 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 52 200 336 33 192 161 289), lower := (rows 7 42 52 200 336 33 192 128 256), losses := [] }

theorem u64 : Upper (D 8) (R 8) [6,40,48,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b64 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 304 96 65 160 416), lower := (rows 7 42 69 152 304 96 65 128 256), losses := [] }

theorem u65 : Upper (D 8) (R 8) [6,40,65,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b65 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 304 96 96 129 385), lower := (rows 7 42 69 152 304 96 96 128 256), losses := [] }

theorem u66 : Upper (D 8) (R 8) [6,40,65,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b66 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 304, targets := 128 }], pairs := [(4,7)], upper := (rows 7 42 69 152 304 96 192 161 289), lower := (rows 7 42 69 152 304 96 192 128 256), losses := [] }

theorem u67 : Upper (D 8) (R 8) [6,40,65,144,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b67 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 394, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 112 160 65 160 416), lower := (rows 7 42 69 280 112 160 65 128 256), losses := [] }

theorem u68 : Upper (D 8) (R 8) [6,40,65,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b68 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 280 112 160 96 129 385), lower := (rows 7 42 69 280 112 160 96 128 256), losses := [] }

theorem u69 : Upper (D 8) (R 8) [6,40,65,272,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b69 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 280 112 160 192 161 289), lower := (rows 7 42 69 280 112 160 192 128 256), losses := [] }

theorem u70 : Upper (D 8) (R 8) [6,40,65,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b70 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 176 96 65 160 416), lower := (rows 7 42 69 280 176 96 65 128 256), losses := [] }

theorem u71 : Upper (D 8) (R 8) [6,40,65,272,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b71 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 280 176 96 96 129 385), lower := (rows 7 42 69 280 176 96 96 128 256), losses := [] }

theorem u72 : Upper (D 8) (R 8) [6,40,65,272,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b72 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 69 280 176 96 192 161 289), lower := (rows 7 42 69 280 176 96 192 128 256), losses := [] }

theorem u73 : Upper (D 8) (R 8) [6,40,65,272,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b73 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 392 176 96 65 176 304), lower := (rows 7 42 69 392 176 96 65 128 256), losses := [] }

theorem u74 : Upper (D 8) (R 8) [6,40,65,384,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b74 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 69 392 176 96 80 161 289), lower := (rows 7 42 69 392 176 96 80 128 256), losses := [] }

theorem u75 : Upper (D 8) (R 8) [6,40,65,384,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b75 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 392 176 96 96 145 273), lower := (rows 7 42 69 392 176 96 96 128 256), losses := [] }

theorem u76 : Upper (D 8) (R 8) [6,40,65,384,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b76 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 84 137 304 96 65 160 416), lower := (rows 7 42 84 137 304 96 65 128 256), losses := [] }

theorem u77 : Upper (D 8) (R 8) [6,40,80,129,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b77 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 137 304 96 96 129 385), lower := (rows 7 42 84 137 304 96 96 128 256), losses := [] }

theorem u78 : Upper (D 8) (R 8) [6,40,80,129,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b78 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 137 304 96 192 161 289), lower := (rows 7 42 84 137 304 96 192 128 256), losses := [] }

theorem u79 : Upper (D 8) (R 8) [6,40,80,129,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b79 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 84 265 176 96 65 160 416), lower := (rows 7 42 84 265 176 96 65 128 256), losses := [] }

theorem u80 : Upper (D 8) (R 8) [6,40,80,257,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b80 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 84 265 176 96 96 129 385), lower := (rows 7 42 84 265 176 96 96 128 256), losses := [] }

theorem u81 : Upper (D 8) (R 8) [6,40,80,257,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b81 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 84 265 176 96 192 161 289), lower := (rows 7 42 84 265 176 96 192 128 256), losses := [] }

theorem u82 : Upper (D 8) (R 8) [6,40,80,257,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b82 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r83 : Route 9 := (fun mask => (mask,id))

def c83 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u83 : Upper (D 8) (R 8) [6,40,80,384,160,64,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,64,1] 13 (by decide) (choices 1) [1,32] r83 c83
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b84 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 392 176 96 96 129 257), lower := (rows 7 42 84 392 176 96 96 128 256), losses := [] }

theorem u84 : Upper (D 8) (R 8) [6,40,80,384,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b84 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 25 304 160 65 192 448), lower := (rows 7 42 100 25 304 160 65 128 256), losses := [] }

theorem u85 : Upper (D 8) (R 8) [6,40,96,17,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b85 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 25 304 160 192 193 321), lower := (rows 7 42 100 25 304 160 192 128 256), losses := [] }

theorem u86 : Upper (D 8) (R 8) [6,40,96,17,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b86 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 152 336 33 65 160 416), lower := (rows 7 42 100 152 336 33 65 128 256), losses := [] }

theorem u87 : Upper (D 8) (R 8) [6,40,96,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b87 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 336 33 96 129 385), lower := (rows 7 42 100 152 336 33 96 128 256), losses := [] }

theorem u88 : Upper (D 8) (R 8) [6,40,96,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b88 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0)], upper := (rows 7 42 100 152 336 33 192 161 289), lower := (rows 7 42 100 152 336 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 200 128 256), good := (rows 6 110 100 216 336 32 192 192 256) }] }

theorem u89 : Upper (D 8) (R 8) [6,40,96,144,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b89 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 280 208 33 65 160 416), lower := (rows 7 42 100 280 208 33 65 128 256), losses := [] }

theorem u90 : Upper (D 8) (R 8) [6,40,96,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b90 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 280 208 33 96 129 385), lower := (rows 7 42 100 280 208 33 96 128 256), losses := [] }

theorem u91 : Upper (D 8) (R 8) [6,40,96,272,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b91 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 280 208 33 192 161 289), lower := (rows 7 42 100 280 208 33 192 128 256), losses := [] }

theorem u92 : Upper (D 8) (R 8) [6,40,96,272,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b92 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 392 176 33 65 208 336), lower := (rows 7 42 100 392 176 33 65 128 256), losses := [] }

theorem u93 : Upper (D 8) (R 8) [6,40,96,384,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b93 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 42 100 392 176 33 80 193 321), lower := (rows 7 42 100 392 176 33 80 128 256), losses := [] }

theorem u94 : Upper (D 8) (R 8) [6,40,96,384,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b94 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 392 208 33 65 176 304), lower := (rows 7 42 100 392 208 33 65 128 256), losses := [] }

theorem u95 : Upper (D 8) (R 8) [6,40,96,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b95 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 100 392 208 33 80 161 289), lower := (rows 7 42 100 392 208 33 80 128 256), losses := [] }

theorem u96 : Upper (D 8) (R 8) [6,40,96,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b96 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 392 208 33 96 145 273), lower := (rows 7 42 100 392 208 33 96 128 256), losses := [] }

theorem u97 : Upper (D 8) (R 8) [6,40,96,384,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b97 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 25 304 96 65 160 416), lower := (rows 7 42 196 25 304 96 65 128 256), losses := [] }

theorem u98 : Upper (D 8) (R 8) [6,40,192,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b98 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 25 304 96 96 129 385), lower := (rows 7 42 196 25 304 96 96 128 256), losses := [] }

theorem u99 : Upper (D 8) (R 8) [6,40,192,17,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b99 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 196 25 304 96 192 161 289), lower := (rows 7 42 196 25 304 96 192 128 256), losses := [] }

theorem u100 : Upper (D 8) (R 8) [6,40,192,17,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 25 112 160 65 192 448), lower := (rows 7 42 292 25 112 160 65 128 256), losses := [] }

theorem u101 : Upper (D 8) (R 8) [6,40,288,17,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 25 112 160 192 193 321), lower := (rows 7 42 292 25 112 160 192 128 256), losses := [] }

theorem u102 : Upper (D 8) (R 8) [6,40,288,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 73 112 160 65 144 400), lower := (rows 7 42 292 73 112 160 65 128 256), losses := [] }

theorem u103 : Upper (D 8) (R 8) [6,40,288,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 292 73 112 160 80 129 385), lower := (rows 7 42 292 73 112 160 80 128 256), losses := [] }

theorem u104 : Upper (D 8) (R 8) [6,40,288,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b104 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 73 112 160 192 145 273), lower := (rows 7 42 292 73 112 160 192 128 256), losses := [] }

theorem u105 : Upper (D 8) (R 8) [6,40,288,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 73 208 160 65 176 304), lower := (rows 7 42 292 73 208 160 65 128 256), losses := [] }

theorem u106 : Upper (D 8) (R 8) [6,40,288,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 292 73 208 160 80 161 289), lower := (rows 7 42 292 73 208 160 80 128 256), losses := [] }

theorem u107 : Upper (D 8) (R 8) [6,40,288,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b107 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 73 208 160 96 145 273), lower := (rows 7 42 292 73 208 160 96 128 256), losses := [] }

theorem u108 : Upper (D 8) (R 8) [6,40,288,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 138, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 292 200 112 33 65 144 400), lower := (rows 7 42 292 200 112 33 65 128 256), losses := [] }

theorem u109 : Upper (D 8) (R 8) [6,40,288,192,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 292 200 112 33 80 129 385), lower := (rows 7 42 292 200 112 33 80 128 256), losses := [] }

theorem u110 : Upper (D 8) (R 8) [6,40,288,192,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b110 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 200 112 33 192 145 273), lower := (rows 7 42 292 200 112 33 192 128 256), losses := [] }

theorem u111 : Upper (D 8) (R 8) [6,40,288,192,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 324 25 176 96 65 160 416), lower := (rows 7 42 324 25 176 96 65 128 256), losses := [] }

theorem u112 : Upper (D 8) (R 8) [6,40,320,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 25 176 96 96 129 385), lower := (rows 7 42 324 25 176 96 96 128 256), losses := [] }

theorem u113 : Upper (D 8) (R 8) [6,40,320,17,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 324 25 176 96 192 161 289), lower := (rows 7 42 324 25 176 96 192 128 256), losses := [] }

theorem u114 : Upper (D 8) (R 8) [6,40,320,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 324 137 176 96 65 176 304), lower := (rows 7 42 324 137 176 96 65 128 256), losses := [] }

theorem u115 : Upper (D 8) (R 8) [6,40,320,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 324 137 176 96 80 161 289), lower := (rows 7 42 324 137 176 96 80 128 256), losses := [] }

theorem u116 : Upper (D 8) (R 8) [6,40,320,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b116 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 137 176 96 96 145 273), lower := (rows 7 42 324 137 176 96 96 128 256), losses := [] }

theorem u117 : Upper (D 8) (R 8) [6,40,320,129,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 56 336 160 65 160 288), lower := (rows 7 67 140 56 336 160 65 128 256), losses := [] }

theorem u118 : Upper (D 8) (R 8) [6,65,136,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 33, camps := [], pairs := [(0,7)], upper := (rows 7 67 140 56 336 160 96 161 289), lower := (rows 7 67 140 56 336 160 96 128 256), losses := [{ target := 7, region := (rows 5 6 4 8 16 32 104 0 256), good := (rows 7 67 79 120 336 96 96 0 256) }] }

theorem u119 : Upper (D 8) (R 8) [6,65,136,48,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P08
