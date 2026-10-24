import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0088

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19440 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 368, targets := 128 }], pairs := [(3,1),(4,1),(4,7)], upper := (rows 35 70 134 137 280 48 97 225 353), lower := (rows 35 70 134 137 280 48 64 128 256), losses := [] }

theorem u19440 : Upper (D 7) (R 7) [34,68,130,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19440 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19441 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 137 280 96 113 177 305), lower := (rows 35 70 134 137 280 96 64 128 256), losses := [] }

theorem u19441 : Upper (D 7) (R 7) [34,68,130,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19442 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 137 304 33 88 216 344), lower := (rows 35 70 134 137 304 33 64 128 256), losses := [] }

theorem u19442 : Upper (D 7) (R 7) [34,68,130,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19443 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 134 137 304 40 81 209 337), lower := (rows 35 70 134 137 304 40 64 128 256), losses := [] }

theorem u19443 : Upper (D 7) (R 7) [34,68,130,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19443 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19444 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 134 137 304 48 73 201 329), lower := (rows 35 70 134 137 304 48 64 128 256), losses := [] }

theorem u19444 : Upper (D 7) (R 7) [34,68,130,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19444 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19445 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 137 304 96 89 153 281), lower := (rows 35 70 134 137 304 96 64 128 256), losses := [] }

theorem u19445 : Upper (D 7) (R 7) [34,68,130,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19446 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 137 336 33 120 184 312), lower := (rows 35 70 134 137 336 33 64 128 256), losses := [] }

theorem u19446 : Upper (D 7) (R 7) [34,68,130,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19447 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 134 137 336 40 113 177 305), lower := (rows 35 70 134 137 336 40 64 128 256), losses := [] }

theorem u19447 : Upper (D 7) (R 7) [34,68,130,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19447 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19448 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 137 336 48 105 169 297), lower := (rows 35 70 134 137 336 48 64 128 256), losses := [] }

theorem u19448 : Upper (D 7) (R 7) [34,68,130,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19448 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19449 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 152 273 33 104 232 360), lower := (rows 35 70 134 152 273 33 64 128 256), losses := [] }

theorem u19449 : Upper (D 7) (R 7) [34,68,130,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19450 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(3,1),(4,1),(4,7)], upper := (rows 35 70 134 152 273 40 97 225 353), lower := (rows 35 70 134 152 273 40 64 128 256), losses := [] }

theorem u19450 : Upper (D 7) (R 7) [34,68,130,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19450 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19451 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 152 273 96 105 169 297), lower := (rows 35 70 134 152 273 96 64 128 256), losses := [] }

theorem u19451 : Upper (D 7) (R 7) [34,68,130,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19452 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 152 304 33 73 201 329), lower := (rows 35 70 134 152 304 33 64 128 256), losses := [] }

theorem u19452 : Upper (D 7) (R 7) [34,68,130,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19453 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 152 304 40 65 193 321), lower := (rows 35 70 134 152 304 40 64 128 256), losses := [] }

theorem u19453 : Upper (D 7) (R 7) [34,68,130,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19453 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19454 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 152 304 96 73 137 265), lower := (rows 35 70 134 152 304 96 64 128 256), losses := [] }

theorem u19454 : Upper (D 7) (R 7) [34,68,130,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19455 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 152 336 33 105 169 297), lower := (rows 35 70 134 152 336 33 64 128 256), losses := [] }

theorem u19455 : Upper (D 7) (R 7) [34,68,130,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19456 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 152 336 40 97 161 289), lower := (rows 35 70 134 152 336 40 64 128 256), losses := [] }

theorem u19456 : Upper (D 7) (R 7) [34,68,130,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19456 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19457 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 168 273 33 88 216 344), lower := (rows 35 70 134 168 273 33 64 128 256), losses := [] }

theorem u19457 : Upper (D 7) (R 7) [34,68,130,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19458 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 168 273 40 81 209 337), lower := (rows 35 70 134 168 273 40 64 128 256), losses := [] }

theorem u19458 : Upper (D 7) (R 7) [34,68,130,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19458 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19459 : Route 9 := (fun mask => (mask,id))

def c19459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19459 : Upper (D 7) (R 7) [34,68,130,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,160,257,16] 13 (by decide) (choices 1) [1,8] r19459 c19459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5307
  · exact u5308

def b19460 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 168 273 96 89 153 281), lower := (rows 35 70 134 168 273 96 64 128 256), losses := [] }

theorem u19460 : Upper (D 7) (R 7) [34,68,130,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19461 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 168 280 33 81 209 337), lower := (rows 35 70 134 168 280 33 64 128 256), losses := [] }

theorem u19461 : Upper (D 7) (R 7) [34,68,130,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19462 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 168 280 48 65 193 321), lower := (rows 35 70 134 168 280 48 64 128 256), losses := [] }

theorem u19462 : Upper (D 7) (R 7) [34,68,130,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19462 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19463 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 168 280 96 81 145 273), lower := (rows 35 70 134 168 280 96 64 128 256), losses := [] }

theorem u19463 : Upper (D 7) (R 7) [34,68,130,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19464 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 168 336 33 89 153 281), lower := (rows 35 70 134 168 336 33 64 128 256), losses := [] }

theorem u19464 : Upper (D 7) (R 7) [34,68,130,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19465 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 168 336 40 81 145 273), lower := (rows 35 70 134 168 336 40 64 128 256), losses := [] }

theorem u19465 : Upper (D 7) (R 7) [34,68,130,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19465 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19466 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 168 336 48 73 137 265), lower := (rows 35 70 134 168 336 48 64 128 256), losses := [] }

theorem u19466 : Upper (D 7) (R 7) [34,68,130,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19466 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19467 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 140 25 274 33 224 224 480), lower := (rows 35 70 140 25 274 33 64 128 256), losses := [] }

theorem u19467 : Upper (D 7) (R 7) [34,68,136,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19468 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 274 96 225 161 417), lower := (rows 35 70 140 25 274 96 64 128 256), losses := [] }

theorem u19468 : Upper (D 7) (R 7) [34,68,136,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19469 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 228, targets := 2 }], pairs := [(0,6),(2,1),(3,7),(4,7)], upper := (rows 35 70 140 25 274 160 97 225 353), lower := (rows 35 70 140 25 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 24 16 164 0 128 256), good := (rows 35 39 172 25 283 160 0 160 256) }] }

theorem u19469 : Upper (D 7) (R 7) [34,68,136,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19470 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 25 304 33 194 194 450), lower := (rows 35 70 140 25 304 33 64 128 256), losses := [] }

theorem u19470 : Upper (D 7) (R 7) [34,68,136,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19471 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 25 304 34 193 193 449), lower := (rows 35 70 140 25 304 34 64 128 256), losses := [] }

theorem u19471 : Upper (D 7) (R 7) [34,68,136,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19472 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 304 96 195 131 387), lower := (rows 35 70 140 25 304 96 64 128 256), losses := [] }

theorem u19472 : Upper (D 7) (R 7) [34,68,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19473 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 140 25 304 160 67 195 323), lower := (rows 35 70 140 25 304 160 64 128 256), losses := [] }

theorem u19473 : Upper (D 7) (R 7) [34,68,136,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19474 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 70 140 25 336 33 226 162 418), lower := (rows 35 70 140 25 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 65 129 257), good := (rows 498 70 158 478 336 496 64 128 256) }] }

theorem u19474 : Upper (D 7) (R 7) [34,68,136,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19475 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 25 336 34 225 161 417), lower := (rows 35 70 140 25 336 34 64 128 256), losses := [] }

theorem u19475 : Upper (D 7) (R 7) [34,68,136,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19476 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 140 25 336 160 99 163 291), lower := (rows 35 70 140 25 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 175 0 131 259), good := (rows 419 423 172 445 272 160 0 160 256) }] }

theorem u19476 : Upper (D 7) (R 7) [34,68,136,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19477 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,0)], upper := (rows 35 70 140 25 400 33 98 226 354), lower := (rows 35 70 140 25 400 33 64 128 256), losses := [] }

theorem u19477 : Upper (D 7) (R 7) [34,68,136,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19478 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 25 400 34 97 225 353), lower := (rows 35 70 140 25 400 34 64 128 256), losses := [] }

theorem u19478 : Upper (D 7) (R 7) [34,68,136,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19479 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 400 96 99 163 291), lower := (rows 35 70 140 25 400 96 64 128 256), losses := [] }

theorem u19479 : Upper (D 7) (R 7) [34,68,136,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19480 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,7)], upper := (rows 35 70 140 26 112 33 449 385 385), lower := (rows 35 70 140 26 112 33 64 128 256), losses := [] }

theorem u19480 : Upper (D 7) (R 7) [34,68,136,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19481 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 140 26 112 160 321 385 257), lower := (rows 35 70 140 26 112 160 64 128 256), losses := [] }

theorem u19481 : Upper (D 7) (R 7) [34,68,136,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19482 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 35 70 140 26 112 288 193 129 385), lower := (rows 35 70 140 26 112 288 64 128 256), losses := [] }

theorem u19482 : Upper (D 7) (R 7) [34,68,136,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19482 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19483 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 140 26 176 33 321 449 321), lower := (rows 35 70 140 26 176 33 64 128 256), losses := [] }

theorem u19483 : Upper (D 7) (R 7) [34,68,136,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19484 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 176 96 321 385 257), lower := (rows 35 70 140 26 176 96 64 128 256), losses := [] }

theorem u19484 : Upper (D 7) (R 7) [34,68,136,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19485 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(1,7),(4,1)], upper := (rows 35 70 140 26 176 288 65 193 321), lower := (rows 35 70 140 26 176 288 64 128 256), losses := [] }

theorem u19485 : Upper (D 7) (R 7) [34,68,136,18,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19485 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19486 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(0,7),(1,0),(4,1)], upper := (rows 35 70 140 26 273 33 224 224 480), lower := (rows 35 70 140 26 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 97 161 289), good := (rows 482 70 140 30 478 480 64 128 256) }] }

theorem u19486 : Upper (D 7) (R 7) [34,68,136,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19487 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 140 26 273 96 225 161 417), lower := (rows 35 70 140 26 273 96 64 128 256), losses := [] }

theorem u19487 : Upper (D 7) (R 7) [34,68,136,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19488 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 2 }], pairs := [(2,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 140 26 273 160 97 225 353), lower := (rows 35 70 140 26 273 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 189 81 145 273), good := (rows 497 100 172 508 497 160 64 160 256) }] }

theorem u19488 : Upper (D 7) (R 7) [34,68,136,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19489 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(0,7),(1,5),(4,1)], upper := (rows 35 70 140 26 304 33 193 193 449), lower := (rows 35 70 140 26 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 20 24 16 0 97 161 289), good := (rows 451 70 140 30 478 449 64 128 256) }] }

theorem u19489 : Upper (D 7) (R 7) [34,68,136,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19490 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 140 26 304 96 193 129 385), lower := (rows 35 70 140 26 304 96 64 128 256), losses := [] }

theorem u19490 : Upper (D 7) (R 7) [34,68,136,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19491 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 2 }], pairs := [(0,6),(3,7),(4,1),(4,7)], upper := (rows 35 70 140 26 304 160 65 193 321), lower := (rows 35 70 140 26 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 27 304 160 0 160 256) }] }

theorem u19491 : Upper (D 7) (R 7) [34,68,136,18,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19492 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,1)], upper := (rows 35 70 140 26 336 33 225 161 417), lower := (rows 35 70 140 26 336 33 64 128 256), losses := [] }

theorem u19492 : Upper (D 7) (R 7) [34,68,136,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19493 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 140 26 336 160 97 161 289), lower := (rows 35 70 140 26 336 160 64 128 256), losses := [] }

theorem u19493 : Upper (D 7) (R 7) [34,68,136,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19494 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 140 26 400 33 97 225 353), lower := (rows 35 70 140 26 400 33 64 128 256), losses := [] }

theorem u19494 : Upper (D 7) (R 7) [34,68,136,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19495 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 400 96 97 161 289), lower := (rows 35 70 140 26 400 96 64 128 256), losses := [] }

theorem u19495 : Upper (D 7) (R 7) [34,68,136,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19496 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 56 273 33 194 194 450), lower := (rows 35 70 140 56 273 33 64 128 256), losses := [] }

theorem u19496 : Upper (D 7) (R 7) [34,68,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19497 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 56 273 34 193 193 449), lower := (rows 35 70 140 56 273 34 64 128 256), losses := [] }

theorem u19497 : Upper (D 7) (R 7) [34,68,136,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19498 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 140 56 273 96 195 131 387), lower := (rows 35 70 140 56 273 96 64 128 256), losses := [] }

theorem u19498 : Upper (D 7) (R 7) [34,68,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19499 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 56 273 160 67 195 323), lower := (rows 35 70 140 56 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 56 273 160 0 160 256) }] }

theorem u19499 : Upper (D 7) (R 7) [34,68,136,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19499
end Delivery.IrregularNine14.P07
