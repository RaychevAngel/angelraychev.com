import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0022

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 336 33 464 400 400), lower := (rows 35 70 44 137 336 33 64 128 256), losses := [] }

theorem u4440 : Upper (D 9) (R 9) [34,68,40,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4440 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4441 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 44 137 336 48 449 385 385), lower := (rows 35 70 44 137 336 48 64 128 256), losses := [] }

theorem u4441 : Upper (D 9) (R 9) [34,68,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4441 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4442 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 70 44 137 336 160 337 401 273), lower := (rows 35 70 44 137 336 160 64 128 256), losses := [] }

theorem u4442 : Upper (D 9) (R 9) [34,68,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4442 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4443 : Route 9 := (fun mask => (mask,id))

def c4443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4443 : Upper (D 9) (R 9) [34,68,40,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320,256] 13 (by decide) (choices 1) [1,16,128] r4443 c4443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1343
  · exact u1344
  · exact u1345

def b4444 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 400 33 336 464 336), lower := (rows 35 70 44 137 400 33 64 128 256), losses := [] }

theorem u4444 : Upper (D 9) (R 9) [34,68,40,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4444 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 137 400 48 321 449 321), lower := (rows 35 70 44 137 400 48 64 128 256), losses := [] }

theorem u4445 : Upper (D 9) (R 9) [34,68,40,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4445 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4446 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 44 137 400 96 337 401 273), lower := (rows 35 70 44 137 400 96 64 128 256), losses := [] }

theorem u4446 : Upper (D 9) (R 9) [34,68,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4446 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4447 : Route 9 := (fun mask => (mask,id))

def c4447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4447 : Upper (D 9) (R 9) [34,68,40,129,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,384,256] 13 (by decide) (choices 1) [1,16] r4447 c4447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1346
  · exact u1347

def b4448 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 44 152 273 33 448 448 448), lower := (rows 35 70 44 152 273 33 64 128 256), losses := [] }

theorem u4448 : Upper (D 9) (R 9) [34,68,40,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 44 152 273 96 449 385 385), lower := (rows 35 70 44 152 273 96 64 128 256), losses := [] }

theorem u4449 : Upper (D 9) (R 9) [34,68,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4449 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 70 44 152 273 160 321 449 321), lower := (rows 35 70 44 152 273 160 64 128 256), losses := [] }

theorem u4450 : Upper (D 9) (R 9) [34,68,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4450 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4451 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 195, targets := 256 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 44 152 273 288 193 193 449), lower := (rows 35 70 44 152 273 288 64 128 256), losses := [] }

theorem u4451 : Upper (D 9) (R 9) [34,68,40,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4451 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4452 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 44 152 336 33 449 385 385), lower := (rows 35 70 44 152 336 33 64 128 256), losses := [] }

theorem u4452 : Upper (D 9) (R 9) [34,68,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4453 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 70 44 152 336 160 321 385 257), lower := (rows 35 70 44 152 336 160 64 128 256), losses := [] }

theorem u4453 : Upper (D 9) (R 9) [34,68,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4453 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4454 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 195, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(3,5),(4,5)], upper := (rows 35 70 44 152 336 288 193 129 385), lower := (rows 35 70 44 152 336 288 64 128 256), losses := [] }

theorem u4454 : Upper (D 9) (R 9) [34,68,40,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4454 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 44 200 145 33 336 400 272), lower := (rows 35 70 44 200 145 33 64 128 256), losses := [] }

theorem u4455 : Upper (D 9) (R 9) [34,68,40,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4455 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4456 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 44 200 145 48 321 385 257), lower := (rows 35 70 44 200 145 48 64 128 256), losses := [] }

theorem u4456 : Upper (D 9) (R 9) [34,68,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4456 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4457 : Route 9 := (fun mask => (mask,id))

def c4457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4457 : Upper (D 9) (R 9) [34,68,40,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,129,256] 13 (by decide) (choices 1) [1,16,256] r4457 c4457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1348
  · exact u1349
  · exact u1350

def b4458 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 44 200 273 33 464 400 400), lower := (rows 35 70 44 200 273 33 64 128 256), losses := [] }

theorem u4458 : Upper (D 9) (R 9) [34,68,40,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4458 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 200 273 48 449 385 385), lower := (rows 35 70 44 200 273 48 64 128 256), losses := [] }

theorem u4459 : Upper (D 9) (R 9) [34,68,40,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4459 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4460 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 39, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 70 44 200 273 160 337 401 273), lower := (rows 35 70 44 200 273 160 64 128 256), losses := [] }

theorem u4460 : Upper (D 9) (R 9) [34,68,40,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4461 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,6),(3,5),(3,8),(4,5),(4,6)], upper := (rows 35 70 44 200 273 288 209 145 401), lower := (rows 35 70 44 200 273 288 64 128 256), losses := [] }

theorem u4461 : Upper (D 9) (R 9) [34,68,40,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4461 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4462 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 44 200 400 33 337 401 273), lower := (rows 35 70 44 200 400 33 64 128 256), losses := [] }

theorem u4462 : Upper (D 9) (R 9) [34,68,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4462 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4463 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 200 400 48 321 385 257), lower := (rows 35 70 44 200 400 48 64 128 256), losses := [] }

theorem u4463 : Upper (D 9) (R 9) [34,68,40,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4463 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4464 : Route 9 := (fun mask => (mask,id))

def c4464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4464 : Upper (D 9) (R 9) [34,68,40,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,384,256] 13 (by decide) (choices 1) [1,16] r4464 c4464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1351
  · exact u1352

def b4465 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(3,5),(4,7),(4,8)], upper := (rows 35 70 44 392 81 33 464 400 400), lower := (rows 35 70 44 392 81 33 64 128 256), losses := [] }

theorem u4465 : Upper (D 9) (R 9) [34,68,40,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 44 392 81 48 449 385 385), lower := (rows 35 70 44 392 81 48 64 128 256), losses := [] }

theorem u4466 : Upper (D 9) (R 9) [34,68,40,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4466 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 70 44 392 81 160 337 401 273), lower := (rows 35 70 44 392 81 160 64 128 256), losses := [] }

theorem u4467 : Upper (D 9) (R 9) [34,68,40,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4467 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 44 392 145 33 336 464 336), lower := (rows 35 70 44 392 145 33 64 128 256), losses := [] }

theorem u4468 : Upper (D 9) (R 9) [34,68,40,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4468 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 392 145 48 321 449 321), lower := (rows 35 70 44 392 145 48 64 128 256), losses := [] }

theorem u4469 : Upper (D 9) (R 9) [34,68,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4469 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 44 392 145 96 337 401 273), lower := (rows 35 70 44 392 145 96 64 128 256), losses := [] }

theorem u4470 : Upper (D 9) (R 9) [34,68,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4470 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4471 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 70 44 392 145 288 81 209 337), lower := (rows 35 70 44 392 145 288 64 128 256), losses := [] }

theorem u4471 : Upper (D 9) (R 9) [34,68,40,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4471 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4472 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 44 392 208 33 337 401 273), lower := (rows 35 70 44 392 208 33 64 128 256), losses := [] }

theorem u4472 : Upper (D 9) (R 9) [34,68,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4472 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 44 392 208 48 321 385 257), lower := (rows 35 70 44 392 208 48 64 128 256), losses := [] }

theorem u4473 : Upper (D 9) (R 9) [34,68,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4473 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 70 44 392 208 288 81 145 273), lower := (rows 35 70 44 392 208 288 64 128 256), losses := [] }

theorem u4474 : Upper (D 9) (R 9) [34,68,40,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4474 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4475 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,7),(4,7)], upper := (rows 35 70 133 25 88 160 352 416 288), lower := (rows 35 70 133 25 88 160 64 128 256), losses := [] }

theorem u4475 : Upper (D 9) (R 9) [34,68,129,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4475 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4476 : Route 9 := (fun mask => (mask,id))

def c4476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4476 : Upper (D 9) (R 9) [34,68,129,17,72,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,72,256] 13 (by decide) (choices 1) [32,128,256] r4476 c4476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1353
  · exact u1354
  · exact u1355

def b4477 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 25 112 40 448 384 384), lower := (rows 35 70 133 25 112 40 64 128 256), losses := [] }

theorem u4477 : Upper (D 9) (R 9) [34,68,129,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4477 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 496, targets := 1 }], pairs := [(1,5),(2,5),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 25 112 160 328 392 264), lower := (rows 35 70 133 25 112 160 64 128 256), losses := [] }

theorem u4478 : Upper (D 9) (R 9) [34,68,129,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4479 : Route 9 := (fun mask => (mask,id))

def c4479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4479 : Upper (D 9) (R 9) [34,68,129,17,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,96,256] 13 (by decide) (choices 1) [8,128,256] r4479 c4479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1356
  · exact u1357
  · exact u1358

def b4480 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 56, targets := 320 }], pairs := [(3,6),(3,8),(4,6),(4,8)], upper := (rows 35 70 133 25 176 40 320 448 320), lower := (rows 35 70 133 25 176 40 64 128 256), losses := [] }

theorem u4480 : Upper (D 9) (R 9) [34,68,129,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4480 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4481 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 176 96 328 392 264), lower := (rows 35 70 133 25 176 96 64 128 256), losses := [] }

theorem u4481 : Upper (D 9) (R 9) [34,68,129,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4481 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4482 : Route 9 := (fun mask => (mask,id))

def c4482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4482 : Upper (D 9) (R 9) [34,68,129,17,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,160,256] 13 (by decide) (choices 1) [8,256] r4482 c4482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1359
  · exact u1360

def b4483 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 25 208 40 352 416 288), lower := (rows 35 70 133 25 208 40 64 128 256), losses := [] }

theorem u4483 : Upper (D 9) (R 9) [34,68,129,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4483 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4484 : Route 9 := (fun mask => (mask,id))

def c4484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4484 : Upper (D 9) (R 9) [34,68,129,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,192,256] 13 (by decide) (choices 1) [8,32,256] r4484 c4484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1361
  · exact u1362
  · exact u1363

def b4485 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 280 96 480 416 416), lower := (rows 35 70 133 25 280 96 64 128 256), losses := [] }

theorem u4485 : Upper (D 9) (R 9) [34,68,129,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4485 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4486 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 2, region := 354, targets := 1 },{ cop := 3, region := 496, targets := 1 }], pairs := [(0,6),(1,0),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 25 280 160 352 480 352), lower := (rows 35 70 133 25 280 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 25 280 160 0 160 256) }] }

theorem u4486 : Upper (D 9) (R 9) [34,68,129,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4486 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4487 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 354, targets := 1 },{ cop := 3, region := 496, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(4,0)], upper := (rows 35 70 133 25 280 288 224 224 480), lower := (rows 35 70 133 25 280 288 64 128 256), losses := [] }

theorem u4487 : Upper (D 9) (R 9) [34,68,129,17,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4487 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4488 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 464, targets := 1 },{ cop := 2, region := 322, targets := 1 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 35 70 133 25 304 40 448 448 448), lower := (rows 35 70 133 25 304 40 64 128 256), losses := [] }

theorem u4488 : Upper (D 9) (R 9) [34,68,129,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4488 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4489 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 304 96 456 392 392), lower := (rows 35 70 133 25 304 96 64 128 256), losses := [] }

theorem u4489 : Upper (D 9) (R 9) [34,68,129,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4489 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4490 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 496, targets := 1 }], pairs := [(1,5),(2,5),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 25 304 160 328 456 328), lower := (rows 35 70 133 25 304 160 64 128 256), losses := [] }

theorem u4490 : Upper (D 9) (R 9) [34,68,129,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4491 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 133 25 304 288 200 200 456), lower := (rows 35 70 133 25 304 288 64 128 256), losses := [] }

theorem u4491 : Upper (D 9) (R 9) [34,68,129,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4492 : Route 9 := (fun mask => (mask,id))

def c4492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4492 : Upper (D 9) (R 9) [34,68,129,17,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,320,8] 13 (by decide) (choices 1) [32,128,256] r4492 c4492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1364
  · exact u1365
  · exact u1366

def b4493 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 496, targets := 1 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 25 336 160 360 424 296), lower := (rows 35 70 133 25 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 172 0 136 264), good := (rows 35 39 165 445 272 160 0 160 256) }] }

theorem u4493 : Upper (D 9) (R 9) [34,68,129,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4493 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4494 : Route 9 := (fun mask => (mask,id))

def c4494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4494 : Upper (D 9) (R 9) [34,68,129,17,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,320,256] 13 (by decide) (choices 1) [8,32,128] r4494 c4494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1367
  · exact u1368
  · exact u1369

def r4495 : Route 9 := (fun mask => (mask,id))

def c4495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4495 : Upper (D 9) (R 9) [34,68,129,17,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384,8] 13 (by decide) (choices 1) [32,256] r4495 c4495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1370
  · exact u1371

def b4496 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 400 96 360 424 296), lower := (rows 35 70 133 25 400 96 64 128 256), losses := [] }

theorem u4496 : Upper (D 9) (R 9) [34,68,129,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4496 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4497 : Route 9 := (fun mask => (mask,id))

def c4497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4497 : Upper (D 9) (R 9) [34,68,129,17,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384,256] 13 (by decide) (choices 1) [8,32] r4497 c4497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1372
  · exact u1373

def b4498 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 56 81 40 448 384 384), lower := (rows 35 70 133 56 81 40 64 128 256), losses := [] }

theorem u4498 : Upper (D 9) (R 9) [34,68,129,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4498 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4499 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 428, targets := 64 },{ cop := 4, region := 424, targets := 1 }], pairs := [(2,6),(3,0),(3,6),(3,7),(4,7)], upper := (rows 35 70 133 56 81 160 328 392 264), lower := (rows 35 70 133 56 81 160 64 128 256), losses := [] }

theorem u4499 : Upper (D 9) (R 9) [34,68,129,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4499 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4499
end Delivery.IrregularNine14.P09
