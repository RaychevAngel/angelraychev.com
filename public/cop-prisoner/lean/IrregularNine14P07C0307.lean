import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0082
import IrregularNine14P07C0083

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r18420 : Route 9 := (fun mask => (mask,id))

def c18420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18420 : Upper (D 7) (R 7) [34,65,40,258,129,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,129,16] 13 (by decide) (choices 1) [4,128] r18420 c18420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4962
  · exact u4963

def b18421 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 266 145 96 212 148 404), lower := (rows 35 67 44 266 145 96 64 128 256), losses := [] }

theorem u18421 : Upper (D 7) (R 7) [34,65,40,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18422 : Route 9 := (fun mask => (mask,id))

def c18422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18422 : Upper (D 7) (R 7) [34,65,40,258,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,129,128] 13 (by decide) (choices 1) [4,16] r18422 c18422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4964
  · exact u4965

def b18423 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 44 266 148 33 208 208 464), lower := (rows 35 67 44 266 148 33 64 128 256), losses := [] }

theorem u18423 : Upper (D 7) (R 7) [34,65,40,258,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18424 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(3,5)], upper := (rows 35 67 44 266 148 48 193 193 449), lower := (rows 35 67 44 266 148 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 60 67 131 259), good := (rows 481 449 60 508 180 48 64 128 256) }] }

theorem u18424 : Upper (D 7) (R 7) [34,65,40,258,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18424 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18425 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 266 148 96 209 145 401), lower := (rows 35 67 44 266 148 96 64 128 256), losses := [] }

theorem u18425 : Upper (D 7) (R 7) [34,65,40,258,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18426 : Route 9 := (fun mask => (mask,id))

def c18426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18426 : Upper (D 7) (R 7) [34,65,40,258,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,132,128] 13 (by decide) (choices 1) [1,16] r18426 c18426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4966
  · exact u4967

def b18427 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 44 266 208 33 212 148 404), lower := (rows 35 67 44 266 208 33 64 128 256), losses := [] }

theorem u18427 : Upper (D 7) (R 7) [34,65,40,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18428 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 266 208 36 209 145 401), lower := (rows 35 67 44 266 208 36 64 128 256), losses := [] }

theorem u18428 : Upper (D 7) (R 7) [34,65,40,258,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18428 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18429 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 266 208 48 197 133 389), lower := (rows 35 67 44 266 208 48 64 128 256), losses := [] }

theorem u18429 : Upper (D 7) (R 7) [34,65,40,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18429 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18430 : Route 9 := (fun mask => (mask,id))

def c18430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18430 : Upper (D 7) (R 7) [34,65,40,258,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,192,128] 13 (by decide) (choices 1) [1,4,16] r18430 c18430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4968
  · exact u4969
  · exact u4970

def b18431 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 268 145 34 208 208 464), lower := (rows 35 67 44 268 145 34 64 128 256), losses := [] }

theorem u18431 : Upper (D 7) (R 7) [34,65,40,260,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18432 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 67 44 268 145 48 194 194 450), lower := (rows 35 67 44 268 145 48 64 128 256), losses := [] }

theorem u18432 : Upper (D 7) (R 7) [34,65,40,260,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18432 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18433 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 268 145 96 210 146 402), lower := (rows 35 67 44 268 145 96 64 128 256), losses := [] }

theorem u18433 : Upper (D 7) (R 7) [34,65,40,260,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18434 : Route 9 := (fun mask => (mask,id))

def c18434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18434 : Upper (D 7) (R 7) [34,65,40,260,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,129,128] 13 (by decide) (choices 1) [2,16] r18434 c18434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4971
  · exact u4972

def b18435 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 268 146 33 208 208 464), lower := (rows 35 67 44 268 146 33 64 128 256), losses := [] }

theorem u18435 : Upper (D 7) (R 7) [34,65,40,260,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18436 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 67 44 268 146 48 193 193 449), lower := (rows 35 67 44 268 146 48 64 128 256), losses := [] }

theorem u18436 : Upper (D 7) (R 7) [34,65,40,260,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18436 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18437 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 268 146 96 209 145 401), lower := (rows 35 67 44 268 146 96 64 128 256), losses := [] }

theorem u18437 : Upper (D 7) (R 7) [34,65,40,260,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18438 : Route 9 := (fun mask => (mask,id))

def c18438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18438 : Upper (D 7) (R 7) [34,65,40,260,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,130,128] 13 (by decide) (choices 1) [1,16] r18438 c18438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4973
  · exact u4974

def b18439 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 268 208 33 210 146 402), lower := (rows 35 67 44 268 208 33 64 128 256), losses := [] }

theorem u18439 : Upper (D 7) (R 7) [34,65,40,260,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18440 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 268 208 34 209 145 401), lower := (rows 35 67 44 268 208 34 64 128 256), losses := [] }

theorem u18440 : Upper (D 7) (R 7) [34,65,40,260,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18441 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 35 67 44 268 208 48 195 131 387), lower := (rows 35 67 44 268 208 48 64 128 256), losses := [] }

theorem u18441 : Upper (D 7) (R 7) [34,65,40,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18441 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18442 : Route 9 := (fun mask => (mask,id))

def c18442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18442 : Upper (D 7) (R 7) [34,65,40,260,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,192,128] 13 (by decide) (choices 1) [1,2,16] r18442 c18442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4975
  · exact u4976
  · exact u4977

def b18443 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 280 145 34 196 196 452), lower := (rows 35 67 44 280 145 34 64 128 256), losses := [] }

theorem u18443 : Upper (D 7) (R 7) [34,65,40,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18444 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 280 145 36 194 194 450), lower := (rows 35 67 44 280 145 36 64 128 256), losses := [] }

theorem u18444 : Upper (D 7) (R 7) [34,65,40,272,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18444 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18445 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 280 145 96 198 134 390), lower := (rows 35 67 44 280 145 96 64 128 256), losses := [] }

theorem u18445 : Upper (D 7) (R 7) [34,65,40,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18446 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 35 67 44 280 145 160 70 198 326), lower := (rows 35 67 44 280 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 316 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 65 44 316 177 160 64 160 256) }] }

theorem u18446 : Upper (D 7) (R 7) [34,65,40,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18447 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 280 146 33 196 196 452), lower := (rows 35 67 44 280 146 33 64 128 256), losses := [] }

theorem u18447 : Upper (D 7) (R 7) [34,65,40,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18448 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 280 146 36 193 193 449), lower := (rows 35 67 44 280 146 36 64 128 256), losses := [] }

theorem u18448 : Upper (D 7) (R 7) [34,65,40,272,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18448 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18449 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 280 146 96 197 133 389), lower := (rows 35 67 44 280 146 96 64 128 256), losses := [] }

theorem u18449 : Upper (D 7) (R 7) [34,65,40,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18450 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 67, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,0)], upper := (rows 35 67 44 280 146 160 69 197 325), lower := (rows 35 67 44 280 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 316 178 160 64 160 256) }] }

theorem u18450 : Upper (D 7) (R 7) [34,65,40,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18451 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 280 148 33 194 194 450), lower := (rows 35 67 44 280 148 33 64 128 256), losses := [] }

theorem u18451 : Upper (D 7) (R 7) [34,65,40,272,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18452 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 280 148 34 193 193 449), lower := (rows 35 67 44 280 148 34 64 128 256), losses := [] }

theorem u18452 : Upper (D 7) (R 7) [34,65,40,272,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18453 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 280 148 96 195 131 387), lower := (rows 35 67 44 280 148 96 64 128 256), losses := [] }

theorem u18453 : Upper (D 7) (R 7) [34,65,40,272,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18454 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 67, targets := 128 },{ cop := 0, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,0)], upper := (rows 35 67 44 280 148 160 67 195 323), lower := (rows 35 67 44 280 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 316 180 160 64 160 256) }] }

theorem u18454 : Upper (D 7) (R 7) [34,65,40,272,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18455 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 280 208 33 198 134 390), lower := (rows 35 67 44 280 208 33 64 128 256), losses := [] }

theorem u18455 : Upper (D 7) (R 7) [34,65,40,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18456 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 280 208 34 197 133 389), lower := (rows 35 67 44 280 208 34 64 128 256), losses := [] }

theorem u18456 : Upper (D 7) (R 7) [34,65,40,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18457 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 280 208 36 195 131 387), lower := (rows 35 67 44 280 208 36 64 128 256), losses := [] }

theorem u18457 : Upper (D 7) (R 7) [34,65,40,272,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18457 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18458 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 35 67 44 280 208 160 71 135 263), lower := (rows 35 67 44 280 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 316 240 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 65 44 316 240 160 64 160 256) }] }

theorem u18458 : Upper (D 7) (R 7) [34,65,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18459 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 328 145 34 212 148 404), lower := (rows 35 67 44 328 145 34 64 128 256), losses := [] }

theorem u18459 : Upper (D 7) (R 7) [34,65,40,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18460 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 328 145 36 210 146 402), lower := (rows 35 67 44 328 145 36 64 128 256), losses := [] }

theorem u18460 : Upper (D 7) (R 7) [34,65,40,320,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18460 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18461 : Route 9 := (fun mask => (mask,id))

def c18461 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18461 : Upper (D 7) (R 7) [34,65,40,320,129,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,129,16] 13 (by decide) (choices 1) [2,4,128] r18461 c18461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4978
  · exact u4979
  · exact u4980

def r18462 : Route 9 := (fun mask => (mask,id))

def c18462 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18462 : Upper (D 7) (R 7) [34,65,40,320,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,129,128] 13 (by decide) (choices 1) [2,4,16] r18462 c18462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4981
  · exact u4982
  · exact u4983

def b18463 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 328 146 33 212 148 404), lower := (rows 35 67 44 328 146 33 64 128 256), losses := [] }

theorem u18463 : Upper (D 7) (R 7) [34,65,40,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18464 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 328 146 36 209 145 401), lower := (rows 35 67 44 328 146 36 64 128 256), losses := [] }

theorem u18464 : Upper (D 7) (R 7) [34,65,40,320,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18464 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18465 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 44 328 146 48 197 133 389), lower := (rows 35 67 44 328 146 48 64 128 256), losses := [] }

theorem u18465 : Upper (D 7) (R 7) [34,65,40,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18465 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18466 : Route 9 := (fun mask => (mask,id))

def c18466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18466 : Upper (D 7) (R 7) [34,65,40,320,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,130,128] 13 (by decide) (choices 1) [1,4,16] r18466 c18466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4984
  · exact u4985
  · exact u4986

def b18467 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 328 148 33 210 146 402), lower := (rows 35 67 44 328 148 33 64 128 256), losses := [] }

theorem u18467 : Upper (D 7) (R 7) [34,65,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18468 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 328 148 34 209 145 401), lower := (rows 35 67 44 328 148 34 64 128 256), losses := [] }

theorem u18468 : Upper (D 7) (R 7) [34,65,40,320,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18469 : Route 9 := (fun mask => (mask,id))

def c18469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18469 : Upper (D 7) (R 7) [34,65,40,320,132,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132,16] 13 (by decide) (choices 1) [1,2,128] r18469 c18469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4987
  · exact u4988
  · exact u4989

def r18470 : Route 9 := (fun mask => (mask,id))

def c18470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18470 : Upper (D 7) (R 7) [34,65,40,320,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132,128] 13 (by decide) (choices 1) [1,2,16] r18470 c18470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4990
  · exact u4991
  · exact u4992

def b18471 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 392 145 34 84 212 340), lower := (rows 35 67 44 392 145 34 64 128 256), losses := [] }

theorem u18471 : Upper (D 7) (R 7) [34,65,40,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18472 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 392 145 36 82 210 338), lower := (rows 35 67 44 392 145 36 64 128 256), losses := [] }

theorem u18472 : Upper (D 7) (R 7) [34,65,40,384,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18472 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18473 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(3,0)], upper := (rows 35 67 44 392 145 48 70 198 326), lower := (rows 35 67 44 392 145 48 64 128 256), losses := [] }

theorem u18473 : Upper (D 7) (R 7) [34,65,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18473 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18474 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 392 145 96 86 150 278), lower := (rows 35 67 44 392 145 96 64 128 256), losses := [] }

theorem u18474 : Upper (D 7) (R 7) [34,65,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18475 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 392 146 33 84 212 340), lower := (rows 35 67 44 392 146 33 64 128 256), losses := [] }

theorem u18475 : Upper (D 7) (R 7) [34,65,40,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18476 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 392 146 36 81 209 337), lower := (rows 35 67 44 392 146 36 64 128 256), losses := [] }

theorem u18476 : Upper (D 7) (R 7) [34,65,40,384,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18476 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18477 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 67 44 392 146 48 69 197 325), lower := (rows 35 67 44 392 146 48 64 128 256), losses := [] }

theorem u18477 : Upper (D 7) (R 7) [34,65,40,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18477 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18478 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 392 146 96 85 149 277), lower := (rows 35 67 44 392 146 96 64 128 256), losses := [] }

theorem u18478 : Upper (D 7) (R 7) [34,65,40,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18479 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 392 148 33 82 210 338), lower := (rows 35 67 44 392 148 33 64 128 256), losses := [] }

theorem u18479 : Upper (D 7) (R 7) [34,65,40,384,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18479
end Delivery.IrregularNine14.P07
