import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0113
import IrregularNine14P07C0114

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22440 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 70 392 208 34 81 145 273), lower := (rows 37 42 70 392 208 34 64 128 256), losses := [] }

theorem u22440 : Upper (D 7) (R 7) [36,40,66,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22441 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 42 70 392 208 48 67 131 259), lower := (rows 37 42 70 392 208 48 64 128 256), losses := [] }

theorem u22441 : Upper (D 7) (R 7) [36,40,66,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22441 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22442 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 84 200 19 33 450 386 386), lower := (rows 37 42 84 200 19 33 64 128 256), losses := [] }

theorem u22442 : Upper (D 7) (R 7) [36,40,80,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22443 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 84 200 19 34 449 385 385), lower := (rows 37 42 84 200 19 34 64 128 256), losses := [] }

theorem u22443 : Upper (D 7) (R 7) [36,40,80,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22444 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 84 200 19 160 323 387 259), lower := (rows 37 42 84 200 19 160 64 128 256), losses := [] }

theorem u22444 : Upper (D 7) (R 7) [36,40,80,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22445 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(0,6),(2,5),(3,5)], upper := (rows 37 42 84 200 19 288 195 131 387), lower := (rows 37 42 84 200 19 288 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 308 0 144 272), good := (rows 37 42 437 136 435 288 0 128 288) }] }

theorem u22445 : Upper (D 7) (R 7) [36,40,80,192,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22445 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22446 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 84 200 145 33 322 386 258), lower := (rows 37 42 84 200 145 33 64 128 256), losses := [] }

theorem u22446 : Upper (D 7) (R 7) [36,40,80,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22447 : Route 9 := (fun mask => (mask,id))

def c22447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u22447 : Upper (D 7) (R 7) [36,40,80,192,129,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,129,2] 13 (by decide) (choices 1) [1,2,256] r22447 c22447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6825
  · exact u6826
  · exact u6827

def r22448 : Route 9 := (fun mask => (mask,id))

def c22448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22448 : Upper (D 7) (R 7) [36,40,80,192,129,256] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,129,256] 13 (by decide) (choices 1) [1,2] r22448 c22448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6828
  · exact u6829

def b22449 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 42 84 200 146 33 323 387 259), lower := (rows 37 42 84 200 146 33 64 128 256), losses := [] }

theorem u22449 : Upper (D 7) (R 7) [36,40,80,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22450 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 54, targets := 1 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 42 84 200 146 34 321 385 257), lower := (rows 37 42 84 200 146 34 64 128 256), losses := [] }

theorem u22450 : Upper (D 7) (R 7) [36,40,80,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22451 : Route 9 := (fun mask => (mask,id))

def c22451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22451 : Upper (D 7) (R 7) [36,40,80,192,130,256] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,130,256] 13 (by decide) (choices 1) [1,2] r22451 c22451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6830
  · exact u6831

def b22452 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 84 200 273 33 194 130 386), lower := (rows 37 42 84 200 273 33 64 128 256), losses := [] }

theorem u22452 : Upper (D 7) (R 7) [36,40,80,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22453 : Route 9 := (fun mask => (mask,id))

def c22453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22453 : Upper (D 7) (R 7) [36,40,80,192,257,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,257,2] 13 (by decide) (choices 1) [1,2,128] r22453 c22453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6832
  · exact u6833
  · exact u6834

def b22454 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 84 200 273 160 67 131 259), lower := (rows 37 42 84 200 273 160 64 128 256), losses := [] }

theorem u22454 : Upper (D 7) (R 7) [36,40,80,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22455 : Route 9 := (fun mask => (mask,id))

def c22455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22455 : Upper (D 7) (R 7) [36,40,80,192,258,1] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,258,1] 13 (by decide) (choices 1) [1,2,128] r22455 c22455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6835
  · exact u6836
  · exact u6837

def b22456 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 37 42 84 200 274 34 193 129 385), lower := (rows 37 42 84 200 274 34 64 128 256), losses := [] }

theorem u22456 : Upper (D 7) (R 7) [36,40,80,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22457 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 84 200 274 160 67 131 259), lower := (rows 37 42 84 200 274 160 64 128 256), losses := [] }

theorem u22457 : Upper (D 7) (R 7) [36,40,80,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22458 : Route 9 := (fun mask => (mask,id))

def c22458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22458 : Upper (D 7) (R 7) [36,40,80,192,384,1] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,384,1] 13 (by decide) (choices 1) [1,2] r22458 c22458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6838
  · exact u6839

def r22459 : Route 9 := (fun mask => (mask,id))

def c22459 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22459 : Upper (D 7) (R 7) [36,40,80,192,384,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,384,2] 13 (by decide) (choices 1) [1,2] r22459 c22459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6840
  · exact u6841

def b22460 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(2,5)], upper := (rows 37 42 84 265 145 34 194 194 450), lower := (rows 37 42 84 265 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 98 162 290), good := (rows 477 458 84 285 157 450 64 128 256) }] }

theorem u22460 : Upper (D 7) (R 7) [36,40,80,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22461 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 265 145 96 194 130 386), lower := (rows 37 42 84 265 145 96 64 128 256), losses := [] }

theorem u22461 : Upper (D 7) (R 7) [36,40,80,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22462 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 42 84 265 145 160 66 194 322), lower := (rows 37 42 84 265 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 117 265 177 160 64 160 256) }] }

theorem u22462 : Upper (D 7) (R 7) [36,40,80,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22463 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 84 265 146 33 194 194 450), lower := (rows 37 42 84 265 146 33 64 128 256), losses := [] }

theorem u22463 : Upper (D 7) (R 7) [36,40,80,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22464 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 37 42 84 265 146 34 193 193 449), lower := (rows 37 42 84 265 146 34 64 128 256), losses := [] }

theorem u22464 : Upper (D 7) (R 7) [36,40,80,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22465 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 265 146 96 195 131 387), lower := (rows 37 42 84 265 146 96 64 128 256), losses := [] }

theorem u22465 : Upper (D 7) (R 7) [36,40,80,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22466 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 84 265 146 160 67 195 323), lower := (rows 37 42 84 265 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 117 265 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 42 53 265 178 160 0 160 256) }] }

theorem u22466 : Upper (D 7) (R 7) [36,40,80,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22467 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 84 266 145 33 194 194 450), lower := (rows 37 42 84 266 145 33 64 128 256), losses := [] }

theorem u22467 : Upper (D 7) (R 7) [36,40,80,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22468 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 84 266 145 34 193 193 449), lower := (rows 37 42 84 266 145 34 64 128 256), losses := [] }

theorem u22468 : Upper (D 7) (R 7) [36,40,80,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22469 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 266 145 96 195 131 387), lower := (rows 37 42 84 266 145 96 64 128 256), losses := [] }

theorem u22469 : Upper (D 7) (R 7) [36,40,80,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22470 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 84 266 145 160 67 195 323), lower := (rows 37 42 84 266 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 117 264 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 42 53 266 177 160 0 160 256) }] }

theorem u22470 : Upper (D 7) (R 7) [36,40,80,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22471 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 84 266 146 33 193 193 449), lower := (rows 37 42 84 266 146 33 64 128 256), losses := [] }

theorem u22471 : Upper (D 7) (R 7) [36,40,80,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22472 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 266 146 96 193 129 385), lower := (rows 37 42 84 266 146 96 64 128 256), losses := [] }

theorem u22472 : Upper (D 7) (R 7) [36,40,80,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22473 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 42 84 266 146 160 65 193 321), lower := (rows 37 42 84 266 146 160 64 128 256), losses := [] }

theorem u22473 : Upper (D 7) (R 7) [36,40,80,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22474 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 84 328 19 33 194 130 386), lower := (rows 37 42 84 328 19 33 64 128 256), losses := [] }

theorem u22474 : Upper (D 7) (R 7) [36,40,80,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22475 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 84 328 19 34 193 129 385), lower := (rows 37 42 84 328 19 34 64 128 256), losses := [] }

theorem u22475 : Upper (D 7) (R 7) [36,40,80,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22476 : Route 9 := (fun mask => (mask,id))

def c22476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22476 : Upper (D 7) (R 7) [36,40,80,320,3,128] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320,3,128] 13 (by decide) (choices 1) [1,2,128] r22476 c22476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6842
  · exact u6843
  · exact u6844

def b22477 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 84 328 145 33 194 130 386), lower := (rows 37 42 84 328 145 33 64 128 256), losses := [] }

theorem u22477 : Upper (D 7) (R 7) [36,40,80,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22478 : Route 9 := (fun mask => (mask,id))

def c22478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22478 : Upper (D 7) (R 7) [36,40,80,320,129,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320,129,2] 13 (by decide) (choices 1) [1,2,128] r22478 c22478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6845
  · exact u6846
  · exact u6847

def b22479 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 84 328 145 160 67 131 259), lower := (rows 37 42 84 328 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 117 328 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 42 53 264 177 160 0 160 256) }] }

theorem u22479 : Upper (D 7) (R 7) [36,40,80,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22480 : Route 9 := (fun mask => (mask,id))

def c22480 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22480 : Upper (D 7) (R 7) [36,40,80,320,130,1] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320,130,1] 13 (by decide) (choices 1) [1,2,128] r22480 c22480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6848
  · exact u6849
  · exact u6850

def b22481 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 37 42 84 328 146 34 193 129 385), lower := (rows 37 42 84 328 146 34 64 128 256), losses := [] }

theorem u22481 : Upper (D 7) (R 7) [36,40,80,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22482 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 84 328 146 160 67 131 259), lower := (rows 37 42 84 328 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 117 328 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 42 53 264 178 160 0 160 256) }] }

theorem u22482 : Upper (D 7) (R 7) [36,40,80,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22483 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 84 392 19 33 194 194 450), lower := (rows 37 42 84 392 19 33 64 128 256), losses := [] }

theorem u22483 : Upper (D 7) (R 7) [36,40,80,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22484 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 42 84 392 19 34 193 193 449), lower := (rows 37 42 84 392 19 34 64 128 256), losses := [] }

theorem u22484 : Upper (D 7) (R 7) [36,40,80,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22485 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 392 19 96 195 131 387), lower := (rows 37 42 84 392 19 96 64 128 256), losses := [] }

theorem u22485 : Upper (D 7) (R 7) [36,40,80,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22486 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 84 392 19 160 67 195 323), lower := (rows 37 42 84 392 19 160 64 128 256), losses := [] }

theorem u22486 : Upper (D 7) (R 7) [36,40,80,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22487 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 84 392 145 33 66 194 322), lower := (rows 37 42 84 392 145 33 64 128 256), losses := [] }

theorem u22487 : Upper (D 7) (R 7) [36,40,80,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22488 : Route 9 := (fun mask => (mask,id))

def c22488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22488 : Upper (D 7) (R 7) [36,40,80,384,129,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,384,129,2] 13 (by decide) (choices 1) [1,2] r22488 c22488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6851
  · exact u6852

def b22489 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 392 145 96 67 131 259), lower := (rows 37 42 84 392 145 96 64 128 256), losses := [] }

theorem u22489 : Upper (D 7) (R 7) [36,40,80,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22490 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 42 84 392 146 33 67 195 323), lower := (rows 37 42 84 392 146 33 64 128 256), losses := [] }

theorem u22490 : Upper (D 7) (R 7) [36,40,80,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22491 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 42 84 392 146 34 65 193 321), lower := (rows 37 42 84 392 146 34 64 128 256), losses := [] }

theorem u22491 : Upper (D 7) (R 7) [36,40,80,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22492 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 84 392 146 96 67 131 259), lower := (rows 37 42 84 392 146 96 64 128 256), losses := [] }

theorem u22492 : Upper (D 7) (R 7) [36,40,80,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22493 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 37 42 196 265 19 34 208 208 464), lower := (rows 37 42 196 265 19 34 64 128 256), losses := [] }

theorem u22493 : Upper (D 7) (R 7) [36,40,192,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22494 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 37 42 196 265 19 48 194 194 450), lower := (rows 37 42 196 265 19 48 64 128 256), losses := [] }

theorem u22494 : Upper (D 7) (R 7) [36,40,192,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22494 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22495 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 196 265 19 96 210 146 402), lower := (rows 37 42 196 265 19 96 64 128 256), losses := [] }

theorem u22495 : Upper (D 7) (R 7) [36,40,192,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22496 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 37 42 196 265 81 34 210 146 402), lower := (rows 37 42 196 265 81 34 64 128 256), losses := [] }

theorem u22496 : Upper (D 7) (R 7) [36,40,192,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22497 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 42 196 265 81 48 194 130 386), lower := (rows 37 42 196 265 81 48 64 128 256), losses := [] }

theorem u22497 : Upper (D 7) (R 7) [36,40,192,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22497 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22498 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 265 81 160 82 146 274), lower := (rows 37 42 196 265 81 160 64 128 256), losses := [] }

theorem u22498 : Upper (D 7) (R 7) [36,40,192,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22499 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 196 265 82 33 210 146 402), lower := (rows 37 42 196 265 82 33 64 128 256), losses := [] }

theorem u22499 : Upper (D 7) (R 7) [36,40,192,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22499
end Delivery.IrregularNine14.P07
