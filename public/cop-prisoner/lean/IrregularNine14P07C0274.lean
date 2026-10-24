import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0062

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16440 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 100 392 19 34 193 193 449), lower := (rows 13 50 100 392 19 34 64 128 256), losses := [] }

theorem u16440 : Upper (D 7) (R 7) [12,48,96,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16441 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 392 19 96 195 131 387), lower := (rows 13 50 100 392 19 96 64 128 256), losses := [] }

theorem u16441 : Upper (D 7) (R 7) [12,48,96,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16442 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 456, targets := 32 }], pairs := [(1,6),(2,7),(3,5),(4,6)], upper := (rows 13 50 100 392 19 160 67 195 323), lower := (rows 13 50 100 392 19 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 17 168 0 128 256), good := (rows 63 50 36 424 19 160 0 160 256) },{ target := 7, region := (rows 1 2 6 8 16 32 80 0 272), good := (rows 13 374 100 264 343 32 64 0 256) }] }

theorem u16442 : Upper (D 7) (R 7) [12,48,96,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16443 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 100 392 81 33 194 130 386), lower := (rows 13 50 100 392 81 33 64 128 256), losses := [] }

theorem u16443 : Upper (D 7) (R 7) [12,48,96,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16444 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 100 392 81 34 195 131 387), lower := (rows 13 50 100 392 81 34 64 128 256), losses := [] }

theorem u16444 : Upper (D 7) (R 7) [12,48,96,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16445 : Route 9 := (fun mask => (mask,id))

def c16445 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16445 : Upper (D 7) (R 7) [12,48,96,384,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,65,128] 13 (by decide) (choices 1) [1,2] r16445 c16445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3721
  · exact u3722

def b16446 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,0),(2,7),(3,0)], upper := (rows 13 50 100 392 145 33 66 194 322), lower := (rows 13 50 100 392 145 33 64 128 256), losses := [] }

theorem u16446 : Upper (D 7) (R 7) [12,48,96,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16447 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 34, targets := 65 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,7)], upper := (rows 13 50 100 392 145 34 67 195 323), lower := (rows 13 50 100 392 145 34 64 128 256), losses := [] }

theorem u16447 : Upper (D 7) (R 7) [12,48,96,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16448 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 392 145 96 67 131 259), lower := (rows 13 50 100 392 145 96 64 128 256), losses := [] }

theorem u16448 : Upper (D 7) (R 7) [12,48,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16449 : Route 9 := (fun mask => (mask,id))

def c16449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16449 : Upper (D 7) (R 7) [12,48,96,384,130,1] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,130,1] 13 (by decide) (choices 1) [1,2] r16449 c16449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3723
  · exact u3724

def b16450 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 100 392 146 34 65 193 321), lower := (rows 13 50 100 392 146 34 64 128 256), losses := [] }

theorem u16450 : Upper (D 7) (R 7) [12,48,96,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16451 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 392 146 96 67 131 259), lower := (rows 13 50 100 392 146 96 64 128 256), losses := [] }

theorem u16451 : Upper (D 7) (R 7) [12,48,96,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16452 : Route 9 := (fun mask => (mask,id))

def c16452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16452 : Upper (D 7) (R 7) [12,48,96,384,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,192,1] 13 (by decide) (choices 1) [1,2] r16452 c16452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3725
  · exact u3726

def b16453 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 100 392 208 34 67 131 259), lower := (rows 13 50 100 392 208 34 64 128 256), losses := [] }

theorem u16453 : Upper (D 7) (R 7) [12,48,96,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16454 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 196 265 19 34 224 224 480), lower := (rows 13 50 196 265 19 34 64 128 256), losses := [] }

theorem u16454 : Upper (D 7) (R 7) [12,48,192,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16455 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,6)], upper := (rows 13 50 196 265 19 96 226 162 418), lower := (rows 13 50 196 265 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 24 16 32 0 130 258), good := (rows 13 442 132 265 411 32 0 128 256) },{ target := 7, region := (rows 1 3 4 8 25 100 64 0 256), good := (rows 63 50 100 283 19 96 96 0 256) }] }

theorem u16455 : Upper (D 7) (R 7) [12,48,192,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16456 : Route 9 := (fun mask => (mask,id))

def c16456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16456 : Upper (D 7) (R 7) [12,48,192,257,66,1] 13 := by
  apply FastRouting.sound _ _ [12,48,192,257,66,1] 13 (by decide) (choices 1) [2,32,128] r16456 c16456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3727
  · exact u3728
  · exact u3729

def b16457 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 196 265 82 34 225 161 417), lower := (rows 13 50 196 265 82 34 64 128 256), losses := [] }

theorem u16457 : Upper (D 7) (R 7) [12,48,192,257,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16458 : Route 9 := (fun mask => (mask,id))

def c16458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16458 : Upper (D 7) (R 7) [12,48,192,257,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,192,257,66,128] 13 (by decide) (choices 1) [1,2,32] r16458 c16458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3730
  · exact u3731
  · exact u3732

def b16459 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 196 266 19 33 224 224 480), lower := (rows 13 50 196 266 19 33 64 128 256), losses := [] }

theorem u16459 : Upper (D 7) (R 7) [12,48,192,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16460 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(4,7)], upper := (rows 13 50 196 266 19 96 225 161 417), lower := (rows 13 50 196 266 19 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 17 100 64 0 256), good := (rows 63 50 100 266 19 96 96 0 256) }] }

theorem u16460 : Upper (D 7) (R 7) [12,48,192,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16461 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 196 266 81 33 226 162 418), lower := (rows 13 50 196 266 81 33 64 128 256), losses := [] }

theorem u16461 : Upper (D 7) (R 7) [12,48,192,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16462 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 34, targets := 129 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 13 50 196 266 81 34 225 161 417), lower := (rows 13 50 196 266 81 34 64 128 256), losses := [] }

theorem u16462 : Upper (D 7) (R 7) [12,48,192,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16463 : Route 9 := (fun mask => (mask,id))

def c16463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16463 : Upper (D 7) (R 7) [12,48,192,258,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,192,258,65,128] 13 (by decide) (choices 1) [1,2,32] r16463 c16463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3733
  · exact u3734
  · exact u3735

def r16464 : Route 9 := (fun mask => (mask,id))

def c16464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16464 : Upper (D 7) (R 7) [12,48,192,258,66,1] 13 := by
  apply FastRouting.sound _ _ [12,48,192,258,66,1] 13 (by decide) (choices 1) [1,32,128] r16464 c16464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3736
  · exact u3737
  · exact u3738

def b16465 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 196 266 82 160 97 161 289), lower := (rows 13 50 196 266 82 160 64 128 256), losses := [] }

theorem u16465 : Upper (D 7) (R 7) [12,48,192,258,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16466 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 196 296 19 33 194 194 450), lower := (rows 13 50 196 296 19 33 64 128 256), losses := [] }

theorem u16466 : Upper (D 7) (R 7) [12,48,192,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16467 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 196 296 19 34 193 193 449), lower := (rows 13 50 196 296 19 34 64 128 256), losses := [] }

theorem u16467 : Upper (D 7) (R 7) [12,48,192,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16468 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 196, targets := 32 }], pairs := [(1,7),(2,5),(3,6),(4,7)], upper := (rows 13 50 196 296 19 96 195 131 387), lower := (rows 13 50 196 296 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 16 32 0 144 272), good := (rows 13 442 132 296 411 32 0 128 256) },{ target := 7, region := (rows 1 3 4 8 17 100 64 0 256), good := (rows 63 50 100 296 19 96 96 0 256) }] }

theorem u16468 : Upper (D 7) (R 7) [12,48,192,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16469 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 196 296 81 33 194 130 386), lower := (rows 13 50 196 296 81 33 64 128 256), losses := [] }

theorem u16469 : Upper (D 7) (R 7) [12,48,192,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16470 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 129 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 13 50 196 296 81 34 195 131 387), lower := (rows 13 50 196 296 81 34 64 128 256), losses := [] }

theorem u16470 : Upper (D 7) (R 7) [12,48,192,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16471 : Route 9 := (fun mask => (mask,id))

def c16471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16471 : Upper (D 7) (R 7) [12,48,192,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,65,128] 13 (by decide) (choices 1) [1,2] r16471 c16471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3739
  · exact u3740

def r16472 : Route 9 := (fun mask => (mask,id))

def c16472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16472 : Upper (D 7) (R 7) [12,48,192,288,66,1] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,66,1] 13 (by decide) (choices 1) [1,2,128] r16472 c16472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3741
  · exact u3742
  · exact u3743

def b16473 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 196 296 82 34 193 129 385), lower := (rows 13 50 196 296 82 34 64 128 256), losses := [] }

theorem u16473 : Upper (D 7) (R 7) [12,48,192,288,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16474 : Route 9 := (fun mask => (mask,id))

def c16474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16474 : Upper (D 7) (R 7) [12,48,192,288,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,66,128] 13 (by decide) (choices 1) [1,2] r16474 c16474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3744
  · exact u3745

def b16475 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 50, targets := 64 },{ cop := 0, region := 50, targets := 128 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 196 328 19 33 226 162 418), lower := (rows 13 50 196 328 19 33 64 128 256), losses := [] }

theorem u16475 : Upper (D 7) (R 7) [12,48,192,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16476 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 461, targets := 2 },{ cop := 0, region := 50, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 13 50 196 328 19 34 225 161 417), lower := (rows 13 50 196 328 19 34 64 128 256), losses := [] }

theorem u16476 : Upper (D 7) (R 7) [12,48,192,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16477 : Route 9 := (fun mask => (mask,id))

def c16477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16477 : Upper (D 7) (R 7) [12,48,192,320,3,128] 13 := by
  apply FastRouting.sound _ _ [12,48,192,320,3,128] 13 (by decide) (choices 1) [1,2,32] r16477 c16477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3746
  · exact u3747
  · exact u3748

def r16478 : Route 9 := (fun mask => (mask,id))

def c16478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16478 : Upper (D 7) (R 7) [12,48,192,320,130,1] 13 := by
  apply FastRouting.sound _ _ [12,48,192,320,130,1] 13 (by decide) (choices 1) [1,2,32] r16478 c16478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3749
  · exact u3750
  · exact u3751

def b16479 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 196 328 146 34 97 161 289), lower := (rows 13 50 196 328 146 34 64 128 256), losses := [] }

theorem u16479 : Upper (D 7) (R 7) [12,48,192,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16480 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 25 176 34 448 448 448), lower := (rows 13 98 7 25 176 34 64 128 256), losses := [] }

theorem u16480 : Upper (D 7) (R 7) [12,96,3,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16481 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 25 176 96 450 386 386), lower := (rows 13 98 7 25 176 96 64 128 256), losses := [] }

theorem u16481 : Upper (D 7) (R 7) [12,96,3,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16482 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 25 176 160 322 450 322), lower := (rows 13 98 7 25 176 160 64 128 256), losses := [] }

theorem u16482 : Upper (D 7) (R 7) [12,96,3,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16483 : Route 9 := (fun mask => (mask,id))

def c16483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16483 : Upper (D 7) (R 7) [12,96,3,17,160,256] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17,160,256] 13 (by decide) (choices 1) [2,128] r16483 c16483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3752
  · exact u3753

def b16484 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 25 304 34 192 192 448), lower := (rows 13 98 7 25 304 34 64 128 256), losses := [] }

theorem u16484 : Upper (D 7) (R 7) [12,96,3,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16485 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 25 304 96 194 130 386), lower := (rows 13 98 7 25 304 96 64 128 256), losses := [] }

theorem u16485 : Upper (D 7) (R 7) [12,96,3,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16486 : Route 9 := (fun mask => (mask,id))

def c16486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16486 : Upper (D 7) (R 7) [12,96,3,17,288,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17,288,128] 13 (by decide) (choices 1) [2,128] r16486 c16486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3754
  · exact u3755

def b16487 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 25 400 34 224 224 480), lower := (rows 13 98 7 25 400 34 64 128 256), losses := [] }

theorem u16487 : Upper (D 7) (R 7) [12,96,3,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16488 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 25 400 96 226 162 418), lower := (rows 13 98 7 25 400 96 64 128 256), losses := [] }

theorem u16488 : Upper (D 7) (R 7) [12,96,3,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16489_2 : Upper (D 7) (R 7) [12,96,3,17,384,128,2] 13 :=
  permutation_upper _ _ _ [12,96,3,17,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3756

theorem m16489_32 : Upper (D 7) (R 7) [12,96,3,17,384,128,32] 13 :=
  permutation_upper _ _ _ [12,96,3,17,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3757

def r16489 : Route 9 := (fun mask => (mask,id))

def c16489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16489 : Upper (D 7) (R 7) [12,96,3,17,384,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17,384,128] 13 (by decide) (choices 1) [2,32] r16489 c16489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16489_2
  · exact m16489_32

def b16490 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 56 145 34 448 448 448), lower := (rows 13 98 7 56 145 34 64 128 256), losses := [] }

theorem u16490 : Upper (D 7) (R 7) [12,96,3,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16491 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 56 145 96 450 386 386), lower := (rows 13 98 7 56 145 96 64 128 256), losses := [] }

theorem u16491 : Upper (D 7) (R 7) [12,96,3,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16492 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 56 145 160 322 450 322), lower := (rows 13 98 7 56 145 160 64 128 256), losses := [] }

theorem u16492 : Upper (D 7) (R 7) [12,96,3,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16493 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 13 98 7 56 145 288 194 194 450), lower := (rows 13 98 7 56 145 288 64 128 256), losses := [] }

theorem u16493 : Upper (D 7) (R 7) [12,96,3,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16493 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16494 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 7 56 146 33 448 448 448), lower := (rows 13 98 7 56 146 33 64 128 256), losses := [] }

theorem u16494 : Upper (D 7) (R 7) [12,96,3,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16495 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 56 146 96 449 385 385), lower := (rows 13 98 7 56 146 96 64 128 256), losses := [] }

theorem u16495 : Upper (D 7) (R 7) [12,96,3,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16496 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 13 98 7 56 146 160 321 449 321), lower := (rows 13 98 7 56 146 160 64 128 256), losses := [] }

theorem u16496 : Upper (D 7) (R 7) [12,96,3,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16497 : Route 9 := (fun mask => (mask,id))

def c16497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16497 : Upper (D 7) (R 7) [12,96,3,48,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,130,256] 13 (by decide) (choices 1) [1,128] r16497 c16497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3758
  · exact u3759

def b16498 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 56 208 33 450 386 386), lower := (rows 13 98 7 56 208 33 64 128 256), losses := [] }

theorem u16498 : Upper (D 7) (R 7) [12,96,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16499 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 56 208 34 449 385 385), lower := (rows 13 98 7 56 208 34 64 128 256), losses := [] }

theorem u16499 : Upper (D 7) (R 7) [12,96,3,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16499
end Delivery.IrregularNine14.P07
