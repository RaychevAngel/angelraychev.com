import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0046
import IrregularNine14P09C0047
import IrregularNine14P09C0048

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6540 : Route 9 := (fun mask => (mask,id))

def c6540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6540 : Upper (D 9) (R 9) [96,36,136,320,129,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,129,16] 13 (by decide) (choices 1) [1,2,256] r6540 c6540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2803
  · exact u2804
  · exact u2805

def b6541 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,8)], upper := (rows 97 38 140 328 145 288 83 147 275), lower := (rows 97 38 140 328 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 360 144 288 64 128 288) },{ target := 6, region := (rows 1 6 4 8 16 296 0 128 256), good := (rows 33 38 174 296 145 288 0 128 288) }] }

theorem u6541 : Upper (D 9) (R 9) [96,36,136,320,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6541 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6542 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 33, targets := 384 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 97 38 140 328 146 33 337 401 273), lower := (rows 97 38 140 328 146 33 64 128 256), losses := [{ target := 7, region := (rows 89 6 4 24 16 125 80 0 272), good := (rows 97 38 47 361 379 33 97 0 256) },{ target := 8, region := (rows 73 6 4 8 20 109 64 128 0), good := (rows 97 54 191 105 146 33 97 128 0) }] }

theorem u6542 : Upper (D 9) (R 9) [96,36,136,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6542 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6543 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 50, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(4,0)], upper := (rows 97 38 140 328 146 48 321 385 257), lower := (rows 97 38 140 328 146 48 64 128 256), losses := [] }

theorem u6543 : Upper (D 9) (R 9) [96,36,136,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6543 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6544 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(3,7),(4,8)], upper := (rows 97 38 140 328 146 288 81 145 273), lower := (rows 97 38 140 328 146 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 296 64 128 256), good := (rows 96 54 190 360 146 288 64 128 288) }] }

theorem u6544 : Upper (D 9) (R 9) [96,36,136,320,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6544 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6545 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 49, targets := 128 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 38 140 328 273 33 210 146 402), lower := (rows 97 38 140 328 273 33 64 128 256), losses := [{ target := 7, region := (rows 73 6 4 8 24 125 64 0 256), good := (rows 97 38 63 377 305 33 97 0 256) },{ target := 8, region := (rows 73 6 4 8 16 125 64 128 0), good := (rows 97 38 175 105 49 33 97 128 0) }] }

theorem u6545 : Upper (D 9) (R 9) [96,36,136,320,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6545 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6546 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 328 273 34 209 145 401), lower := (rows 97 38 140 328 273 34 64 128 256), losses := [] }

theorem u6546 : Upper (D 9) (R 9) [96,36,136,320,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6546 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6547 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 49, targets := 128 },{ cop := 1, region := 193, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 97 38 140 328 273 48 195 131 387), lower := (rows 97 38 140 328 273 48 64 128 256), losses := [{ target := 7, region := (rows 9 6 4 8 24 60 64 0 256), good := (rows 97 38 63 377 305 48 64 0 256) }] }

theorem u6547 : Upper (D 9) (R 9) [96,36,136,320,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6547 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6548 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 328 273 160 83 147 275), lower := (rows 97 38 140 328 273 160 64 128 256), losses := [] }

theorem u6548 : Upper (D 9) (R 9) [96,36,136,320,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6548 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6549 : Route 9 := (fun mask => (mask,id))

def c6549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6549 : Upper (D 9) (R 9) [96,36,136,320,258,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,258,1] 13 (by decide) (choices 1) [1,16,128] r6549 c6549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2806
  · exact u2807
  · exact u2808

def r6550 : Route 9 := (fun mask => (mask,id))

def c6550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6550 : Upper (D 9) (R 9) [96,36,136,320,258,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,258,16] 13 (by decide) (choices 1) [1,128] r6550 c6550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2809
  · exact u2810

def b6551 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 328 274 160 81 145 273), lower := (rows 97 38 140 328 274 160 64 128 256), losses := [] }

theorem u6551 : Upper (D 9) (R 9) [96,36,136,320,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6551 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6552 : Route 9 := (fun mask => (mask,id))

def c6552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6552 : Upper (D 9) (R 9) [96,36,136,320,384,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,384,1] 13 (by decide) (choices 1) [1,2,16] r6552 c6552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2811
  · exact u2812
  · exact u2813

def b6553 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 328 400 34 81 145 273), lower := (rows 97 38 140 328 400 34 64 128 256), losses := [] }

theorem u6553 : Upper (D 9) (R 9) [96,36,136,320,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6553 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6554 : Route 9 := (fun mask => (mask,id))

def c6554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6554 : Upper (D 9) (R 9) [96,36,136,320,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,384,16] 13 (by decide) (choices 1) [1,2] r6554 c6554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2814
  · exact u2815

def b6555 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 35, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 196 137 273 34 344 408 280), lower := (rows 97 38 196 137 273 34 64 128 256), losses := [] }

theorem u6555 : Upper (D 9) (R 9) [96,36,192,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6555 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6556 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 97 38 196 137 273 40 338 402 274), lower := (rows 97 38 196 137 273 40 64 128 256), losses := [] }

theorem u6556 : Upper (D 9) (R 9) [96,36,192,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6556 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6557 : Route 9 := (fun mask => (mask,id))

def c6557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6557 : Upper (D 9) (R 9) [96,36,192,129,257,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,257,16] 13 (by decide) (choices 1) [2,8,256] r6557 c6557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2816
  · exact u2817
  · exact u2818

def r6558 : Route 9 := (fun mask => (mask,id))

def c6558 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6558 : Upper (D 9) (R 9) [96,36,192,129,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,257,256] 13 (by decide) (choices 1) [2,8,16] r6558 c6558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2819
  · exact u2820
  · exact u2821

def b6559 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,8)], upper := (rows 97 38 196 137 274 33 344 408 280), lower := (rows 97 38 196 137 274 33 64 128 256), losses := [] }

theorem u6559 : Upper (D 9) (R 9) [96,36,192,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6559 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6560 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 97 38 196 137 274 40 337 401 273), lower := (rows 97 38 196 137 274 40 64 128 256), losses := [] }

theorem u6560 : Upper (D 9) (R 9) [96,36,192,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6560 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6561 : Route 9 := (fun mask => (mask,id))

def c6561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6561 : Upper (D 9) (R 9) [96,36,192,129,258,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,258,16] 13 (by decide) (choices 1) [1,8,256] r6561 c6561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2822
  · exact u2823
  · exact u2824

def r6562 : Route 9 := (fun mask => (mask,id))

def c6562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6562 : Upper (D 9) (R 9) [96,36,192,129,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,258,256] 13 (by decide) (choices 1) [1,8,16] r6562 c6562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2825
  · exact u2826
  · exact u2827

def b6563 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,8)], upper := (rows 97 38 196 137 280 33 338 402 274), lower := (rows 97 38 196 137 280 33 64 128 256), losses := [] }

theorem u6563 : Upper (D 9) (R 9) [96,36,192,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6563 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6564 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 35, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 196 137 280 34 337 401 273), lower := (rows 97 38 196 137 280 34 64 128 256), losses := [] }

theorem u6564 : Upper (D 9) (R 9) [96,36,192,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6564 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6565 : Route 9 := (fun mask => (mask,id))

def c6565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6565 : Upper (D 9) (R 9) [96,36,192,129,264,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,264,16] 13 (by decide) (choices 1) [1,2,256] r6565 c6565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2828
  · exact u2829
  · exact u2830

def r6566 : Route 9 := (fun mask => (mask,id))

def c6566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6566 : Upper (D 9) (R 9) [96,36,192,129,264,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,264,256] 13 (by decide) (choices 1) [1,2,16] r6566 c6566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2831
  · exact u2832
  · exact u2833

def b6567 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,8)], upper := (rows 97 38 196 138 273 33 344 408 280), lower := (rows 97 38 196 138 273 33 64 128 256), losses := [] }

theorem u6567 : Upper (D 9) (R 9) [96,36,192,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6567 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6568 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 38 196 138 273 40 337 401 273), lower := (rows 97 38 196 138 273 40 64 128 256), losses := [] }

theorem u6568 : Upper (D 9) (R 9) [96,36,192,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6568 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6569 : Route 9 := (fun mask => (mask,id))

def c6569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6569 : Upper (D 9) (R 9) [96,36,192,130,257,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,257,16] 13 (by decide) (choices 1) [1,8,256] r6569 c6569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2834
  · exact u2835
  · exact u2836

def r6570 : Route 9 := (fun mask => (mask,id))

def c6570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6570 : Upper (D 9) (R 9) [96,36,192,130,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,257,256] 13 (by decide) (choices 1) [1,8,16] r6570 c6570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2837
  · exact u2838
  · exact u2839

def b6571 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,8)], upper := (rows 97 38 196 138 280 33 337 401 273), lower := (rows 97 38 196 138 280 33 64 128 256), losses := [] }

theorem u6571 : Upper (D 9) (R 9) [96,36,192,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6571 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6572 : Route 9 := (fun mask => (mask,id))

def c6572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6572 : Upper (D 9) (R 9) [96,36,192,130,264,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,264,16] 13 (by decide) (choices 1) [1,256] r6572 c6572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2840
  · exact u2841

def r6573 : Route 9 := (fun mask => (mask,id))

def c6573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6573 : Upper (D 9) (R 9) [96,36,192,130,264,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,264,256] 13 (by decide) (choices 1) [1,16] r6573 c6573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2842
  · exact u2843

def r6574 : Route 9 := (fun mask => (mask,id))

def c6574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6574 : Upper (D 9) (R 9) [96,36,192,144,257,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,257,1] 13 (by decide) (choices 1) [2,8,256] r6574 c6574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2844
  · exact u2845
  · exact u2846

def b6575 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 152 273 34 329 393 265), lower := (rows 97 38 196 152 273 34 64 128 256), losses := [] }

theorem u6575 : Upper (D 9) (R 9) [96,36,192,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6575 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6576 : Route 9 := (fun mask => (mask,id))

def c6576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6576 : Upper (D 9) (R 9) [96,36,192,144,257,8] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,257,8] 13 (by decide) (choices 1) [1,2,256] r6576 c6576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2847
  · exact u2848
  · exact u2849

def r6577 : Route 9 := (fun mask => (mask,id))

def c6577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6577 : Upper (D 9) (R 9) [96,36,192,144,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,257,256] 13 (by decide) (choices 1) [1,2,8] r6577 c6577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2850
  · exact u2851
  · exact u2852

def r6578 : Route 9 := (fun mask => (mask,id))

def c6578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6578 : Upper (D 9) (R 9) [96,36,192,144,258,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,258,1] 13 (by decide) (choices 1) [1,8,256] r6578 c6578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2853
  · exact u2854
  · exact u2855

def r6579 : Route 9 := (fun mask => (mask,id))

def c6579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6579 : Upper (D 9) (R 9) [96,36,192,144,258,8] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,258,8] 13 (by decide) (choices 1) [1,256] r6579 c6579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2856
  · exact u2857

def r6580 : Route 9 := (fun mask => (mask,id))

def c6580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6580 : Upper (D 9) (R 9) [96,36,192,144,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,258,256] 13 (by decide) (choices 1) [1,8] r6580 c6580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2858
  · exact u2859

def r6581 : Route 9 := (fun mask => (mask,id))

def c6581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6581 : Upper (D 9) (R 9) [96,36,192,144,264,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,264,1] 13 (by decide) (choices 1) [1,2,256] r6581 c6581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2860
  · exact u2861
  · exact u2862

def b6582 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 196 152 280 34 321 385 257), lower := (rows 97 38 196 152 280 34 64 128 256), losses := [] }

theorem u6582 : Upper (D 9) (R 9) [96,36,192,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6582 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6583 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,8)], upper := (rows 97 38 196 152 280 288 67 131 259), lower := (rows 97 38 196 152 280 288 64 128 256), losses := [] }

theorem u6583 : Upper (D 9) (R 9) [96,36,192,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6583 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6584 : Route 9 := (fun mask => (mask,id))

def c6584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6584 : Upper (D 9) (R 9) [96,36,192,257,258,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,258,1] 13 (by decide) (choices 1) [8,16,128] r6584 c6584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2863
  · exact u2864
  · exact u2865

def r6585 : Route 9 := (fun mask => (mask,id))

def c6585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6585 : Upper (D 9) (R 9) [96,36,192,257,258,8] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,258,8] 13 (by decide) (choices 1) [1,16,128] r6585 c6585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2866
  · exact u2867
  · exact u2868

def b6586 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 3, region := 196, targets := 256 }], pairs := [(2,5),(2,8),(3,5),(3,6)], upper := (rows 97 38 196 265 274 48 201 137 393), lower := (rows 97 38 196 265 274 48 64 128 256), losses := [] }

theorem u6586 : Upper (D 9) (R 9) [96,36,192,257,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6586 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6587 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 196 265 274 160 89 153 281), lower := (rows 97 38 196 265 274 160 64 128 256), losses := [] }

theorem u6587 : Upper (D 9) (R 9) [96,36,192,257,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6587 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6588 : Route 9 := (fun mask => (mask,id))

def c6588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6588 : Upper (D 9) (R 9) [96,36,192,257,384,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,384,1] 13 (by decide) (choices 1) [2,8,16] r6588 c6588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2869
  · exact u2870
  · exact u2871

def b6589 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 265 400 34 89 153 281), lower := (rows 97 38 196 265 400 34 64 128 256), losses := [] }

theorem u6589 : Upper (D 9) (R 9) [96,36,192,257,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6589 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6590 : Route 9 := (fun mask => (mask,id))

def c6590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6590 : Upper (D 9) (R 9) [96,36,192,257,384,8] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,384,8] 13 (by decide) (choices 1) [1,2,16] r6590 c6590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2872
  · exact u2873
  · exact u2874

def r6591 : Route 9 := (fun mask => (mask,id))

def c6591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6591 : Upper (D 9) (R 9) [96,36,192,257,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,384,16] 13 (by decide) (choices 1) [1,2,8] r6591 c6591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2875
  · exact u2876
  · exact u2877

def r6592 : Route 9 := (fun mask => (mask,id))

def c6592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6592 : Upper (D 9) (R 9) [96,36,192,258,384,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,258,384,1] 13 (by decide) (choices 1) [1,8,16] r6592 c6592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2878
  · exact u2879
  · exact u2880

def r6593 : Route 9 := (fun mask => (mask,id))

def c6593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6593 : Upper (D 9) (R 9) [96,36,192,258,384,8] 13 := by
  apply FastRouting.sound _ _ [96,36,192,258,384,8] 13 (by decide) (choices 1) [1,16] r6593 c6593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2881
  · exact u2882

def r6594 : Route 9 := (fun mask => (mask,id))

def c6594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6594 : Upper (D 9) (R 9) [96,36,192,258,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,192,258,384,16] 13 (by decide) (choices 1) [1,8] r6594 c6594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2883
  · exact u2884

def b6595 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 388 137 273 34 88 216 344), lower := (rows 97 38 388 137 273 34 64 128 256), losses := [] }

theorem u6595 : Upper (D 9) (R 9) [96,36,384,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6595 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6596 : Route 9 := (fun mask => (mask,id))

def c6596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6596 : Upper (D 9) (R 9) [96,36,384,129,257,8] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,257,8] 13 (by decide) (choices 1) [2,16] r6596 c6596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2885
  · exact u2886

def b6597 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 388 137 273 96 90 154 282), lower := (rows 97 38 388 137 273 96 64 128 256), losses := [] }

theorem u6597 : Upper (D 9) (R 9) [96,36,384,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6597 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6598 : Route 9 := (fun mask => (mask,id))

def c6598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6598 : Upper (D 9) (R 9) [96,36,384,129,258,1] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,258,1] 13 (by decide) (choices 1) [8,16] r6598 c6598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2887
  · exact u2888

def b6599 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 4, region := 233, targets := 256 }], pairs := [(0,7),(0,8),(3,8),(4,7)], upper := (rows 97 38 388 137 274 40 81 209 337), lower := (rows 97 38 388 137 274 40 64 128 256), losses := [] }

theorem u6599 : Upper (D 9) (R 9) [96,36,384,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6599 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6599
end Delivery.IrregularNine14.P09
