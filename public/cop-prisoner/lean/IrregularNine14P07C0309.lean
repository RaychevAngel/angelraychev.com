import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0083
import IrregularNine14P07C0084

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18540 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 133 138 304 48 76 204 332), lower := (rows 35 67 133 138 304 48 64 128 256), losses := [] }

theorem u18540 : Upper (D 7) (R 7) [34,65,129,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18540 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18541 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 138 304 96 92 156 284), lower := (rows 35 67 133 138 304 96 64 128 256), losses := [] }

theorem u18541 : Upper (D 7) (R 7) [34,65,129,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18542 : Route 9 := (fun mask => (mask,id))

def c18542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18542 : Upper (D 7) (R 7) [34,65,129,144,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,258,4] 13 (by decide) (choices 1) [8,32] r18542 c18542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5031
  · exact u5032

def r18543 : Route 9 := (fun mask => (mask,id))

def c18543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18543 : Upper (D 7) (R 7) [34,65,129,144,258,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,258,8] 13 (by decide) (choices 1) [4,32] r18543 c18543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5033
  · exact u5034

def b18544 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 152 274 96 108 172 300), lower := (rows 35 67 133 152 274 96 64 128 256), losses := [] }

theorem u18544 : Upper (D 7) (R 7) [34,65,129,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18545 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 276 34 104 232 360), lower := (rows 35 67 133 152 276 34 64 128 256), losses := [] }

theorem u18545 : Upper (D 7) (R 7) [34,65,129,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18546 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0)], upper := (rows 35 67 133 152 276 40 98 226 354), lower := (rows 35 67 133 152 276 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 65 129 257), good := (rows 482 450 508 184 316 40 64 128 256) }] }

theorem u18546 : Upper (D 7) (R 7) [34,65,129,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18546 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18547 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 152 276 96 106 170 298), lower := (rows 35 67 133 152 276 96 64 128 256), losses := [] }

theorem u18547 : Upper (D 7) (R 7) [34,65,129,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18548 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 280 34 100 228 356), lower := (rows 35 67 133 152 280 34 64 128 256), losses := [] }

theorem u18548 : Upper (D 7) (R 7) [34,65,129,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18549 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 35 67 133 152 280 36 98 226 354), lower := (rows 35 67 133 152 280 36 64 128 256), losses := [] }

theorem u18549 : Upper (D 7) (R 7) [34,65,129,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18549 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18550 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 152 280 96 102 166 294), lower := (rows 35 67 133 152 280 96 64 128 256), losses := [] }

theorem u18550 : Upper (D 7) (R 7) [34,65,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18551 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 304 34 76 204 332), lower := (rows 35 67 133 152 304 34 64 128 256), losses := [] }

theorem u18551 : Upper (D 7) (R 7) [34,65,129,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18552 : Route 9 := (fun mask => (mask,id))

def c18552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18552 : Upper (D 7) (R 7) [34,65,129,144,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,288,4] 13 (by decide) (choices 1) [2,8] r18552 c18552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5035
  · exact u5036

def b18553 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 67 133 152 304 40 70 198 326), lower := (rows 35 67 133 152 304 40 64 128 256), losses := [] }

theorem u18553 : Upper (D 7) (R 7) [34,65,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18553 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18554 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 152 304 96 78 142 270), lower := (rows 35 67 133 152 304 96 64 128 256), losses := [] }

theorem u18554 : Upper (D 7) (R 7) [34,65,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18555 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 336 34 108 172 300), lower := (rows 35 67 133 152 336 34 64 128 256), losses := [] }

theorem u18555 : Upper (D 7) (R 7) [34,65,129,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18556 : Route 9 := (fun mask => (mask,id))

def c18556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18556 : Upper (D 7) (R 7) [34,65,129,144,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320,4] 13 (by decide) (choices 1) [2,8,32] r18556 c18556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5037
  · exact u5038
  · exact u5039

def r18557 : Route 9 := (fun mask => (mask,id))

def c18557 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18557 : Upper (D 7) (R 7) [34,65,129,144,320,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320,8] 13 (by decide) (choices 1) [2,4,32] r18557 c18557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5040
  · exact u5041
  · exact u5042

def b18558 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 168 274 36 88 216 344), lower := (rows 35 67 133 168 274 36 64 128 256), losses := [] }

theorem u18558 : Upper (D 7) (R 7) [34,65,129,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18558 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18559 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 67 133 168 274 40 84 212 340), lower := (rows 35 67 133 168 274 40 64 128 256), losses := [] }

theorem u18559 : Upper (D 7) (R 7) [34,65,129,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18559 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18560 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 133 168 274 48 76 204 332), lower := (rows 35 67 133 168 274 48 64 128 256), losses := [] }

theorem u18560 : Upper (D 7) (R 7) [34,65,129,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18560 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18561 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 168 274 96 92 156 284), lower := (rows 35 67 133 168 274 96 64 128 256), losses := [] }

theorem u18561 : Upper (D 7) (R 7) [34,65,129,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18562 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 168 276 34 88 216 344), lower := (rows 35 67 133 168 276 34 64 128 256), losses := [] }

theorem u18562 : Upper (D 7) (R 7) [34,65,129,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18563 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 67 133 168 276 40 82 210 338), lower := (rows 35 67 133 168 276 40 64 128 256), losses := [] }

theorem u18563 : Upper (D 7) (R 7) [34,65,129,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18563 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18564 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 67, targets := 128 },{ cop := 0, region := 200, targets := 1 }], pairs := [(0,7),(1,7),(3,0)], upper := (rows 35 67 133 168 276 48 74 202 330), lower := (rows 35 67 133 168 276 48 64 128 256), losses := [] }

theorem u18564 : Upper (D 7) (R 7) [34,65,129,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18564 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18565 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 168 276 96 90 154 282), lower := (rows 35 67 133 168 276 96 64 128 256), losses := [] }

theorem u18565 : Upper (D 7) (R 7) [34,65,129,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18566 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 168 280 34 84 212 340), lower := (rows 35 67 133 168 280 34 64 128 256), losses := [] }

theorem u18566 : Upper (D 7) (R 7) [34,65,129,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18567 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 168 280 36 82 210 338), lower := (rows 35 67 133 168 280 36 64 128 256), losses := [] }

theorem u18567 : Upper (D 7) (R 7) [34,65,129,160,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18567 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18568 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 67 133 168 280 48 70 198 326), lower := (rows 35 67 133 168 280 48 64 128 256), losses := [] }

theorem u18568 : Upper (D 7) (R 7) [34,65,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18568 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18569 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 133 168 280 96 86 150 278), lower := (rows 35 67 133 168 280 96 64 128 256), losses := [] }

theorem u18569 : Upper (D 7) (R 7) [34,65,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18570 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 168 336 34 92 156 284), lower := (rows 35 67 133 168 336 34 64 128 256), losses := [] }

theorem u18570 : Upper (D 7) (R 7) [34,65,129,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18571 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 168 336 36 90 154 282), lower := (rows 35 67 133 168 336 36 64 128 256), losses := [] }

theorem u18571 : Upper (D 7) (R 7) [34,65,129,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18571 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18572 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 67 133 168 336 40 86 150 278), lower := (rows 35 67 133 168 336 40 64 128 256), losses := [] }

theorem u18572 : Upper (D 7) (R 7) [34,65,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18572 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18573 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 133 168 336 48 78 142 270), lower := (rows 35 67 133 168 336 48 64 128 256), losses := [] }

theorem u18573 : Upper (D 7) (R 7) [34,65,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18573 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18574 : Route 9 := (fun mask => (mask,id))

def c18574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18574 : Upper (D 7) (R 7) [34,65,129,192,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,258,4] 13 (by decide) (choices 1) [8,16,32] r18574 c18574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5043
  · exact u5044
  · exact u5045

def b18575 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 67 133 200 274 40 116 180 308), lower := (rows 35 67 133 200 274 40 64 128 256), losses := [] }

theorem u18575 : Upper (D 7) (R 7) [34,65,129,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18575 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18576 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 133 200 274 48 108 172 300), lower := (rows 35 67 133 200 274 48 64 128 256), losses := [] }

theorem u18576 : Upper (D 7) (R 7) [34,65,129,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18576 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18577 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 276 34 120 184 312), lower := (rows 35 67 133 200 276 34 64 128 256), losses := [] }

theorem u18577 : Upper (D 7) (R 7) [34,65,129,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18578 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 67 133 200 276 40 114 178 306), lower := (rows 35 67 133 200 276 40 64 128 256), losses := [] }

theorem u18578 : Upper (D 7) (R 7) [34,65,129,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18578 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18579 : Route 9 := (fun mask => (mask,id))

def c18579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18579 : Upper (D 7) (R 7) [34,65,129,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,260,16] 13 (by decide) (choices 1) [2,8,32] r18579 c18579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5046
  · exact u5047
  · exact u5048

def b18580 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 280 34 116 180 308), lower := (rows 35 67 133 200 280 34 64 128 256), losses := [] }

theorem u18580 : Upper (D 7) (R 7) [34,65,129,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18581 : Route 9 := (fun mask => (mask,id))

def c18581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18581 : Upper (D 7) (R 7) [34,65,129,192,264,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264,4] 13 (by decide) (choices 1) [2,16,32] r18581 c18581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5049
  · exact u5050
  · exact u5051

def r18582 : Route 9 := (fun mask => (mask,id))

def c18582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18582 : Upper (D 7) (R 7) [34,65,129,192,264,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264,16] 13 (by decide) (choices 1) [2,4,32] r18582 c18582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5052
  · exact u5053
  · exact u5054

def b18583 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 304 34 92 156 284), lower := (rows 35 67 133 200 304 34 64 128 256), losses := [] }

theorem u18583 : Upper (D 7) (R 7) [34,65,129,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18584 : Route 9 := (fun mask => (mask,id))

def c18584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18584 : Upper (D 7) (R 7) [34,65,129,192,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,288,4] 13 (by decide) (choices 1) [2,8,16] r18584 c18584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5055
  · exact u5056
  · exact u5057

def b18585 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 67 133 200 304 40 86 150 278), lower := (rows 35 67 133 200 304 40 64 128 256), losses := [] }

theorem u18585 : Upper (D 7) (R 7) [34,65,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18585 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18586 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 133 200 304 48 78 142 270), lower := (rows 35 67 133 200 304 48 64 128 256), losses := [] }

theorem u18586 : Upper (D 7) (R 7) [34,65,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18586 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18587 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 176 34 84 212 340), lower := (rows 35 67 140 265 176 34 64 128 256), losses := [] }

theorem u18587 : Upper (D 7) (R 7) [34,65,136,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18588 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 140 265 176 36 82 210 338), lower := (rows 35 67 140 265 176 36 64 128 256), losses := [] }

theorem u18588 : Upper (D 7) (R 7) [34,65,136,257,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18588 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18589 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 140 265 176 48 70 198 326), lower := (rows 35 67 140 265 176 48 64 128 256), losses := [] }

theorem u18589 : Upper (D 7) (R 7) [34,65,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18589 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18590 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 140 265 176 96 86 150 278), lower := (rows 35 67 140 265 176 96 64 128 256), losses := [] }

theorem u18590 : Upper (D 7) (R 7) [34,65,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18591 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 208 34 116 180 308), lower := (rows 35 67 140 265 208 34 64 128 256), losses := [] }

theorem u18591 : Upper (D 7) (R 7) [34,65,136,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18592 : Route 9 := (fun mask => (mask,id))

def c18592 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18592 : Upper (D 7) (R 7) [34,65,136,257,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,192,4] 13 (by decide) (choices 1) [2,16,32] r18592 c18592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5058
  · exact u5059
  · exact u5060

def b18593 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 140 265 208 48 102 166 294), lower := (rows 35 67 140 265 208 48 64 128 256), losses := [] }

theorem u18593 : Upper (D 7) (R 7) [34,65,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18593 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18594 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 140 268 176 33 82 210 338), lower := (rows 35 67 140 268 176 33 64 128 256), losses := [] }

theorem u18594 : Upper (D 7) (R 7) [34,65,136,260,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18595 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 140 268 176 34 81 209 337), lower := (rows 35 67 140 268 176 34 64 128 256), losses := [] }

theorem u18595 : Upper (D 7) (R 7) [34,65,136,260,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18596 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 140 268 176 48 67 195 323), lower := (rows 35 67 140 268 176 48 64 128 256), losses := [] }

theorem u18596 : Upper (D 7) (R 7) [34,65,136,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18596 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18597 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 140 268 176 96 83 147 275), lower := (rows 35 67 140 268 176 96 64 128 256), losses := [] }

theorem u18597 : Upper (D 7) (R 7) [34,65,136,260,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18598 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 140 280 176 33 70 198 326), lower := (rows 35 67 140 280 176 33 64 128 256), losses := [] }

theorem u18598 : Upper (D 7) (R 7) [34,65,136,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18599 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 140 280 176 34 69 197 325), lower := (rows 35 67 140 280 176 34 64 128 256), losses := [] }

theorem u18599 : Upper (D 7) (R 7) [34,65,136,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18599
end Delivery.IrregularNine14.P07
