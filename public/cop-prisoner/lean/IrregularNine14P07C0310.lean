import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0084

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18600 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 140 280 176 36 67 195 323), lower := (rows 35 67 140 280 176 36 64 128 256), losses := [] }

theorem u18600 : Upper (D 7) (R 7) [34,65,136,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18600 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18601 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 140 280 176 96 71 135 263), lower := (rows 35 67 140 280 176 96 64 128 256), losses := [] }

theorem u18601 : Upper (D 7) (R 7) [34,65,136,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18602 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 140 296 208 33 86 150 278), lower := (rows 35 67 140 296 208 33 64 128 256), losses := [] }

theorem u18602 : Upper (D 7) (R 7) [34,65,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18603 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 140 296 208 34 85 149 277), lower := (rows 35 67 140 296 208 34 64 128 256), losses := [] }

theorem u18603 : Upper (D 7) (R 7) [34,65,136,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18604 : Route 9 := (fun mask => (mask,id))

def c18604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18604 : Upper (D 7) (R 7) [34,65,136,288,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,192,4] 13 (by decide) (choices 1) [1,2,16] r18604 c18604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5061
  · exact u5062
  · exact u5063

def b18605 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 140 296 208 48 71 135 263), lower := (rows 35 67 140 296 208 48 64 128 256), losses := [] }

theorem u18605 : Upper (D 7) (R 7) [34,65,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18605 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18606 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 164 200 273 34 92 156 284), lower := (rows 35 67 164 200 273 34 64 128 256), losses := [] }

theorem u18606 : Upper (D 7) (R 7) [34,65,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18607 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 164 200 273 36 90 154 282), lower := (rows 35 67 164 200 273 36 64 128 256), losses := [] }

theorem u18607 : Upper (D 7) (R 7) [34,65,160,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18607 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18608 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 164 200 273 40 86 150 278), lower := (rows 35 67 164 200 273 40 64 128 256), losses := [] }

theorem u18608 : Upper (D 7) (R 7) [34,65,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18608 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18609 : Route 9 := (fun mask => (mask,id))

def c18609 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18609 : Upper (D 7) (R 7) [34,65,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,257,16] 13 (by decide) (choices 1) [2,4,8] r18609 c18609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5064
  · exact u5065
  · exact u5066

def b18610 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 164 200 276 33 90 154 282), lower := (rows 35 67 164 200 276 33 64 128 256), losses := [] }

theorem u18610 : Upper (D 7) (R 7) [34,65,160,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18611 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 164 200 276 34 89 153 281), lower := (rows 35 67 164 200 276 34 64 128 256), losses := [] }

theorem u18611 : Upper (D 7) (R 7) [34,65,160,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18612 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 164 200 276 40 83 147 275), lower := (rows 35 67 164 200 276 40 64 128 256), losses := [] }

theorem u18612 : Upper (D 7) (R 7) [34,65,160,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18612 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18613 : Route 9 := (fun mask => (mask,id))

def c18613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18613 : Upper (D 7) (R 7) [34,65,160,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,260,16] 13 (by decide) (choices 1) [1,2,8] r18613 c18613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5067
  · exact u5068
  · exact u5069

def b18614 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 26 145 96 480 416 416), lower := (rows 35 70 13 26 145 96 64 128 256), losses := [] }

theorem u18614 : Upper (D 7) (R 7) [34,68,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18615 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 464, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,1)], upper := (rows 35 70 13 26 145 160 352 480 352), lower := (rows 35 70 13 26 145 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 35 6 13 63 177 160 0 160 256) }] }

theorem u18615 : Upper (D 7) (R 7) [34,68,9,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18616 : Route 9 := (fun mask => (mask,id))

def c18616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18616 : Upper (D 7) (R 7) [34,68,9,18,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,129,256] 13 (by decide) (choices 1) [32,128] r18616 c18616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5070
  · exact u5071

def b18617 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 26 176 33 448 448 448), lower := (rows 35 70 13 26 176 33 64 128 256), losses := [] }

theorem u18617 : Upper (D 7) (R 7) [34,68,9,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18618 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 26 176 96 449 385 385), lower := (rows 35 70 13 26 176 96 64 128 256), losses := [] }

theorem u18618 : Upper (D 7) (R 7) [34,68,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18619 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 26 176 160 321 449 321), lower := (rows 35 70 13 26 176 160 64 128 256), losses := [] }

theorem u18619 : Upper (D 7) (R 7) [34,68,9,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18620 : Route 9 := (fun mask => (mask,id))

def c18620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18620 : Upper (D 7) (R 7) [34,68,9,18,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,160,256] 13 (by decide) (choices 1) [1,128] r18620 c18620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5072
  · exact u5073

def b18621 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 26 208 33 480 416 416), lower := (rows 35 70 13 26 208 33 64 128 256), losses := [] }

theorem u18621 : Upper (D 7) (R 7) [34,68,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18622 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(1,7),(2,6),(4,1)], upper := (rows 35 70 13 26 208 160 353 417 289), lower := (rows 35 70 13 26 208 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 32 65 0 257), good := (rows 355 70 335 26 80 32 64 0 256) }] }

theorem u18622 : Upper (D 7) (R 7) [34,68,9,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18623 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 35 70 13 26 208 288 225 161 417), lower := (rows 35 70 13 26 208 288 64 128 256), losses := [] }

theorem u18623 : Upper (D 7) (R 7) [34,68,9,18,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18623 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18624 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 26 273 96 224 160 416), lower := (rows 35 70 13 26 273 96 64 128 256), losses := [] }

theorem u18624 : Upper (D 7) (R 7) [34,68,9,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18625 : Route 9 := (fun mask => (mask,id))

def c18625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18625 : Upper (D 7) (R 7) [34,68,9,18,257,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,257,128] 13 (by decide) (choices 1) [32,128] r18625 c18625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5074
  · exact u5075

def b18626 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 26 304 33 192 192 448), lower := (rows 35 70 13 26 304 33 64 128 256), losses := [] }

theorem u18626 : Upper (D 7) (R 7) [34,68,9,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18627 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 26 304 96 193 129 385), lower := (rows 35 70 13 26 304 96 64 128 256), losses := [] }

theorem u18627 : Upper (D 7) (R 7) [34,68,9,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18628 : Route 9 := (fun mask => (mask,id))

def c18628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18628 : Upper (D 7) (R 7) [34,68,9,18,288,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,288,128] 13 (by decide) (choices 1) [1,128] r18628 c18628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5076
  · exact u5077

def b18629 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 26 336 33 224 160 416), lower := (rows 35 70 13 26 336 33 64 128 256), losses := [] }

theorem u18629 : Upper (D 7) (R 7) [34,68,9,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18630 : Route 9 := (fun mask => (mask,id))

def c18630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18630 : Upper (D 7) (R 7) [34,68,9,18,320,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,320,128] 13 (by decide) (choices 1) [1,32,128] r18630 c18630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5078
  · exact u5079
  · exact u5080

def b18631 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 26 400 33 224 224 480), lower := (rows 35 70 13 26 400 33 64 128 256), losses := [] }

theorem u18631 : Upper (D 7) (R 7) [34,68,9,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18632 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 26 400 96 225 161 417), lower := (rows 35 70 13 26 400 96 64 128 256), losses := [] }

theorem u18632 : Upper (D 7) (R 7) [34,68,9,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18633 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(1,7),(2,6),(4,1)], upper := (rows 35 70 13 26 400 160 97 225 353), lower := (rows 35 70 13 26 400 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 35 6 13 63 432 160 0 160 256) },{ target := 7, region := (rows 1 6 4 8 16 32 65 0 257), good := (rows 355 70 335 26 272 32 64 0 256) }] }

theorem u18633 : Upper (D 7) (R 7) [34,68,9,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18634 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 56 146 33 448 448 448), lower := (rows 35 70 13 56 146 33 64 128 256), losses := [] }

theorem u18634 : Upper (D 7) (R 7) [34,68,9,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18635 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 56 146 96 449 385 385), lower := (rows 35 70 13 56 146 96 64 128 256), losses := [] }

theorem u18635 : Upper (D 7) (R 7) [34,68,9,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18636 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 70 13 56 146 160 321 449 321), lower := (rows 35 70 13 56 146 160 64 128 256), losses := [] }

theorem u18636 : Upper (D 7) (R 7) [34,68,9,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18637 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,5)], upper := (rows 35 70 13 56 146 288 193 193 449), lower := (rows 35 70 13 56 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 295 69 133 261), good := (rows 481 484 493 56 184 288 64 128 288) }] }

theorem u18637 : Upper (D 7) (R 7) [34,68,9,48,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18637 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18638 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 56 208 33 450 386 386), lower := (rows 35 70 13 56 208 33 64 128 256), losses := [] }

theorem u18638 : Upper (D 7) (R 7) [34,68,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18639 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 56 208 34 449 385 385), lower := (rows 35 70 13 56 208 34 64 128 256), losses := [] }

theorem u18639 : Upper (D 7) (R 7) [34,68,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18640 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 56 208 160 323 387 259), lower := (rows 35 70 13 56 208 160 64 128 256), losses := [] }

theorem u18640 : Upper (D 7) (R 7) [34,68,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18641 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 70 13 56 208 288 195 131 387), lower := (rows 35 70 13 56 208 288 64 128 256), losses := [] }

theorem u18641 : Upper (D 7) (R 7) [34,68,9,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18641 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18642 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 56 274 33 192 192 448), lower := (rows 35 70 13 56 274 33 64 128 256), losses := [] }

theorem u18642 : Upper (D 7) (R 7) [34,68,9,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18643 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 56 274 96 193 129 385), lower := (rows 35 70 13 56 274 96 64 128 256), losses := [] }

theorem u18643 : Upper (D 7) (R 7) [34,68,9,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18644 : Route 9 := (fun mask => (mask,id))

def c18644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18644 : Upper (D 7) (R 7) [34,68,9,48,258,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,258,128] 13 (by decide) (choices 1) [1,128] r18644 c18644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5081
  · exact u5082

def b18645 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 56 336 33 194 130 386), lower := (rows 35 70 13 56 336 33 64 128 256), losses := [] }

theorem u18645 : Upper (D 7) (R 7) [34,68,9,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18646 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 56 336 34 193 129 385), lower := (rows 35 70 13 56 336 34 64 128 256), losses := [] }

theorem u18646 : Upper (D 7) (R 7) [34,68,9,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18647 : Route 9 := (fun mask => (mask,id))

def c18647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18647 : Upper (D 7) (R 7) [34,68,9,48,320,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,320,128] 13 (by decide) (choices 1) [1,2,128] r18647 c18647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5083
  · exact u5084
  · exact u5085

def b18648 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 56 400 33 194 194 450), lower := (rows 35 70 13 56 400 33 64 128 256), losses := [] }

theorem u18648 : Upper (D 7) (R 7) [34,68,9,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18649 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 56 400 34 193 193 449), lower := (rows 35 70 13 56 400 34 64 128 256), losses := [] }

theorem u18649 : Upper (D 7) (R 7) [34,68,9,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18650 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 56 400 96 195 131 387), lower := (rows 35 70 13 56 400 96 64 128 256), losses := [] }

theorem u18650 : Upper (D 7) (R 7) [34,68,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18651 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 56 400 160 67 195 323), lower := (rows 35 70 13 56 400 160 64 128 256), losses := [] }

theorem u18651 : Upper (D 7) (R 7) [34,68,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18652 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 88 146 33 480 416 416), lower := (rows 35 70 13 88 146 33 64 128 256), losses := [] }

theorem u18652 : Upper (D 7) (R 7) [34,68,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18653 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,7),(2,6),(4,6)], upper := (rows 35 70 13 88 146 160 353 417 289), lower := (rows 35 70 13 88 146 160 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 191 0 159 287), good := (rows 435 439 445 445 435 160 0 160 256) },{ target := 7, region := (rows 1 6 4 8 16 32 65 0 257), good := (rows 355 70 335 88 18 32 64 0 256) }] }

theorem u18653 : Upper (D 7) (R 7) [34,68,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18654 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 13 88 146 288 225 161 417), lower := (rows 35 70 13 88 146 288 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 319 0 159 287), good := (rows 435 439 445 445 435 288 0 128 288) }] }

theorem u18654 : Upper (D 7) (R 7) [34,68,9,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18654 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18655 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 88 176 33 450 386 386), lower := (rows 35 70 13 88 176 33 64 128 256), losses := [] }

theorem u18655 : Upper (D 7) (R 7) [34,68,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18656 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 88 176 34 449 385 385), lower := (rows 35 70 13 88 176 34 64 128 256), losses := [] }

theorem u18656 : Upper (D 7) (R 7) [34,68,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18657 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 88 176 160 323 387 259), lower := (rows 35 70 13 88 176 160 64 128 256), losses := [] }

theorem u18657 : Upper (D 7) (R 7) [34,68,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18658 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 35 70 13 88 176 288 195 131 387), lower := (rows 35 70 13 88 176 288 64 128 256), losses := [] }

theorem u18658 : Upper (D 7) (R 7) [34,68,9,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18658 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18659 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 88 274 33 224 160 416), lower := (rows 35 70 13 88 274 33 64 128 256), losses := [] }

theorem u18659 : Upper (D 7) (R 7) [34,68,9,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18659
end Delivery.IrregularNine14.P07
