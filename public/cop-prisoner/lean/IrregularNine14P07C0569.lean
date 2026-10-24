import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0309
import IrregularNine14P07C0310
import IrregularNine14P07C0311

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34140 : Route 9 := (fun mask => (mask,id))

def c34140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34140 : Upper (D 7) (R 7) [34,65,136,260,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,160] 13 (by decide) (choices 1) [1,2,16,64] r34140 c34140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18594
  · exact u18595
  · exact u18596
  · exact u18597

def r34141 : Route 9 := (fun mask => (mask,id))

def c34141 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34141 : Upper (D 7) (R 7) [34,65,136,272,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,160] 13 (by decide) (choices 1) [1,2,4,64] r34141 c34141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18598
  · exact u18599
  · exact u18600
  · exact u18601

def r34142 : Route 9 := (fun mask => (mask,id))

def c34142 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34142 : Upper (D 7) (R 7) [34,65,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,192] 13 (by decide) (choices 1) [1,2,4,16] r34142 c34142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18602
  · exact u18603
  · exact u18604
  · exact u18605

def r34143 : Route 9 := (fun mask => (mask,id))

def c34143 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34143 : Upper (D 7) (R 7) [34,65,160,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,257] 13 (by decide) (choices 1) [2,4,8,16] r34143 c34143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18606
  · exact u18607
  · exact u18608
  · exact u18609

def r34144 : Route 9 := (fun mask => (mask,id))

def c34144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34144 : Upper (D 7) (R 7) [34,65,160,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,260] 13 (by decide) (choices 1) [1,2,8,16] r34144 c34144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18610
  · exact u18611
  · exact u18612
  · exact u18613

def b34145 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 13 26 49 480 448 448 448), lower := (rows 35 70 13 26 49 32 64 128 256), losses := [] }

theorem u34145 : Upper (D 7) (R 7) [34,68,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34146 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 14, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 13 26 81 416 480 416 416), lower := (rows 35 70 13 26 81 32 64 128 256), losses := [] }

theorem u34146 : Upper (D 7) (R 7) [34,68,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34147 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 26 112 417 449 385 385), lower := (rows 35 70 13 26 112 32 64 128 256), losses := [] }

theorem u34147 : Upper (D 7) (R 7) [34,68,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34148 : Route 9 := (fun mask => (mask,id))

def c34148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u34148 : Upper (D 7) (R 7) [34,68,9,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,129] 13 (by decide) (choices 1) [64,128,256] r34148 c34148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18614
  · exact u18615
  · exact u18616

def r34149 : Route 9 := (fun mask => (mask,id))

def c34149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u34149 : Upper (D 7) (R 7) [34,68,9,18,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,160] 13 (by decide) (choices 1) [1,64,128,256] r34149 c34149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18617
  · exact u18618
  · exact u18619
  · exact u18620

def r34150 : Route 9 := (fun mask => (mask,id))

def c34150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34150 : Upper (D 7) (R 7) [34,68,9,18,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,192] 13 (by decide) (choices 1) [1,128,256] r34150 c34150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18621
  · exact u18622
  · exact u18623

def r34151 : Route 9 := (fun mask => (mask,id))

def c34151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34151 : Upper (D 7) (R 7) [34,68,9,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,257] 13 (by decide) (choices 1) [64,128] r34151 c34151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18624
  · exact u18625

def r34152 : Route 9 := (fun mask => (mask,id))

def c34152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34152 : Upper (D 7) (R 7) [34,68,9,18,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,288] 13 (by decide) (choices 1) [1,64,128] r34152 c34152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18626
  · exact u18627
  · exact u18628

def r34153 : Route 9 := (fun mask => (mask,id))

def c34153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34153 : Upper (D 7) (R 7) [34,68,9,18,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,320] 13 (by decide) (choices 1) [1,128] r34153 c34153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18629
  · exact u18630

def r34154 : Route 9 := (fun mask => (mask,id))

def c34154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34154 : Upper (D 7) (R 7) [34,68,9,18,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,384] 13 (by decide) (choices 1) [1,64,128] r34154 c34154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18631
  · exact u18632
  · exact u18633

def b34155 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 13 56 19 480 448 448 448), lower := (rows 35 70 13 56 19 32 64 128 256), losses := [] }

theorem u34155 : Upper (D 7) (R 7) [34,68,9,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34156 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 417, targets := 64 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(1,5),(4,5)], upper := (rows 35 70 13 56 81 418 450 386 386), lower := (rows 35 70 13 56 81 32 64 128 256), losses := [] }

theorem u34156 : Upper (D 7) (R 7) [34,68,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34157 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 56 82 417 449 385 385), lower := (rows 35 70 13 56 82 32 64 128 256), losses := [] }

theorem u34157 : Upper (D 7) (R 7) [34,68,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34158 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 56 145 482 450 450 450), lower := (rows 35 70 13 56 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 56 504 32 64 128 256) }] }

theorem u34158 : Upper (D 7) (R 7) [34,68,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34159 : Route 9 := (fun mask => (mask,id))

def c34159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u34159 : Upper (D 7) (R 7) [34,68,9,48,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,130] 13 (by decide) (choices 1) [1,64,128,256] r34159 c34159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18634
  · exact u18635
  · exact u18636
  · exact u18637

def r34160 : Route 9 := (fun mask => (mask,id))

def c34160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34160 : Upper (D 7) (R 7) [34,68,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,192] 13 (by decide) (choices 1) [1,2,128,256] r34160 c34160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18638
  · exact u18639
  · exact u18640
  · exact u18641

def b34161 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 56 273 226 194 194 450), lower := (rows 35 70 13 56 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 56 504 32 64 128 256) }] }

theorem u34161 : Upper (D 7) (R 7) [34,68,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34162 : Route 9 := (fun mask => (mask,id))

def c34162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34162 : Upper (D 7) (R 7) [34,68,9,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,258] 13 (by decide) (choices 1) [1,64,128] r34162 c34162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18642
  · exact u18643
  · exact u18644

def r34163 : Route 9 := (fun mask => (mask,id))

def c34163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34163 : Upper (D 7) (R 7) [34,68,9,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,320] 13 (by decide) (choices 1) [1,2,128] r34163 c34163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18645
  · exact u18646
  · exact u18647

def r34164 : Route 9 := (fun mask => (mask,id))

def c34164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34164 : Upper (D 7) (R 7) [34,68,9,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,384] 13 (by decide) (choices 1) [1,2,64,128] r34164 c34164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18648
  · exact u18649
  · exact u18650
  · exact u18651

def b34165 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 88 19 416 480 416 416), lower := (rows 35 70 13 88 19 32 64 128 256), losses := [] }

theorem u34165 : Upper (D 7) (R 7) [34,68,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34166 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 13 88 49 418 450 386 386), lower := (rows 35 70 13 88 49 32 64 128 256), losses := [] }

theorem u34166 : Upper (D 7) (R 7) [34,68,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34167 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 13 88 50 417 449 385 385), lower := (rows 35 70 13 88 50 32 64 128 256), losses := [] }

theorem u34167 : Upper (D 7) (R 7) [34,68,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34168 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 35 70 13 88 145 418 482 418 418), lower := (rows 35 70 13 88 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 88 504 32 64 128 256) }] }

theorem u34168 : Upper (D 7) (R 7) [34,68,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34169 : Route 9 := (fun mask => (mask,id))

def c34169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34169 : Upper (D 7) (R 7) [34,68,9,80,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,130] 13 (by decide) (choices 1) [1,128,256] r34169 c34169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18652
  · exact u18653
  · exact u18654

def r34170 : Route 9 := (fun mask => (mask,id))

def c34170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34170 : Upper (D 7) (R 7) [34,68,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,160] 13 (by decide) (choices 1) [1,2,128,256] r34170 c34170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18655
  · exact u18656
  · exact u18657
  · exact u18658

def b34171 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 35 70 13 88 273 162 226 162 418), lower := (rows 35 70 13 88 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 88 504 32 64 128 256) }] }

theorem u34171 : Upper (D 7) (R 7) [34,68,9,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34172 : Route 9 := (fun mask => (mask,id))

def c34172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34172 : Upper (D 7) (R 7) [34,68,9,80,258] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,258] 13 (by decide) (choices 1) [1,128] r34172 c34172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18659
  · exact u18660

def r34173 : Route 9 := (fun mask => (mask,id))

def c34173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34173 : Upper (D 7) (R 7) [34,68,9,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,288] 13 (by decide) (choices 1) [1,2,128] r34173 c34173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18661
  · exact u18662
  · exact u18663

def r34174 : Route 9 := (fun mask => (mask,id))

def c34174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34174 : Upper (D 7) (R 7) [34,68,9,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,384] 13 (by decide) (choices 1) [1,2,128] r34174 c34174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18664
  · exact u18665
  · exact u18666

def b34175 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 70 13 138 49 496 464 464 464), lower := (rows 35 70 13 138 49 32 64 128 256), losses := [] }

theorem u34175 : Upper (D 7) (R 7) [34,68,9,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34176 : Route 9 := (fun mask => (mask,id))

def c34176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34176 : Upper (D 7) (R 7) [34,68,9,130,65] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,65] 13 (by decide) (choices 1) [16,128,256] r34176 c34176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18667
  · exact u18668
  · exact u18669

def r34177 : Route 9 := (fun mask => (mask,id))

def c34177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34177 : Upper (D 7) (R 7) [34,68,9,130,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,96] 13 (by decide) (choices 1) [1,16,128,256] r34177 c34177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18670
  · exact u18671
  · exact u18672
  · exact u18673

def r34178 : Route 9 := (fun mask => (mask,id))

def c34178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34178 : Upper (D 7) (R 7) [34,68,9,130,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,129] 13 (by decide) (choices 1) [16,64,256] r34178 c34178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18674
  · exact u18675
  · exact u18676

def r34179 : Route 9 := (fun mask => (mask,id))

def c34179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34179 : Upper (D 7) (R 7) [34,68,9,130,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,160] 13 (by decide) (choices 1) [1,16,64,256] r34179 c34179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18677
  · exact u18678
  · exact u18679
  · exact u18680

def r34180 : Route 9 := (fun mask => (mask,id))

def c34180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34180 : Upper (D 7) (R 7) [34,68,9,130,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,192] 13 (by decide) (choices 1) [1,16,256] r34180 c34180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18681
  · exact u18682
  · exact u18683

def r34181 : Route 9 := (fun mask => (mask,id))

def c34181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34181 : Upper (D 7) (R 7) [34,68,9,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,257] 13 (by decide) (choices 1) [16,64,128] r34181 c34181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18684
  · exact u18685
  · exact u18686

def r34182 : Route 9 := (fun mask => (mask,id))

def c34182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34182 : Upper (D 7) (R 7) [34,68,9,130,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,288] 13 (by decide) (choices 1) [1,16,64,128] r34182 c34182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18687
  · exact u18688
  · exact u18689
  · exact u18690

def r34183 : Route 9 := (fun mask => (mask,id))

def c34183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34183 : Upper (D 7) (R 7) [34,68,9,130,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,320] 13 (by decide) (choices 1) [1,16,128] r34183 c34183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18691
  · exact u18692
  · exact u18693

def r34184 : Route 9 := (fun mask => (mask,id))

def c34184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34184 : Upper (D 7) (R 7) [34,68,9,130,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,384] 13 (by decide) (choices 1) [1,16,64] r34184 c34184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18694
  · exact u18695
  · exact u18696

def b34185 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 152 19 480 480 480 480), lower := (rows 35 70 13 152 19 32 64 128 256), losses := [] }

theorem u34185 : Upper (D 7) (R 7) [34,68,9,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34186 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 13 152 49 482 450 450 450), lower := (rows 35 70 13 152 49 32 64 128 256), losses := [] }

theorem u34186 : Upper (D 7) (R 7) [34,68,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34187 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 13 152 50 481 449 449 449), lower := (rows 35 70 13 152 50 32 64 128 256), losses := [] }

theorem u34187 : Upper (D 7) (R 7) [34,68,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34188 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 417, targets := 64 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 35 70 13 152 81 418 482 418 418), lower := (rows 35 70 13 152 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 152 504 32 64 128 256) },{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 423 429 156 445 32 0 128 256) }] }

theorem u34188 : Upper (D 7) (R 7) [34,68,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34189 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 152 82 417 481 417 417), lower := (rows 35 70 13 152 82 32 64 128 256), losses := [] }

theorem u34189 : Upper (D 7) (R 7) [34,68,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34190 : Route 9 := (fun mask => (mask,id))

def c34190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34190 : Upper (D 7) (R 7) [34,68,9,144,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,96] 13 (by decide) (choices 1) [1,2,128,256] r34190 c34190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18697
  · exact u18698
  · exact u18699
  · exact u18700

def b34191 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 35 70 13 152 145 354 354 482 354), lower := (rows 35 70 13 152 145 32 64 128 256), losses := [] }

theorem u34191 : Upper (D 7) (R 7) [34,68,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34192 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 13 152 146 353 353 481 353), lower := (rows 35 70 13 152 146 32 64 128 256), losses := [] }

theorem u34192 : Upper (D 7) (R 7) [34,68,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34193 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 13 152 176 355 323 451 323), lower := (rows 35 70 13 152 176 32 64 128 256), losses := [] }

theorem u34193 : Upper (D 7) (R 7) [34,68,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34194 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 13 152 208 291 355 419 291), lower := (rows 35 70 13 152 208 32 64 128 256), losses := [] }

theorem u34194 : Upper (D 7) (R 7) [34,68,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34195 : Route 9 := (fun mask => (mask,id))

def c34195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34195 : Upper (D 7) (R 7) [34,68,9,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,257] 13 (by decide) (choices 1) [2,64,128] r34195 c34195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18701
  · exact u18702
  · exact u18703

def r34196 : Route 9 := (fun mask => (mask,id))

def c34196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34196 : Upper (D 7) (R 7) [34,68,9,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,258] 13 (by decide) (choices 1) [1,64,128] r34196 c34196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18704
  · exact u18705
  · exact u18706

def r34197 : Route 9 := (fun mask => (mask,id))

def c34197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34197 : Upper (D 7) (R 7) [34,68,9,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,288] 13 (by decide) (choices 1) [1,2,64,128] r34197 c34197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18707
  · exact u18708
  · exact u18709
  · exact u18710

def r34198 : Route 9 := (fun mask => (mask,id))

def c34198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34198 : Upper (D 7) (R 7) [34,68,9,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,320] 13 (by decide) (choices 1) [1,2,128] r34198 c34198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18711
  · exact u18712
  · exact u18713

def b34199 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 13 152 400 99 99 227 355), lower := (rows 35 70 13 152 400 32 64 128 256), losses := [] }

theorem u34199 : Upper (D 7) (R 7) [34,68,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34199
end Delivery.IrregularNine14.P07
