import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0293
import IrregularNine14P06C0294
import IrregularNine14P06C0295

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34140 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 100 25 22 357 325 453 325), lower := (rows 11 162 100 25 22 32 64 128 256), losses := [] }

theorem u34140 : Upper (D 6) (R 6) [10,160,96,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34141 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 100 25 81 294 326 390 262), lower := (rows 11 162 100 25 81 32 64 128 256), losses := [] }

theorem u34141 : Upper (D 6) (R 6) [10,160,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34142 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 25 82 293 325 389 261), lower := (rows 11 162 100 25 82 32 64 128 256), losses := [] }

theorem u34142 : Upper (D 6) (R 6) [10,160,96,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34143 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 100 25 84 295 327 391 263), lower := (rows 11 162 100 25 84 32 64 128 256), losses := [] }

theorem u34143 : Upper (D 6) (R 6) [10,160,96,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34144 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 100 25 273 102 70 198 326), lower := (rows 11 162 100 25 273 32 64 128 256), losses := [] }

theorem u34144 : Upper (D 6) (R 6) [10,160,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34145 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 25 274 101 69 197 325), lower := (rows 11 162 100 25 274 32 64 128 256), losses := [] }

theorem u34145 : Upper (D 6) (R 6) [10,160,96,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34146 : Route 9 := (fun mask => (mask,id))

def c34146 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34146 : Upper (D 6) (R 6) [10,160,96,17,260] 13 := by
  apply FastRouting.sound _ _ [10,160,96,17,260] 13 (by decide) (choices 1) [1,2,4,64] r34146 c34146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17611
  · exact u17612
  · exact u17613
  · exact u17614

def r34147 : Route 9 := (fun mask => (mask,id))

def c34147 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34147 : Upper (D 6) (R 6) [10,160,96,17,320] 13 := by
  apply FastRouting.sound _ _ [10,160,96,17,320] 13 (by decide) (choices 1) [1,2,4] r34147 c34147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17615
  · exact u17616
  · exact u17617

def b34148 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 28 19 357 325 453 325), lower := (rows 11 162 100 28 19 32 64 128 256), losses := [] }

theorem u34148 : Upper (D 6) (R 6) [10,160,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34149 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 100 28 21 355 323 451 323), lower := (rows 11 162 100 28 21 32 64 128 256), losses := [] }

theorem u34149 : Upper (D 6) (R 6) [10,160,96,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34150 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 483, targets := 4 },{ cop := 4, region := 8, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 100 28 22 353 321 449 321), lower := (rows 11 162 100 28 22 32 64 128 256), losses := [] }

theorem u34150 : Upper (D 6) (R 6) [10,160,96,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34151 : Route 9 := (fun mask => (mask,id))

def c34151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34151 : Upper (D 6) (R 6) [10,160,96,20,65] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,65] 13 (by decide) (choices 1) [1,2,4,256] r34151 c34151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17618
  · exact u17619
  · exact u17620
  · exact u17621

def b34152 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 100 28 82 293 325 389 261), lower := (rows 11 162 100 28 82 32 64 128 256), losses := [] }

theorem u34152 : Upper (D 6) (R 6) [10,160,96,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34153 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 100 28 84 291 323 387 259), lower := (rows 11 162 100 28 84 32 64 128 256), losses := [] }

theorem u34153 : Upper (D 6) (R 6) [10,160,96,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34154 : Route 9 := (fun mask => (mask,id))

def c34154 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34154 : Upper (D 6) (R 6) [10,160,96,20,257] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,257] 13 (by decide) (choices 1) [1,2,4,64] r34154 c34154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17622
  · exact u17623
  · exact u17624
  · exact u17625

def r34155 : Route 9 := (fun mask => (mask,id))

def c34155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34155 : Upper (D 6) (R 6) [10,160,96,20,258] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,258] 13 (by decide) (choices 1) [1,4,64] r34155 c34155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17626
  · exact u17627
  · exact u17628

def b34156 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 100 28 276 99 67 195 323), lower := (rows 11 162 100 28 276 32 64 128 256), losses := [] }

theorem u34156 : Upper (D 6) (R 6) [10,160,96,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34157 : Route 9 := (fun mask => (mask,id))

def c34157 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34157 : Upper (D 6) (R 6) [10,160,96,20,320] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,320] 13 (by decide) (choices 1) [1,2,4] r34157 c34157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17629
  · exact u17630
  · exact u17631

def b34158 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 73 19 308 340 404 276), lower := (rows 11 162 100 73 19 32 64 128 256), losses := [] }

theorem u34158 : Upper (D 6) (R 6) [10,160,96,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34159 : PairBound 9 := { available := 278, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 100 73 21 310 342 406 278), lower := (rows 11 162 100 73 21 32 64 128 256), losses := [] }

theorem u34159 : Upper (D 6) (R 6) [10,160,96,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34160 : Route 9 := (fun mask => (mask,id))

def c34160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34160 : Upper (D 6) (R 6) [10,160,96,65,6] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,6] 13 (by decide) (choices 1) [1,4,16,256] r34160 c34160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17632
  · exact u17633
  · exact u17634
  · exact u17635

def r34161 : Route 9 := (fun mask => (mask,id))

def c34161 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34161 : Upper (D 6) (R 6) [10,160,96,65,257] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,257] 13 (by decide) (choices 1) [2,4,16] r34161 c34161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17636
  · exact u17637
  · exact u17638

def r34162 : Route 9 := (fun mask => (mask,id))

def c34162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34162 : Upper (D 6) (R 6) [10,160,96,65,258] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,258] 13 (by decide) (choices 1) [1,4,16] r34162 c34162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17639
  · exact u17640
  · exact u17641

def r34163 : Route 9 := (fun mask => (mask,id))

def c34163 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34163 : Upper (D 6) (R 6) [10,160,96,65,260] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,260] 13 (by decide) (choices 1) [1,2,4,16] r34163 c34163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17642
  · exact u17643
  · exact u17644
  · exact u17645

def b34164 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 88 19 293 325 389 261), lower := (rows 11 162 100 88 19 32 64 128 256), losses := [] }

theorem u34164 : Upper (D 6) (R 6) [10,160,96,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34165 : Route 9 := (fun mask => (mask,id))

def c34165 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34165 : Upper (D 6) (R 6) [10,160,96,80,5] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,5] 13 (by decide) (choices 1) [1,2,4,256] r34165 c34165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17646
  · exact u17647
  · exact u17648
  · exact u17649

def b34166 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 162 100 88 22 293 325 389 261), lower := (rows 11 162 100 88 22 32 64 128 256), losses := [] }

theorem u34166 : Upper (D 6) (R 6) [10,160,96,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34167 : Route 9 := (fun mask => (mask,id))

def c34167 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34167 : Upper (D 6) (R 6) [10,160,96,80,257] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,257] 13 (by decide) (choices 1) [1,2,4] r34167 c34167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17650
  · exact u17651
  · exact u17652

def r34168 : Route 9 := (fun mask => (mask,id))

def c34168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34168 : Upper (D 6) (R 6) [10,160,96,80,258] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,258] 13 (by decide) (choices 1) [1,4] r34168 c34168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17653
  · exact u17654

def r34169 : Route 9 := (fun mask => (mask,id))

def c34169 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34169 : Upper (D 6) (R 6) [10,160,96,80,260] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,260] 13 (by decide) (choices 1) [1,2,4] r34169 c34169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17655
  · exact u17656
  · exact u17657

def b34170 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 265 19 116 84 212 340), lower := (rows 11 162 100 265 19 32 64 128 256), losses := [] }

theorem u34170 : Upper (D 6) (R 6) [10,160,96,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34171 : Route 9 := (fun mask => (mask,id))

def c34171 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34171 : Upper (D 6) (R 6) [10,160,96,257,5] 13 := by
  apply FastRouting.sound _ _ [10,160,96,257,5] 13 (by decide) (choices 1) [2,4,16,64] r34171 c34171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17658
  · exact u17659
  · exact u17660
  · exact u17661

def r34172 : Route 9 := (fun mask => (mask,id))

def c34172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34172 : Upper (D 6) (R 6) [10,160,96,257,6] 13 := by
  apply FastRouting.sound _ _ [10,160,96,257,6] 13 (by decide) (choices 1) [1,4,16,64] r34172 c34172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17662
  · exact u17663
  · exact u17664
  · exact u17665

def r34173 : Route 9 := (fun mask => (mask,id))

def c34173 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34173 : Upper (D 6) (R 6) [10,160,96,257,65] 13 := by
  apply FastRouting.sound _ _ [10,160,96,257,65] 13 (by decide) (choices 1) [2,4,16] r34173 c34173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17666
  · exact u17667
  · exact u17668

def r34174 : Route 9 := (fun mask => (mask,id))

def c34174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34174 : Upper (D 6) (R 6) [10,160,96,257,66] 13 := by
  apply FastRouting.sound _ _ [10,160,96,257,66] 13 (by decide) (choices 1) [1,4,16] r34174 c34174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17669
  · exact u17670
  · exact u17671

def b34175 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 100 265 84 55 87 151 279), lower := (rows 11 162 100 265 84 32 64 128 256), losses := [] }

theorem u34175 : Upper (D 6) (R 6) [10,160,96,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34176 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 268 19 117 85 213 341), lower := (rows 11 162 100 268 19 32 64 128 256), losses := [] }

theorem u34176 : Upper (D 6) (R 6) [10,160,96,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34177 : Route 9 := (fun mask => (mask,id))

def c34177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34177 : Upper (D 6) (R 6) [10,160,96,260,5] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,5] 13 (by decide) (choices 1) [1,2,16,64] r34177 c34177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17672
  · exact u17673
  · exact u17674
  · exact u17675

def r34178 : Route 9 := (fun mask => (mask,id))

def c34178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34178 : Upper (D 6) (R 6) [10,160,96,260,6] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,6] 13 (by decide) (choices 1) [1,16,64] r34178 c34178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17676
  · exact u17677
  · exact u17678

def r34179 : Route 9 := (fun mask => (mask,id))

def c34179 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34179 : Upper (D 6) (R 6) [10,160,96,260,65] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,65] 13 (by decide) (choices 1) [1,2,4,16] r34179 c34179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17679
  · exact u17680
  · exact u17681
  · exact u17682

def r34180 : Route 9 := (fun mask => (mask,id))

def c34180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34180 : Upper (D 6) (R 6) [10,160,96,260,66] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,66] 13 (by decide) (choices 1) [1,4,16] r34180 c34180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17683
  · exact u17684
  · exact u17685

def b34181 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 100 268 84 51 83 147 275), lower := (rows 11 162 100 268 84 32 64 128 256), losses := [] }

theorem u34181 : Upper (D 6) (R 6) [10,160,96,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34182 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 280 19 101 69 197 325), lower := (rows 11 162 100 280 19 32 64 128 256), losses := [] }

theorem u34182 : Upper (D 6) (R 6) [10,160,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34183 : Route 9 := (fun mask => (mask,id))

def c34183 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34183 : Upper (D 6) (R 6) [10,160,96,272,5] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272,5] 13 (by decide) (choices 1) [1,2,4,64] r34183 c34183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17686
  · exact u17687
  · exact u17688
  · exact u17689

def b34184 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 162 100 280 22 101 69 197 325), lower := (rows 11 162 100 280 22 32 64 128 256), losses := [] }

theorem u34184 : Upper (D 6) (R 6) [10,160,96,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34185 : Route 9 := (fun mask => (mask,id))

def c34185 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34185 : Upper (D 6) (R 6) [10,160,96,272,65] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272,65] 13 (by decide) (choices 1) [1,2,4] r34185 c34185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17690
  · exact u17691
  · exact u17692

def r34186 : Route 9 := (fun mask => (mask,id))

def c34186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34186 : Upper (D 6) (R 6) [10,160,96,272,66] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272,66] 13 (by decide) (choices 1) [1,4] r34186 c34186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17693
  · exact u17694

def b34187 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 100 280 84 39 71 135 263), lower := (rows 11 162 100 280 84 32 64 128 256), losses := [] }

theorem u34187 : Upper (D 6) (R 6) [10,160,96,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34188 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 328 19 53 85 149 277), lower := (rows 11 162 100 328 19 32 64 128 256), losses := [] }

theorem u34188 : Upper (D 6) (R 6) [10,160,96,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34189 : Route 9 := (fun mask => (mask,id))

def c34189 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34189 : Upper (D 6) (R 6) [10,160,96,320,5] 13 := by
  apply FastRouting.sound _ _ [10,160,96,320,5] 13 (by decide) (choices 1) [1,2,4,16] r34189 c34189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17695
  · exact u17696
  · exact u17697
  · exact u17698

def r34190 : Route 9 := (fun mask => (mask,id))

def c34190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34190 : Upper (D 6) (R 6) [10,160,96,320,6] 13 := by
  apply FastRouting.sound _ _ [10,160,96,320,6] 13 (by decide) (choices 1) [1,4,16] r34190 c34190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17699
  · exact u17700
  · exact u17701

def b34191 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 261 25 22 100 100 228 356), lower := (rows 11 162 261 25 22 32 64 128 256), losses := [] }

theorem u34191 : Upper (D 6) (R 6) [10,160,257,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34192 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 261 25 50 100 68 196 324), lower := (rows 11 162 261 25 50 32 64 128 256), losses := [] }

theorem u34192 : Upper (D 6) (R 6) [10,160,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34193 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 162 261 25 52 102 70 198 326), lower := (rows 11 162 261 25 52 32 64 128 256), losses := [] }

theorem u34193 : Upper (D 6) (R 6) [10,160,257,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34194 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 261 25 82 100 100 228 356), lower := (rows 11 162 261 25 82 32 64 128 256), losses := [] }

theorem u34194 : Upper (D 6) (R 6) [10,160,257,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34195 : Route 9 := (fun mask => (mask,id))

def c34195 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34195 : Upper (D 6) (R 6) [10,160,257,17,68] 13 := by
  apply FastRouting.sound _ _ [10,160,257,17,68] 13 (by decide) (choices 1) [2,4,64] r34195 c34195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17702
  · exact u17703
  · exact u17704

def b34196 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 162 261 25 112 102 70 198 326), lower := (rows 11 162 261 25 112 32 64 128 256), losses := [] }

theorem u34196 : Upper (D 6) (R 6) [10,160,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34197 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 261 28 19 100 100 228 356), lower := (rows 11 162 261 28 19 32 64 128 256), losses := [] }

theorem u34197 : Upper (D 6) (R 6) [10,160,257,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34198 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 162 261 28 21 98 98 226 354), lower := (rows 11 162 261 28 21 32 64 128 256), losses := [] }

theorem u34198 : Upper (D 6) (R 6) [10,160,257,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34199 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 261 28 22 97 97 225 353), lower := (rows 11 162 261 28 22 32 64 128 256), losses := [] }

theorem u34199 : Upper (D 6) (R 6) [10,160,257,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34199
end Delivery.IrregularNine14.P06
