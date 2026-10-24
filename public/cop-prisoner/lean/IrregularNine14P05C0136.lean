import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0076
import IrregularNine14P05C0077
import IrregularNine14P05C0078

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8160 : Route 9 := (fun mask => (mask,id))

def c8160 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8160 : Upper (D 5) (R 5) [34,68,48,384,9] 13 := by
  apply FastRouting.sound _ _ [34,68,48,384,9] 13 (by decide) (choices 1) [1,2,4,8] r8160 c8160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4612
  · exact u4613
  · exact u4614
  · exact u4615

def r8161 : Route 9 := (fun mask => (mask,id))

def c8161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8161 : Upper (D 5) (R 5) [34,68,48,384,10] 13 := by
  apply FastRouting.sound _ _ [34,68,48,384,10] 13 (by decide) (choices 1) [1,4,8] r8161 c8161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4616
  · exact u4617
  · exact u4618

def b8162 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 425, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 392 28 43 75 139 267), lower := (rows 35 70 52 392 28 32 64 128 256), losses := [] }

theorem u8162 : Upper (D 5) (R 5) [34,68,48,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8163 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 24, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 56 19 300 332 396 268), lower := (rows 35 70 133 56 19 32 64 128 256), losses := [] }

theorem u8163 : Upper (D 5) (R 5) [34,68,129,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8164 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 70 133 56 21 298 330 394 266), lower := (rows 35 70 133 56 21 32 64 128 256), losses := [] }

theorem u8164 : Upper (D 5) (R 5) [34,68,129,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8165 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 133 56 22 297 329 393 265), lower := (rows 35 70 133 56 22 32 64 128 256), losses := [] }

theorem u8165 : Upper (D 5) (R 5) [34,68,129,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8166 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 133 56 25 302 334 398 270), lower := (rows 35 70 133 56 25 32 64 128 256), losses := [] }

theorem u8166 : Upper (D 5) (R 5) [34,68,129,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8167 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 56 26 301 333 397 269), lower := (rows 35 70 133 56 26 32 64 128 256), losses := [] }

theorem u8167 : Upper (D 5) (R 5) [34,68,129,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8168 : Route 9 := (fun mask => (mask,id))

def c8168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8168 : Upper (D 5) (R 5) [34,68,129,48,12] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,12] 13 (by decide) (choices 1) [1,2,8,256] r8168 c8168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4619
  · exact u4620
  · exact u4621
  · exact u4622

def r8169 : Route 9 := (fun mask => (mask,id))

def c8169 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8169 : Upper (D 5) (R 5) [34,68,129,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,257] 13 (by decide) (choices 1) [2,4,8] r8169 c8169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4623
  · exact u4624
  · exact u4625

def r8170 : Route 9 := (fun mask => (mask,id))

def c8170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8170 : Upper (D 5) (R 5) [34,68,129,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,258] 13 (by decide) (choices 1) [1,4,8] r8170 c8170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4626
  · exact u4627
  · exact u4628

def r8171 : Route 9 := (fun mask => (mask,id))

def c8171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8171 : Upper (D 5) (R 5) [34,68,129,48,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,260] 13 (by decide) (choices 1) [1,2,8] r8171 c8171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4629
  · exact u4630
  · exact u4631

def r8172 : Route 9 := (fun mask => (mask,id))

def c8172 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8172 : Upper (D 5) (R 5) [34,68,129,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,264] 13 (by decide) (choices 1) [1,2,4,8] r8172 c8172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4632
  · exact u4633
  · exact u4634
  · exact u4635

def b8173 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 133 265 22 56 120 184 312), lower := (rows 35 70 133 265 22 32 64 128 256), losses := [] }

theorem u8173 : Upper (D 5) (R 5) [34,68,129,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8174 : Route 9 := (fun mask => (mask,id))

def c8174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8174 : Upper (D 5) (R 5) [34,68,129,257,10] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,10] 13 (by decide) (choices 1) [4,8,16] r8174 c8174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4636
  · exact u4637
  · exact u4638

def r8175 : Route 9 := (fun mask => (mask,id))

def c8175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8175 : Upper (D 5) (R 5) [34,68,129,257,12] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,12] 13 (by decide) (choices 1) [2,8,16] r8175 c8175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4639
  · exact u4640
  · exact u4641

def b8176 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 133 265 50 60 92 156 284), lower := (rows 35 70 133 265 50 32 64 128 256), losses := [] }

theorem u8176 : Upper (D 5) (R 5) [34,68,129,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8177 : Route 9 := (fun mask => (mask,id))

def c8177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8177 : Upper (D 5) (R 5) [34,68,129,257,36] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,36] 13 (by decide) (choices 1) [2,8,16] r8177 c8177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4642
  · exact u4643
  · exact u4644

def r8178 : Route 9 := (fun mask => (mask,id))

def c8178 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8178 : Upper (D 5) (R 5) [34,68,129,257,40] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,40] 13 (by decide) (choices 1) [2,4,8,16] r8178 c8178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4645
  · exact u4646
  · exact u4647
  · exact u4648

def b8179 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 70 133 266 21 56 120 184 312), lower := (rows 35 70 133 266 21 32 64 128 256), losses := [] }

theorem u8179 : Upper (D 5) (R 5) [34,68,129,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8179
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8180 : Route 9 := (fun mask => (mask,id))

def c8180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8180 : Upper (D 5) (R 5) [34,68,129,258,9] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258,9] 13 (by decide) (choices 1) [4,8,16] r8180 c8180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4649
  · exact u4650
  · exact u4651

def r8181 : Route 9 := (fun mask => (mask,id))

def c8181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8181 : Upper (D 5) (R 5) [34,68,129,258,12] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258,12] 13 (by decide) (choices 1) [1,8,16] r8181 c8181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4652
  · exact u4653
  · exact u4654

def b8182 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 133 266 49 60 92 156 284), lower := (rows 35 70 133 266 49 32 64 128 256), losses := [] }

theorem u8182 : Upper (D 5) (R 5) [34,68,129,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8182
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8183 : Route 9 := (fun mask => (mask,id))

def c8183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8183 : Upper (D 5) (R 5) [34,68,129,258,36] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258,36] 13 (by decide) (choices 1) [1,8,16] r8183 c8183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4655
  · exact u4656
  · exact u4657

def r8184 : Route 9 := (fun mask => (mask,id))

def c8184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8184 : Upper (D 5) (R 5) [34,68,129,258,40] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258,40] 13 (by decide) (choices 1) [1,4,8,16] r8184 c8184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4658
  · exact u4659
  · exact u4660
  · exact u4661

def b8185 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 133 268 19 56 120 184 312), lower := (rows 35 70 133 268 19 32 64 128 256), losses := [] }

theorem u8185 : Upper (D 5) (R 5) [34,68,129,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8186 : Route 9 := (fun mask => (mask,id))

def c8186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8186 : Upper (D 5) (R 5) [34,68,129,260,9] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260,9] 13 (by decide) (choices 1) [2,8,16] r8186 c8186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4662
  · exact u4663
  · exact u4664

def r8187 : Route 9 := (fun mask => (mask,id))

def c8187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8187 : Upper (D 5) (R 5) [34,68,129,260,10] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260,10] 13 (by decide) (choices 1) [1,8,16] r8187 c8187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4665
  · exact u4666
  · exact u4667

def b8188 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 133 268 49 58 90 154 282), lower := (rows 35 70 133 268 49 32 64 128 256), losses := [] }

theorem u8188 : Upper (D 5) (R 5) [34,68,129,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8189 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 133 268 50 57 89 153 281), lower := (rows 35 70 133 268 50 32 64 128 256), losses := [] }

theorem u8189 : Upper (D 5) (R 5) [34,68,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8189
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8190 : Route 9 := (fun mask => (mask,id))

def c8190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8190 : Upper (D 5) (R 5) [34,68,129,260,40] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260,40] 13 (by decide) (choices 1) [1,2,8,16] r8190 c8190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4668
  · exact u4669
  · exact u4670
  · exact u4671

def b8191 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 133 280 19 44 108 172 300), lower := (rows 35 70 133 280 19 32 64 128 256), losses := [] }

theorem u8191 : Upper (D 5) (R 5) [34,68,129,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8192 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 70 133 280 21 42 106 170 298), lower := (rows 35 70 133 280 21 32 64 128 256), losses := [] }

theorem u8192 : Upper (D 5) (R 5) [34,68,129,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8193 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 133 280 22 41 105 169 297), lower := (rows 35 70 133 280 22 32 64 128 256), losses := [] }

theorem u8193 : Upper (D 5) (R 5) [34,68,129,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8194 : Route 9 := (fun mask => (mask,id))

def c8194 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8194 : Upper (D 5) (R 5) [34,68,129,272,9] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272,9] 13 (by decide) (choices 1) [2,4,8] r8194 c8194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4672
  · exact u4673
  · exact u4674

def r8195 : Route 9 := (fun mask => (mask,id))

def c8195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8195 : Upper (D 5) (R 5) [34,68,129,272,10] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272,10] 13 (by decide) (choices 1) [1,4,8] r8195 c8195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4675
  · exact u4676
  · exact u4677

def r8196 : Route 9 := (fun mask => (mask,id))

def c8196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8196 : Upper (D 5) (R 5) [34,68,129,272,12] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272,12] 13 (by decide) (choices 1) [1,2,8] r8196 c8196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4678
  · exact u4679
  · exact u4680

def b8197 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 133 280 49 46 78 142 270), lower := (rows 35 70 133 280 49 32 64 128 256), losses := [] }

theorem u8197 : Upper (D 5) (R 5) [34,68,129,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8198 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 133 280 50 45 77 141 269), lower := (rows 35 70 133 280 50 32 64 128 256), losses := [] }

theorem u8198 : Upper (D 5) (R 5) [34,68,129,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8199 : Route 9 := (fun mask => (mask,id))

def c8199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8199 : Upper (D 5) (R 5) [34,68,129,272,36] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272,36] 13 (by decide) (choices 1) [1,2,8] r8199 c8199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4681
  · exact u4682
  · exact u4683

def r8200 : Route 9 := (fun mask => (mask,id))

def c8200 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8200 : Upper (D 5) (R 5) [34,68,129,272,40] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272,40] 13 (by decide) (choices 1) [1,2,4,8] r8200 c8200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4684
  · exact u4685
  · exact u4686
  · exact u4687

def b8201 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 133 296 19 60 92 156 284), lower := (rows 35 70 133 296 19 32 64 128 256), losses := [] }

theorem u8201 : Upper (D 5) (R 5) [34,68,129,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8202 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 70 133 296 21 58 90 154 282), lower := (rows 35 70 133 296 21 32 64 128 256), losses := [] }

theorem u8202 : Upper (D 5) (R 5) [34,68,129,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8203 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 133 296 22 57 89 153 281), lower := (rows 35 70 133 296 22 32 64 128 256), losses := [] }

theorem u8203 : Upper (D 5) (R 5) [34,68,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8204 : PairBound 9 := { available := 30, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 296 25 62 94 158 286), lower := (rows 35 70 133 296 25 32 64 128 256), losses := [] }

theorem u8204 : Upper (D 5) (R 5) [34,68,129,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8205 : Route 9 := (fun mask => (mask,id))

def c8205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8205 : Upper (D 5) (R 5) [34,68,129,288,10] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288,10] 13 (by decide) (choices 1) [1,4,8,16] r8205 c8205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4688
  · exact u4689
  · exact u4690
  · exact u4691

def r8206 : Route 9 := (fun mask => (mask,id))

def c8206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8206 : Upper (D 5) (R 5) [34,68,129,288,12] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288,12] 13 (by decide) (choices 1) [1,2,8,16] r8206 c8206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4692
  · exact u4693
  · exact u4694
  · exact u4695

def b8207 : PairBound 9 := { available := 281, camps := [{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 44 25 313 345 409 281), lower := (rows 35 70 134 44 25 32 64 128 256), losses := [] }

theorem u8207 : Upper (D 5) (R 5) [34,68,130,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8208 : Route 9 := (fun mask => (mask,id))

def c8208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8208 : Upper (D 5) (R 5) [34,68,130,36,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,257] 13 (by decide) (choices 1) [1,8,16] r8208 c8208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4696
  · exact u4697
  · exact u4698

def b8209 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 56 21 297 329 393 265), lower := (rows 35 70 134 56 21 32 64 128 256), losses := [] }

theorem u8209 : Upper (D 5) (R 5) [34,68,130,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8210 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 56 25 301 333 397 269), lower := (rows 35 70 134 56 25 32 64 128 256), losses := [] }

theorem u8210 : Upper (D 5) (R 5) [34,68,130,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8211 : Route 9 := (fun mask => (mask,id))

def c8211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8211 : Upper (D 5) (R 5) [34,68,130,48,12] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,12] 13 (by decide) (choices 1) [1,8,256] r8211 c8211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4699
  · exact u4700
  · exact u4701

def r8212 : Route 9 := (fun mask => (mask,id))

def c8212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8212 : Upper (D 5) (R 5) [34,68,130,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,257] 13 (by decide) (choices 1) [1,4,8] r8212 c8212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4702
  · exact u4703
  · exact u4704

def r8213 : Route 9 := (fun mask => (mask,id))

def c8213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8213 : Upper (D 5) (R 5) [34,68,130,48,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,260] 13 (by decide) (choices 1) [1,8] r8213 c8213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4705
  · exact u4706

def r8214 : Route 9 := (fun mask => (mask,id))

def c8214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8214 : Upper (D 5) (R 5) [34,68,130,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,264] 13 (by decide) (choices 1) [1,4,8] r8214 c8214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4707
  · exact u4708
  · exact u4709

def b8215 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 265 21 56 120 184 312), lower := (rows 35 70 134 265 21 32 64 128 256), losses := [] }

theorem u8215 : Upper (D 5) (R 5) [34,68,130,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8216 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 265 25 60 124 188 316), lower := (rows 35 70 134 265 25 32 64 128 256), losses := [] }

theorem u8216 : Upper (D 5) (R 5) [34,68,130,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8217 : Route 9 := (fun mask => (mask,id))

def c8217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8217 : Upper (D 5) (R 5) [34,68,130,257,12] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257,12] 13 (by decide) (choices 1) [1,8,16] r8217 c8217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4710
  · exact u4711
  · exact u4712

def b8218 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 265 49 60 92 156 284), lower := (rows 35 70 134 265 49 32 64 128 256), losses := [] }

theorem u8218 : Upper (D 5) (R 5) [34,68,130,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8219 : Route 9 := (fun mask => (mask,id))

def c8219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8219 : Upper (D 5) (R 5) [34,68,130,257,36] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257,36] 13 (by decide) (choices 1) [1,8,16] r8219 c8219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4713
  · exact u4714
  · exact u4715

#print axioms u8219
end Delivery.IrregularNine14.P05
