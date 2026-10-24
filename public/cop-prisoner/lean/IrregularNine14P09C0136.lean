import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0093
import IrregularNine14P09C0094

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8160 : Route 9 := (fun mask => (mask,id))

def c8160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u8160 : Upper (D 9) (R 9) [96,5,130,160,257] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160,257] 13 (by decide) (choices 1) [8,16,64,256] r8160 c8160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5588
  · exact u5589
  · exact u5590
  · exact u5591

def r8161 : Route 9 := (fun mask => (mask,id))

def c8161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8161 : Upper (D 9) (R 9) [96,5,130,160,264] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160,264] 13 (by decide) (choices 1) [1,16,64,256] r8161 c8161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5592
  · exact u5593
  · exact u5594
  · exact u5595

def r8162 : Route 9 := (fun mask => (mask,id))

def c8162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8162 : Upper (D 9) (R 9) [96,5,130,160,320] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160,320] 13 (by decide) (choices 1) [1,8,16,256] r8162 c8162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5596
  · exact u5597
  · exact u5598
  · exact u5599

def b8163 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,5),(4,6),(4,7)], upper := (rows 97 7 134 265 280 240 240 240 496), lower := (rows 97 7 134 265 280 32 64 128 256), losses := [] }

theorem u8163 : Upper (D 9) (R 9) [96,5,130,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8163 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8164 : Route 9 := (fun mask => (mask,id))

def c8164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8164 : Upper (D 9) (R 9) [96,5,130,257,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,257,288] 13 (by decide) (choices 1) [8,16,64,128] r8164 c8164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5600
  · exact u5601
  · exact u5602
  · exact u5603

def r8165 : Route 9 := (fun mask => (mask,id))

def c8165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8165 : Upper (D 9) (R 9) [96,5,130,257,384] 13 := by
  apply FastRouting.sound _ _ [96,5,130,257,384] 13 (by decide) (choices 1) [8,16,64] r8165 c8165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5604
  · exact u5605
  · exact u5606

def b8166 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 97 7 134 280 280 225 225 225 481), lower := (rows 97 7 134 280 280 32 64 128 256), losses := [] }

theorem u8166 : Upper (D 9) (R 9) [96,5,130,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8166 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8167 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 7 134 280 304 233 201 201 457), lower := (rows 97 7 134 280 304 32 64 128 256), losses := [] }

theorem u8167 : Upper (D 9) (R 9) [96,5,130,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8167 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8168 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 231, targets := 256 },{ cop := 4, region := 8, targets := 33 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,5)], upper := (rows 97 7 134 280 400 105 105 233 361), lower := (rows 97 7 134 280 400 32 64 128 256), losses := [] }

theorem u8168 : Upper (D 9) (R 9) [96,5,130,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8169 : Route 9 := (fun mask => (mask,id))

def c8169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8169 : Upper (D 9) (R 9) [96,5,130,288,320] 13 := by
  apply FastRouting.sound _ _ [96,5,130,288,320] 13 (by decide) (choices 1) [1,8,16,128] r8169 c8169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5607
  · exact u5608
  · exact u5609
  · exact u5610

def r8170 : Route 9 := (fun mask => (mask,id))

def c8170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8170 : Upper (D 9) (R 9) [96,5,130,288,384] 13 := by
  apply FastRouting.sound _ _ [96,5,130,288,384] 13 (by decide) (choices 1) [1,8,16,64] r8170 c8170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5611
  · exact u5612
  · exact u5613
  · exact u5614

def b8171 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 496, targets := 1 },{ cop := 3, region := 484, targets := 1 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 140 25 146 352 352 480 352), lower := (rows 97 7 140 25 146 32 64 128 256), losses := [] }

theorem u8171 : Upper (D 9) (R 9) [96,5,136,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8171 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8172 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(1,5),(1,7),(2,5),(4,0)], upper := (rows 97 7 140 25 176 354 322 450 322), lower := (rows 97 7 140 25 176 32 64 128 256), losses := [] }

theorem u8172 : Upper (D 9) (R 9) [96,5,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8172 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8173_256 : Upper (D 9) (R 9) [96,5,136,17,258,256] 13 :=
  permutation_upper _ _ _ [96,5,136,17,258,128] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5616

def r8173 : Route 9 := (fun mask => (mask,id))

def c8173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8173 : Upper (D 9) (R 9) [96,5,136,17,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17,258] 13 (by decide) (choices 1) [64,128,256] r8173 c8173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5615
  · exact u5616
  · exact m8173_256

def r8174 : Route 9 := (fun mask => (mask,id))

def c8174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8174 : Upper (D 9) (R 9) [96,5,136,17,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17,288] 13 (by decide) (choices 1) [2,64,128,256] r8174 c8174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5617
  · exact u5618
  · exact u5619
  · exact u5620

def r8175 : Route 9 := (fun mask => (mask,id))

def c8175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8175 : Upper (D 9) (R 9) [96,5,136,17,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17,384] 13 (by decide) (choices 1) [2,64,256] r8175 c8175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5621
  · exact u5622
  · exact u5623

def b8176 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 7 140 26 49 480 448 448 448), lower := (rows 97 7 140 26 49 32 64 128 256), losses := [] }

theorem u8176 : Upper (D 9) (R 9) [96,5,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8176 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8177 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 140 26 112 417 449 385 385), lower := (rows 97 7 140 26 112 32 64 128 256), losses := [] }

theorem u8177 : Upper (D 9) (R 9) [96,5,136,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8177 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8178 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 14, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 140 26 145 352 352 480 352), lower := (rows 97 7 140 26 145 32 64 128 256), losses := [] }

theorem u8178 : Upper (D 9) (R 9) [96,5,136,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8178 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8179 : Route 9 := (fun mask => (mask,id))

def c8179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8179 : Upper (D 9) (R 9) [96,5,136,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,160] 13 (by decide) (choices 1) [1,64,256] r8179 c8179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5624
  · exact u5625
  · exact u5626

def r8180 : Route 9 := (fun mask => (mask,id))

def c8180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8180 : Upper (D 9) (R 9) [96,5,136,18,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,257] 13 (by decide) (choices 1) [64,128,256] r8180 c8180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5627
  · exact u5628
  · exact u5629

def r8181 : Route 9 := (fun mask => (mask,id))

def c8181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8181 : Upper (D 9) (R 9) [96,5,136,18,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,288] 13 (by decide) (choices 1) [1,64,128,256] r8181 c8181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5630
  · exact u5631
  · exact u5632
  · exact u5633

def r8182 : Route 9 := (fun mask => (mask,id))

def c8182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8182 : Upper (D 9) (R 9) [96,5,136,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,384] 13 (by decide) (choices 1) [1,64,256] r8182 c8182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5634
  · exact u5635
  · exact u5636

def b8183 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 82 432 464 400 400), lower := (rows 97 7 140 41 82 32 64 128 256), losses := [] }

theorem u8183 : Upper (D 9) (R 9) [96,5,136,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8183 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8184 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 146 368 336 464 336), lower := (rows 97 7 140 41 146 32 64 128 256), losses := [] }

theorem u8184 : Upper (D 9) (R 9) [96,5,136,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8184 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8185 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 208 306 338 402 274), lower := (rows 97 7 140 41 208 32 64 128 256), losses := [] }

theorem u8185 : Upper (D 9) (R 9) [96,5,136,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8185 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8186 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 274 496 464 464 464), lower := (rows 97 7 140 41 274 32 64 128 256), losses := [] }

theorem u8186 : Upper (D 9) (R 9) [96,5,136,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8186 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8187 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 336 434 466 402 402), lower := (rows 97 7 140 41 336 32 64 128 256), losses := [] }

theorem u8187 : Upper (D 9) (R 9) [96,5,136,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8188 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 400 370 338 466 338), lower := (rows 97 7 140 41 400 32 64 128 256), losses := [] }

theorem u8188 : Upper (D 9) (R 9) [96,5,136,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8188 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8189 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,6),(2,6),(3,6),(4,7),(4,8)], upper := (rows 97 7 140 42 81 432 464 400 400), lower := (rows 97 7 140 42 81 32 64 128 256), losses := [] }

theorem u8189 : Upper (D 9) (R 9) [96,5,136,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8190 : Route 9 := (fun mask => (mask,id))

def c8190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8190 : Upper (D 9) (R 9) [96,5,136,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,129] 13 (by decide) (choices 1) [16,64,256] r8190 c8190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5637
  · exact u5638
  · exact u5639

def r8191 : Route 9 := (fun mask => (mask,id))

def c8191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8191 : Upper (D 9) (R 9) [96,5,136,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,192] 13 (by decide) (choices 1) [1,16,256] r8191 c8191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5640
  · exact u5641
  · exact u5642

def r8192 : Route 9 := (fun mask => (mask,id))

def c8192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u8192 : Upper (D 9) (R 9) [96,5,136,34,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,257] 13 (by decide) (choices 1) [16,64,128,256] r8192 c8192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5643
  · exact u5644
  · exact u5645
  · exact u5646

def r8193 : Route 9 := (fun mask => (mask,id))

def c8193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8193 : Upper (D 9) (R 9) [96,5,136,34,320] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,320] 13 (by decide) (choices 1) [1,16,128,256] r8193 c8193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5647
  · exact u5648
  · exact u5649
  · exact u5650

def r8194 : Route 9 := (fun mask => (mask,id))

def c8194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8194 : Upper (D 9) (R 9) [96,5,136,34,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,384] 13 (by decide) (choices 1) [1,16,64,256] r8194 c8194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5651
  · exact u5652
  · exact u5653
  · exact u5654

def b8195 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 24, targets := 384 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(3,7),(3,8),(4,7),(4,8)], upper := (rows 97 7 140 56 81 418 450 386 386), lower := (rows 97 7 140 56 81 32 64 128 256), losses := [] }

theorem u8195 : Upper (D 9) (R 9) [96,5,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8196 : Route 9 := (fun mask => (mask,id))

def c8196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8196 : Upper (D 9) (R 9) [96,5,136,48,66] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,66] 13 (by decide) (choices 1) [1,128,256] r8196 c8196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5655
  · exact u5656
  · exact u5657

def r8197 : Route 9 := (fun mask => (mask,id))

def c8197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8197 : Upper (D 9) (R 9) [96,5,136,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,129] 13 (by decide) (choices 1) [2,64,256] r8197 c8197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5658
  · exact u5659
  · exact u5660

def r8198 : Route 9 := (fun mask => (mask,id))

def c8198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8198 : Upper (D 9) (R 9) [96,5,136,48,130] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,130] 13 (by decide) (choices 1) [1,64,256] r8198 c8198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5661
  · exact u5662
  · exact u5663

def r8199 : Route 9 := (fun mask => (mask,id))

def c8199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8199 : Upper (D 9) (R 9) [96,5,136,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,192] 13 (by decide) (choices 1) [1,2,256] r8199 c8199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5664
  · exact u5665
  · exact u5666

def r8200 : Route 9 := (fun mask => (mask,id))

def c8200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8200 : Upper (D 9) (R 9) [96,5,136,48,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,257] 13 (by decide) (choices 1) [2,64,128,256] r8200 c8200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5667
  · exact u5668
  · exact u5669
  · exact u5670

def r8201 : Route 9 := (fun mask => (mask,id))

def c8201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8201 : Upper (D 9) (R 9) [96,5,136,48,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,258] 13 (by decide) (choices 1) [1,64,128,256] r8201 c8201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5671
  · exact u5672
  · exact u5673
  · exact u5674

def r8202 : Route 9 := (fun mask => (mask,id))

def c8202 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8202 : Upper (D 9) (R 9) [96,5,136,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,320] 13 (by decide) (choices 1) [1,2,128,256] r8202 c8202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5675
  · exact u5676
  · exact u5677
  · exact u5678

def r8203 : Route 9 := (fun mask => (mask,id))

def c8203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8203 : Upper (D 9) (R 9) [96,5,136,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,384] 13 (by decide) (choices 1) [1,2,64,256] r8203 c8203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5679
  · exact u5680
  · exact u5681
  · exact u5682

def b8204 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 140 104 145 306 338 402 274), lower := (rows 97 7 140 104 145 32 64 128 256), losses := [] }

theorem u8204 : Upper (D 9) (R 9) [96,5,136,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8204 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8205 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 140 104 146 305 337 401 273), lower := (rows 97 7 140 104 146 32 64 128 256), losses := [] }

theorem u8205 : Upper (D 9) (R 9) [96,5,136,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8206 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 140 104 273 434 466 402 402), lower := (rows 97 7 140 104 273 32 64 128 256), losses := [] }

theorem u8206 : Upper (D 9) (R 9) [96,5,136,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8206 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8207 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 140 104 274 433 465 401 401), lower := (rows 97 7 140 104 274 32 64 128 256), losses := [] }

theorem u8207 : Upper (D 9) (R 9) [96,5,136,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8207 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8208 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 140 104 400 307 339 403 275), lower := (rows 97 7 140 104 400 32 64 128 256), losses := [] }

theorem u8208 : Upper (D 9) (R 9) [96,5,136,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8208 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8209 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 140 137 50 368 336 464 336), lower := (rows 97 7 140 137 50 32 64 128 256), losses := [] }

theorem u8209 : Upper (D 9) (R 9) [96,5,136,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8209 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8210 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 140 137 274 368 368 496 368), lower := (rows 97 7 140 137 274 32 64 128 256), losses := [] }

theorem u8210 : Upper (D 9) (R 9) [96,5,136,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8210 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8211 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 140 137 304 370 338 466 338), lower := (rows 97 7 140 137 304 32 64 128 256), losses := [] }

theorem u8211 : Upper (D 9) (R 9) [96,5,136,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8211 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8212 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 138 273 368 368 496 368), lower := (rows 97 7 140 138 273 32 64 128 256), losses := [] }

theorem u8212 : Upper (D 9) (R 9) [96,5,136,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8212 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8213 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 138 304 369 337 465 337), lower := (rows 97 7 140 138 304 32 64 128 256), losses := [] }

theorem u8213 : Upper (D 9) (R 9) [96,5,136,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8213 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8214 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 152 50 353 321 449 321), lower := (rows 97 7 140 152 50 32 64 128 256), losses := [] }

theorem u8214 : Upper (D 9) (R 9) [96,5,136,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8214 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8215 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 152 273 354 354 482 354), lower := (rows 97 7 140 152 273 32 64 128 256), losses := [] }

theorem u8215 : Upper (D 9) (R 9) [96,5,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8215 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8216 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 152 274 353 353 481 353), lower := (rows 97 7 140 152 274 32 64 128 256), losses := [] }

theorem u8216 : Upper (D 9) (R 9) [96,5,136,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8216 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8217 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 152 304 355 323 451 323), lower := (rows 97 7 140 152 304 32 64 128 256), losses := [] }

theorem u8217 : Upper (D 9) (R 9) [96,5,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8218 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 168 82 305 337 401 273), lower := (rows 97 7 140 168 82 32 64 128 256), losses := [] }

theorem u8218 : Upper (D 9) (R 9) [96,5,136,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8218 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8219 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 168 273 370 338 466 338), lower := (rows 97 7 140 168 273 32 64 128 256), losses := [] }

theorem u8219 : Upper (D 9) (R 9) [96,5,136,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8219
end Delivery.IrregularNine14.P09
