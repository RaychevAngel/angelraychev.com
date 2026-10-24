import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0142
import IrregularNine14P07C0143

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25140 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 11 400 40 114 178 306), lower := (rows 37 194 69 11 400 40 64 128 256), losses := [] }

theorem u25140 : Upper (D 7) (R 7) [36,192,65,3,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25140 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25141 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 400 48 106 170 298), lower := (rows 37 194 69 11 400 48 64 128 256), losses := [] }

theorem u25141 : Upper (D 7) (R 7) [36,192,65,3,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25141 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25142 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 69 25 26 34 480 416 416), lower := (rows 37 194 69 25 26 34 64 128 256), losses := [] }

theorem u25142 : Upper (D 7) (R 7) [36,192,65,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25143 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 69 25 26 160 354 418 290), lower := (rows 37 194 69 25 26 160 64 128 256), losses := [] }

theorem u25143 : Upper (D 7) (R 7) [36,192,65,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25144 : Route 9 := (fun mask => (mask,id))

def c25144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25144 : Upper (D 7) (R 7) [36,192,65,17,10,256] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,10,256] 13 (by decide) (choices 1) [2,32,128] r25144 c25144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8571
  · exact u8572
  · exact u8573

def b25145 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 25 274 34 232 168 424), lower := (rows 37 194 69 25 274 34 64 128 256), losses := [] }

theorem u25145 : Upper (D 7) (R 7) [36,192,65,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25146 : Route 9 := (fun mask => (mask,id))

def c25146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25146 : Upper (D 7) (R 7) [36,192,65,17,258,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,258,8] 13 (by decide) (choices 1) [2,32,128] r25146 c25146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8574
  · exact u8575
  · exact u8576

def b25147 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 69 25 274 160 106 170 298), lower := (rows 37 194 69 25 274 160 64 128 256), losses := [] }

theorem u25147 : Upper (D 7) (R 7) [36,192,65,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25148 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 25 280 34 226 162 418), lower := (rows 37 194 69 25 280 34 64 128 256), losses := [] }

theorem u25148 : Upper (D 7) (R 7) [36,192,65,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25149 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 69 25 280 160 98 162 290), lower := (rows 37 194 69 25 280 160 64 128 256), losses := [] }

theorem u25149 : Upper (D 7) (R 7) [36,192,65,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25150 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 25 400 34 106 170 298), lower := (rows 37 194 69 25 400 34 64 128 256), losses := [] }

theorem u25150 : Upper (D 7) (R 7) [36,192,65,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25151 : Route 9 := (fun mask => (mask,id))

def c25151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25151 : Upper (D 7) (R 7) [36,192,65,17,384,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,384,8] 13 (by decide) (choices 1) [2,32] r25151 c25151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8577
  · exact u8578

def b25152 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 69 26 56 33 450 386 386), lower := (rows 37 194 69 26 56 33 64 128 256), losses := [] }

theorem u25152 : Upper (D 7) (R 7) [36,192,65,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25153 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 194 69 26 56 34 449 385 385), lower := (rows 37 194 69 26 56 34 64 128 256), losses := [] }

theorem u25153 : Upper (D 7) (R 7) [36,192,65,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25154 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 26 56 160 323 387 259), lower := (rows 37 194 69 26 56 160 64 128 256), losses := [] }

theorem u25154 : Upper (D 7) (R 7) [36,192,65,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25155 : Route 9 := (fun mask => (mask,id))

def c25155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25155 : Upper (D 7) (R 7) [36,192,65,18,40,256] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,40,256] 13 (by decide) (choices 1) [1,2,128] r25155 c25155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8579
  · exact u8580
  · exact u8581

def b25156 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 69 26 176 33 330 394 266), lower := (rows 37 194 69 26 176 33 64 128 256), losses := [] }

theorem u25156 : Upper (D 7) (R 7) [36,192,65,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25157 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 26 176 34 329 393 265), lower := (rows 37 194 69 26 176 34 64 128 256), losses := [] }

theorem u25157 : Upper (D 7) (R 7) [36,192,65,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25158 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 26 176 40 323 387 259), lower := (rows 37 194 69 26 176 40 64 128 256), losses := [] }

theorem u25158 : Upper (D 7) (R 7) [36,192,65,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25158 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25159 : Route 9 := (fun mask => (mask,id))

def c25159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25159 : Upper (D 7) (R 7) [36,192,65,18,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,160,256] 13 (by decide) (choices 1) [1,2,8] r25159 c25159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8582
  · exact u8583
  · exact u8584

def b25160 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 69 26 273 34 232 168 424), lower := (rows 37 194 69 26 273 34 64 128 256), losses := [] }

theorem u25160 : Upper (D 7) (R 7) [36,192,65,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25161 : Route 9 := (fun mask => (mask,id))

def c25161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25161 : Upper (D 7) (R 7) [36,192,65,18,257,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,257,8] 13 (by decide) (choices 1) [2,32,128] r25161 c25161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8585
  · exact u8586
  · exact u8587

def b25162 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 194 69 26 273 160 106 170 298), lower := (rows 37 194 69 26 273 160 64 128 256), losses := [] }

theorem u25162 : Upper (D 7) (R 7) [36,192,65,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25163 : PairBound 9 := { available := 162, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 26 280 33 226 162 418), lower := (rows 37 194 69 26 280 33 64 128 256), losses := [] }

theorem u25163 : Upper (D 7) (R 7) [36,192,65,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25164 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 26 280 34 225 161 417), lower := (rows 37 194 69 26 280 34 64 128 256), losses := [] }

theorem u25164 : Upper (D 7) (R 7) [36,192,65,18,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25165 : Route 9 := (fun mask => (mask,id))

def c25165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25165 : Upper (D 7) (R 7) [36,192,65,18,264,128] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,264,128] 13 (by decide) (choices 1) [1,2,32] r25165 c25165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8588
  · exact u8589
  · exact u8590

def b25166 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 69 26 304 33 202 138 394), lower := (rows 37 194 69 26 304 33 64 128 256), losses := [] }

theorem u25166 : Upper (D 7) (R 7) [36,192,65,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25167 : Route 9 := (fun mask => (mask,id))

def c25167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25167 : Upper (D 7) (R 7) [36,192,65,18,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,288,2] 13 (by decide) (choices 1) [1,8,128] r25167 c25167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8591
  · exact u8592
  · exact u8593

def r25168 : Route 9 := (fun mask => (mask,id))

def c25168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25168 : Upper (D 7) (R 7) [36,192,65,18,288,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,288,8] 13 (by decide) (choices 1) [1,2,128] r25168 c25168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8594
  · exact u8595
  · exact u8596

def r25169 : Route 9 := (fun mask => (mask,id))

def c25169 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25169 : Upper (D 7) (R 7) [36,192,65,18,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,288,128] 13 (by decide) (choices 1) [1,2,8] r25169 c25169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8597
  · exact u8598
  · exact u8599

def b25170 : PairBound 9 := { available := 42, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 26 400 33 106 170 298), lower := (rows 37 194 69 26 400 33 64 128 256), losses := [] }

theorem u25170 : Upper (D 7) (R 7) [36,192,65,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25171 : Route 9 := (fun mask => (mask,id))

def c25171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25171 : Upper (D 7) (R 7) [36,192,65,18,384,2] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,384,2] 13 (by decide) (choices 1) [1,8,32] r25171 c25171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8600
  · exact u8601
  · exact u8602

def r25172 : Route 9 := (fun mask => (mask,id))

def c25172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25172 : Upper (D 7) (R 7) [36,192,65,18,384,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,384,8] 13 (by decide) (choices 1) [1,2,32] r25172 c25172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8603
  · exact u8604
  · exact u8605

def b25173 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 69 42 145 34 344 408 280), lower := (rows 37 194 69 42 145 34 64 128 256), losses := [] }

theorem u25173 : Upper (D 7) (R 7) [36,192,65,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25174 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 42 145 40 338 402 274), lower := (rows 37 194 69 42 145 40 64 128 256), losses := [] }

theorem u25174 : Upper (D 7) (R 7) [36,192,65,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25174 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25175 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 194 69 42 145 48 330 394 266), lower := (rows 37 194 69 42 145 48 64 128 256), losses := [] }

theorem u25175 : Upper (D 7) (R 7) [36,192,65,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25175 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25176 : Route 9 := (fun mask => (mask,id))

def c25176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25176 : Upper (D 7) (R 7) [36,192,65,34,129,256] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,129,256] 13 (by decide) (choices 1) [2,8,16] r25176 c25176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8606
  · exact u8607
  · exact u8608

def b25177 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 42 152 33 338 402 274), lower := (rows 37 194 69 42 152 33 64 128 256), losses := [] }

theorem u25177 : Upper (D 7) (R 7) [36,192,65,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25178 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 42 152 34 337 401 273), lower := (rows 37 194 69 42 152 34 64 128 256), losses := [] }

theorem u25178 : Upper (D 7) (R 7) [36,192,65,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25179 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 42 152 48 323 387 259), lower := (rows 37 194 69 42 152 48 64 128 256), losses := [] }

theorem u25179 : Upper (D 7) (R 7) [36,192,65,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25179 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25180 : Route 9 := (fun mask => (mask,id))

def c25180 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25180 : Upper (D 7) (R 7) [36,192,65,34,136,256] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,136,256] 13 (by decide) (choices 1) [1,2,16] r25180 c25180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8609
  · exact u8610
  · exact u8611

def b25181 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 69 42 273 34 216 152 408), lower := (rows 37 194 69 42 273 34 64 128 256), losses := [] }

theorem u25181 : Upper (D 7) (R 7) [36,192,65,34,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25182 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 42 273 40 210 146 402), lower := (rows 37 194 69 42 273 40 64 128 256), losses := [] }

theorem u25182 : Upper (D 7) (R 7) [36,192,65,34,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25182 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25183 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 69 42 273 48 202 138 394), lower := (rows 37 194 69 42 273 48 64 128 256), losses := [] }

theorem u25183 : Upper (D 7) (R 7) [36,192,65,34,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25183 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25184 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 69 42 273 160 90 154 282), lower := (rows 37 194 69 42 273 160 64 128 256), losses := [] }

theorem u25184 : Upper (D 7) (R 7) [36,192,65,34,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25185 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 42 274 33 216 152 408), lower := (rows 37 194 69 42 274 33 64 128 256), losses := [] }

theorem u25185 : Upper (D 7) (R 7) [36,192,65,34,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25186 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 42 274 40 209 145 401), lower := (rows 37 194 69 42 274 40 64 128 256), losses := [] }

theorem u25186 : Upper (D 7) (R 7) [36,192,65,34,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25186 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25187 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 194 69 42 274 48 201 137 393), lower := (rows 37 194 69 42 274 48 64 128 256), losses := [] }

theorem u25187 : Upper (D 7) (R 7) [36,192,65,34,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25187 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25188 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 69 42 274 160 89 153 281), lower := (rows 37 194 69 42 274 160 64 128 256), losses := [] }

theorem u25188 : Upper (D 7) (R 7) [36,192,65,34,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25189 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 42 280 33 210 146 402), lower := (rows 37 194 69 42 280 33 64 128 256), losses := [] }

theorem u25189 : Upper (D 7) (R 7) [36,192,65,34,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25190 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 69 42 280 34 209 145 401), lower := (rows 37 194 69 42 280 34 64 128 256), losses := [] }

theorem u25190 : Upper (D 7) (R 7) [36,192,65,34,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25191 : Route 9 := (fun mask => (mask,id))

def c25191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25191 : Upper (D 7) (R 7) [36,192,65,34,264,16] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,264,16] 13 (by decide) (choices 1) [1,2,128] r25191 c25191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8612
  · exact u8613
  · exact u8614

def b25192 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 69 42 280 160 83 147 275), lower := (rows 37 194 69 42 280 160 64 128 256), losses := [] }

theorem u25192 : Upper (D 7) (R 7) [36,192,65,34,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25193 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 42 400 33 90 154 282), lower := (rows 37 194 69 42 400 33 64 128 256), losses := [] }

theorem u25193 : Upper (D 7) (R 7) [36,192,65,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25194 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 69 42 400 34 89 153 281), lower := (rows 37 194 69 42 400 34 64 128 256), losses := [] }

theorem u25194 : Upper (D 7) (R 7) [36,192,65,34,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25195 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 42 400 40 83 147 275), lower := (rows 37 194 69 42 400 40 64 128 256), losses := [] }

theorem u25195 : Upper (D 7) (R 7) [36,192,65,34,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25195 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25196 : Route 9 := (fun mask => (mask,id))

def c25196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25196 : Upper (D 7) (R 7) [36,192,65,34,384,16] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,384,16] 13 (by decide) (choices 1) [1,2,8] r25196 c25196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8615
  · exact u8616
  · exact u8617

def b25197 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 69 56 145 34 330 394 266), lower := (rows 37 194 69 56 145 34 64 128 256), losses := [] }

theorem u25197 : Upper (D 7) (R 7) [36,192,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25198 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 61, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 194 69 56 145 40 322 386 258), lower := (rows 37 194 69 56 145 40 64 128 256), losses := [] }

theorem u25198 : Upper (D 7) (R 7) [36,192,65,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25198 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25199 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 69 56 145 288 74 138 266), lower := (rows 37 194 69 56 145 288 64 128 256), losses := [] }

theorem u25199 : Upper (D 7) (R 7) [36,192,65,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25199 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25199
end Delivery.IrregularNine14.P07
