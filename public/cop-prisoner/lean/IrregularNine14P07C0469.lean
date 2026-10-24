import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0174

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28140 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 28 82 33 450 386 386), lower := (rows 97 162 13 28 82 33 64 128 256), losses := [] }

theorem u28140 : Upper (D 7) (R 7) [96,160,9,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28141 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 7, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 162 13 28 82 34 449 385 385), lower := (rows 97 162 13 28 82 34 64 128 256), losses := [] }

theorem u28141 : Upper (D 7) (R 7) [96,160,9,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28142 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 28 82 160 323 387 259), lower := (rows 97 162 13 28 82 160 64 128 256), losses := [] }

theorem u28142 : Upper (D 7) (R 7) [96,160,9,20,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28143 : Route 9 := (fun mask => (mask,id))

def c28143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28143 : Upper (D 7) (R 7) [96,160,9,20,66,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,66,256] 13 (by decide) (choices 1) [1,2,128] r28143 c28143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10442
  · exact u10443
  · exact u10444

def b28144 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 28 208 33 322 386 258), lower := (rows 97 162 13 28 208 33 64 128 256), losses := [] }

theorem u28144 : Upper (D 7) (R 7) [96,160,9,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28145 : Route 9 := (fun mask => (mask,id))

def c28145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u28145 : Upper (D 7) (R 7) [96,160,9,20,192,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,192,2] 13 (by decide) (choices 1) [1,2,256] r28145 c28145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10445
  · exact u10446
  · exact u10447

def r28146 : Route 9 := (fun mask => (mask,id))

def c28146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28146 : Upper (D 7) (R 7) [96,160,9,20,192,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,192,256] 13 (by decide) (choices 1) [1,2] r28146 c28146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10448
  · exact u10449

def b28147 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 28 274 33 194 194 450), lower := (rows 97 162 13 28 274 33 64 128 256), losses := [] }

theorem u28147 : Upper (D 7) (R 7) [96,160,9,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28148 : PairBound 9 := { available := 193, camps := [{ cop := 7, region := 34, targets := 65 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(2,1)], upper := (rows 97 162 13 28 274 34 193 193 449), lower := (rows 97 162 13 28 274 34 64 128 256), losses := [{ target := 1, region := (rows 35 0 20 24 16 32 119 183 311), good := (rows 481 481 461 476 477 481 64 128 256) }] }

theorem u28148 : Upper (D 7) (R 7) [96,160,9,20,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28149 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 28 274 96 195 131 387), lower := (rows 97 162 13 28 274 96 64 128 256), losses := [] }

theorem u28149 : Upper (D 7) (R 7) [96,160,9,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28150 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 28 274 160 67 195 323), lower := (rows 97 162 13 28 274 160 64 128 256), losses := [] }

theorem u28150 : Upper (D 7) (R 7) [96,160,9,20,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28151 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 28 336 33 194 130 386), lower := (rows 97 162 13 28 336 33 64 128 256), losses := [] }

theorem u28151 : Upper (D 7) (R 7) [96,160,9,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28152 : Route 9 := (fun mask => (mask,id))

def c28152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28152 : Upper (D 7) (R 7) [96,160,9,20,320,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,320,2] 13 (by decide) (choices 1) [1,2,128] r28152 c28152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10450
  · exact u10451
  · exact u10452

def b28153 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 28 336 160 67 131 259), lower := (rows 97 162 13 28 336 160 64 128 256), losses := [] }

theorem u28153 : Upper (D 7) (R 7) [96,160,9,20,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28154 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 28 400 33 66 194 322), lower := (rows 97 162 13 28 400 33 64 128 256), losses := [] }

theorem u28154 : Upper (D 7) (R 7) [96,160,9,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28155 : Route 9 := (fun mask => (mask,id))

def c28155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28155 : Upper (D 7) (R 7) [96,160,9,20,384,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,384,2] 13 (by decide) (choices 1) [1,2] r28155 c28155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10453
  · exact u10454

def b28156 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 28 400 96 67 131 259), lower := (rows 97 162 13 28 400 96 64 128 256), losses := [] }

theorem u28156 : Upper (D 7) (R 7) [96,160,9,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28157 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 400, targets := 34 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 97 162 13 74 145 34 340 404 276), lower := (rows 97 162 13 74 145 34 64 128 256), losses := [] }

theorem u28157 : Upper (D 7) (R 7) [96,160,9,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28158 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 74 145 36 338 402 274), lower := (rows 97 162 13 74 145 36 64 128 256), losses := [] }

theorem u28158 : Upper (D 7) (R 7) [96,160,9,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28158 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28159 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 145 48 326 390 262), lower := (rows 97 162 13 74 145 48 64 128 256), losses := [] }

theorem u28159 : Upper (D 7) (R 7) [96,160,9,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28159 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28160 : Route 9 := (fun mask => (mask,id))

def c28160 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28160 : Upper (D 7) (R 7) [96,160,9,66,129,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,129,256] 13 (by decide) (choices 1) [2,4,16] r28160 c28160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10455
  · exact u10456
  · exact u10457

def b28161 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 74 148 33 338 402 274), lower := (rows 97 162 13 74 148 33 64 128 256), losses := [] }

theorem u28161 : Upper (D 7) (R 7) [96,160,9,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28162 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 400, targets := 34 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 97 162 13 74 148 34 337 401 273), lower := (rows 97 162 13 74 148 34 64 128 256), losses := [] }

theorem u28162 : Upper (D 7) (R 7) [96,160,9,66,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28163 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 148 48 323 387 259), lower := (rows 97 162 13 74 148 48 64 128 256), losses := [] }

theorem u28163 : Upper (D 7) (R 7) [96,160,9,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28163 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28164 : Route 9 := (fun mask => (mask,id))

def c28164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28164 : Upper (D 7) (R 7) [96,160,9,66,132,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,132,256] 13 (by decide) (choices 1) [1,2,16] r28164 c28164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10458
  · exact u10459
  · exact u10460

def b28165 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 400, targets := 34 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 97 162 13 74 273 34 212 148 404), lower := (rows 97 162 13 74 273 34 64 128 256), losses := [] }

theorem u28165 : Upper (D 7) (R 7) [96,160,9,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28166 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 74 273 36 210 146 402), lower := (rows 97 162 13 74 273 36 64 128 256), losses := [] }

theorem u28166 : Upper (D 7) (R 7) [96,160,9,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28166 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28167 : Route 9 := (fun mask => (mask,id))

def c28167 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28167 : Upper (D 7) (R 7) [96,160,9,66,257,16] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,257,16] 13 (by decide) (choices 1) [2,4,128] r28167 c28167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10461
  · exact u10462
  · exact u10463

def b28168 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 74 273 160 86 150 278), lower := (rows 97 162 13 74 273 160 64 128 256), losses := [] }

theorem u28168 : Upper (D 7) (R 7) [96,160,9,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28169 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 74 274 33 212 148 404), lower := (rows 97 162 13 74 274 33 64 128 256), losses := [] }

theorem u28169 : Upper (D 7) (R 7) [96,160,9,66,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28170 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 74 274 36 209 145 401), lower := (rows 97 162 13 74 274 36 64 128 256), losses := [] }

theorem u28170 : Upper (D 7) (R 7) [96,160,9,66,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28170 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28171 : Route 9 := (fun mask => (mask,id))

def c28171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28171 : Upper (D 7) (R 7) [96,160,9,66,258,16] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,258,16] 13 (by decide) (choices 1) [1,4,128] r28171 c28171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10464
  · exact u10465
  · exact u10466

def b28172 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 74 274 160 85 149 277), lower := (rows 97 162 13 74 274 160 64 128 256), losses := [] }

theorem u28172 : Upper (D 7) (R 7) [96,160,9,66,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28173 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 74 276 33 210 146 402), lower := (rows 97 162 13 74 276 33 64 128 256), losses := [] }

theorem u28173 : Upper (D 7) (R 7) [96,160,9,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28174 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 400, targets := 34 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 97 162 13 74 276 34 209 145 401), lower := (rows 97 162 13 74 276 34 64 128 256), losses := [] }

theorem u28174 : Upper (D 7) (R 7) [96,160,9,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28175 : Route 9 := (fun mask => (mask,id))

def c28175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28175 : Upper (D 7) (R 7) [96,160,9,66,260,16] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,260,16] 13 (by decide) (choices 1) [1,2,128] r28175 c28175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10467
  · exact u10468
  · exact u10469

def b28176 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 74 276 160 83 147 275), lower := (rows 97 162 13 74 276 160 64 128 256), losses := [] }

theorem u28176 : Upper (D 7) (R 7) [96,160,9,66,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28177 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 74 400 33 86 150 278), lower := (rows 97 162 13 74 400 33 64 128 256), losses := [] }

theorem u28177 : Upper (D 7) (R 7) [96,160,9,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28178 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 400, targets := 34 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 97 162 13 74 400 34 85 149 277), lower := (rows 97 162 13 74 400 34 64 128 256), losses := [] }

theorem u28178 : Upper (D 7) (R 7) [96,160,9,66,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28179 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 74 400 36 83 147 275), lower := (rows 97 162 13 74 400 36 64 128 256), losses := [] }

theorem u28179 : Upper (D 7) (R 7) [96,160,9,66,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28179 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28180 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 400 48 71 135 263), lower := (rows 97 162 13 74 400 48 64 128 256), losses := [] }

theorem u28180 : Upper (D 7) (R 7) [96,160,9,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28180 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28181 : Route 9 := (fun mask => (mask,id))

def c28181 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u28181 : Upper (D 7) (R 7) [96,160,9,80,129,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,129,2] 13 (by decide) (choices 1) [2,4,256] r28181 c28181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10470
  · exact u10471
  · exact u10472

def b28182 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 88 145 36 322 386 258), lower := (rows 97 162 13 88 145 36 64 128 256), losses := [] }

theorem u28182 : Upper (D 7) (R 7) [96,160,9,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28182 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28183 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 145 288 70 134 262), lower := (rows 97 162 13 88 145 288 64 128 256), losses := [] }

theorem u28183 : Upper (D 7) (R 7) [96,160,9,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28183 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28184 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 88 148 33 322 386 258), lower := (rows 97 162 13 88 148 33 64 128 256), losses := [] }

theorem u28184 : Upper (D 7) (R 7) [96,160,9,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28185 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 1, region := 321, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 148 34 323 387 259), lower := (rows 97 162 13 88 148 34 64 128 256), losses := [] }

theorem u28185 : Upper (D 7) (R 7) [96,160,9,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28186 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 97 162 13 88 148 288 67 131 259), lower := (rows 97 162 13 88 148 288 64 128 256), losses := [] }

theorem u28186 : Upper (D 7) (R 7) [96,160,9,80,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28186 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28187 : Route 9 := (fun mask => (mask,id))

def c28187 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28187 : Upper (D 7) (R 7) [96,160,9,80,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,257,2] 13 (by decide) (choices 1) [2,4,128] r28187 c28187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10473
  · exact u10474
  · exact u10475

def b28188 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 88 273 36 194 130 386), lower := (rows 97 162 13 88 273 36 64 128 256), losses := [] }

theorem u28188 : Upper (D 7) (R 7) [96,160,9,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28188 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28189 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 88 273 160 70 134 262), lower := (rows 97 162 13 88 273 160 64 128 256), losses := [] }

theorem u28189 : Upper (D 7) (R 7) [96,160,9,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28190 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 88 274 33 198 134 390), lower := (rows 97 162 13 88 274 33 64 128 256), losses := [] }

theorem u28190 : Upper (D 7) (R 7) [96,160,9,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28191 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 7, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 274 34 197 133 389), lower := (rows 97 162 13 88 274 34 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 50 64 0 256), good := (rows 97 34 13 125 306 34 64 0 256) }] }

theorem u28191 : Upper (D 7) (R 7) [96,160,9,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28192 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 88 274 36 195 131 387), lower := (rows 97 162 13 88 274 36 64 128 256), losses := [] }

theorem u28192 : Upper (D 7) (R 7) [96,160,9,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28192 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28193 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 88 274 160 71 135 263), lower := (rows 97 162 13 88 274 160 64 128 256), losses := [] }

theorem u28193 : Upper (D 7) (R 7) [96,160,9,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28194 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 88 276 33 194 130 386), lower := (rows 97 162 13 88 276 33 64 128 256), losses := [] }

theorem u28194 : Upper (D 7) (R 7) [96,160,9,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28195 : Route 9 := (fun mask => (mask,id))

def c28195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28195 : Upper (D 7) (R 7) [96,160,9,80,260,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,260,2] 13 (by decide) (choices 1) [1,2,128] r28195 c28195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10476
  · exact u10477
  · exact u10478

def b28196 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 88 276 160 67 131 259), lower := (rows 97 162 13 88 276 160 64 128 256), losses := [] }

theorem u28196 : Upper (D 7) (R 7) [96,160,9,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28197 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 88 400 33 70 134 262), lower := (rows 97 162 13 88 400 33 64 128 256), losses := [] }

theorem u28197 : Upper (D 7) (R 7) [96,160,9,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28198 : Route 9 := (fun mask => (mask,id))

def c28198 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28198 : Upper (D 7) (R 7) [96,160,9,80,384,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,384,2] 13 (by decide) (choices 1) [1,2,4] r28198 c28198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10479
  · exact u10480
  · exact u10481

def b28199 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 88 400 36 67 131 259), lower := (rows 97 162 13 88 400 36 64 128 256), losses := [] }

theorem u28199 : Upper (D 7) (R 7) [96,160,9,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28199 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28199
end Delivery.IrregularNine14.P07
