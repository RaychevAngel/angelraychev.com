import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0155
import IrregularNine14P07C0156

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26160 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 266 7 104 81 48 194 130 386), lower := (rows 37 266 7 104 81 48 64 128 256), losses := [] }

theorem u26160 : Upper (D 7) (R 7) [36,264,3,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26160 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26161 : Route 9 := (fun mask => (mask,id))

def c26161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26161 : Upper (D 7) (R 7) [36,264,3,96,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,65,128] 13 (by decide) (choices 1) [2,16,128] r26161 c26161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9326
  · exact u9327
  · exact u9328

def b26162 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 104 82 33 208 144 400), lower := (rows 37 266 7 104 82 33 64 128 256), losses := [] }

theorem u26162 : Upper (D 7) (R 7) [36,264,3,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26163 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 266 7 104 82 48 193 129 385), lower := (rows 37 266 7 104 82 48 64 128 256), losses := [] }

theorem u26163 : Upper (D 7) (R 7) [36,264,3,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26163 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26164 : Route 9 := (fun mask => (mask,id))

def c26164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26164 : Upper (D 7) (R 7) [36,264,3,96,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,66,128] 13 (by decide) (choices 1) [1,16,128] r26164 c26164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9329
  · exact u9330
  · exact u9331

def b26165 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 104 145 34 208 208 464), lower := (rows 37 266 7 104 145 34 64 128 256), losses := [] }

theorem u26165 : Upper (D 7) (R 7) [36,264,3,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26166 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 266 7 104 145 48 194 194 450), lower := (rows 37 266 7 104 145 48 64 128 256), losses := [] }

theorem u26166 : Upper (D 7) (R 7) [36,264,3,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26166 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26167 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 37 266 7 104 145 96 210 146 402), lower := (rows 37 266 7 104 145 96 64 128 256), losses := [] }

theorem u26167 : Upper (D 7) (R 7) [36,264,3,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26168 : Route 9 := (fun mask => (mask,id))

def c26168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26168 : Upper (D 7) (R 7) [36,264,3,96,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,129,128] 13 (by decide) (choices 1) [2,16] r26168 c26168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9332
  · exact u9333

def b26169 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 104 146 33 208 208 464), lower := (rows 37 266 7 104 146 33 64 128 256), losses := [] }

theorem u26169 : Upper (D 7) (R 7) [36,264,3,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26170 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 266 7 104 146 48 193 193 449), lower := (rows 37 266 7 104 146 48 64 128 256), losses := [] }

theorem u26170 : Upper (D 7) (R 7) [36,264,3,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26170 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26171 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 37 266 7 104 146 96 209 145 401), lower := (rows 37 266 7 104 146 96 64 128 256), losses := [] }

theorem u26171 : Upper (D 7) (R 7) [36,264,3,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26172 : Route 9 := (fun mask => (mask,id))

def c26172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26172 : Upper (D 7) (R 7) [36,264,3,96,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,130,128] 13 (by decide) (choices 1) [1,16] r26172 c26172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9334
  · exact u9335

def b26173 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 104 208 33 210 146 402), lower := (rows 37 266 7 104 208 33 64 128 256), losses := [] }

theorem u26173 : Upper (D 7) (R 7) [36,264,3,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26174 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 104 208 34 209 145 401), lower := (rows 37 266 7 104 208 34 64 128 256), losses := [] }

theorem u26174 : Upper (D 7) (R 7) [36,264,3,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26175 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 266 7 104 208 48 195 131 387), lower := (rows 37 266 7 104 208 48 64 128 256), losses := [] }

theorem u26175 : Upper (D 7) (R 7) [36,264,3,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26175 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26176 : Route 9 := (fun mask => (mask,id))

def c26176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26176 : Upper (D 7) (R 7) [36,264,3,96,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,192,128] 13 (by decide) (choices 1) [1,2,16] r26176 c26176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9336
  · exact u9337
  · exact u9338

def b26177 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 200 81 34 240 176 432), lower := (rows 37 266 7 200 81 34 64 128 256), losses := [] }

theorem u26177 : Upper (D 7) (R 7) [36,264,3,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26178 : Route 9 := (fun mask => (mask,id))

def c26178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26178 : Upper (D 7) (R 7) [36,264,3,192,65,16] 13 := by
  apply FastRouting.sound _ _ [36,264,3,192,65,16] 13 (by decide) (choices 1) [2,32,128] r26178 c26178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9339
  · exact u9340
  · exact u9341

def b26179 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 266 7 200 81 160 114 178 306), lower := (rows 37 266 7 200 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 303 7 168 17 160 0 160 256) }] }

theorem u26179 : Upper (D 7) (R 7) [36,264,3,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26180 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 200 82 33 240 176 432), lower := (rows 37 266 7 200 82 33 64 128 256), losses := [] }

theorem u26180 : Upper (D 7) (R 7) [36,264,3,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26181 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 266 7 200 82 48 225 161 417), lower := (rows 37 266 7 200 82 48 64 128 256), losses := [] }

theorem u26181 : Upper (D 7) (R 7) [36,264,3,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26181 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26182 : Route 9 := (fun mask => (mask,id))

def c26182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26182 : Upper (D 7) (R 7) [36,264,3,192,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,192,66,128] 13 (by decide) (choices 1) [1,16,32] r26182 c26182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9342
  · exact u9343
  · exact u9344

def b26183 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 200 112 33 210 146 402), lower := (rows 37 266 7 200 112 33 64 128 256), losses := [] }

theorem u26183 : Upper (D 7) (R 7) [36,264,3,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26184 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 200 112 34 209 145 401), lower := (rows 37 266 7 200 112 34 64 128 256), losses := [] }

theorem u26184 : Upper (D 7) (R 7) [36,264,3,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26185 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 7 200 112 48 195 131 387), lower := (rows 37 266 7 200 112 48 64 128 256), losses := [] }

theorem u26185 : Upper (D 7) (R 7) [36,264,3,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26185 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26186 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 37 266 7 200 112 160 83 147 275), lower := (rows 37 266 7 200 112 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 303 7 168 48 160 0 160 256) }] }

theorem u26186 : Upper (D 7) (R 7) [36,264,3,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26187 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 21 11 208 34 224 224 480), lower := (rows 37 266 21 11 208 34 64 128 256), losses := [] }

theorem u26187 : Upper (D 7) (R 7) [36,264,17,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26188 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 11 208 96 226 162 418), lower := (rows 37 266 21 11 208 96 64 128 256), losses := [] }

theorem u26188 : Upper (D 7) (R 7) [36,264,17,3,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26189 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 42 82 33 192 192 448), lower := (rows 37 266 21 42 82 33 64 128 256), losses := [] }

theorem u26189 : Upper (D 7) (R 7) [36,264,17,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26190 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 394, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 37 266 21 42 82 96 193 129 385), lower := (rows 37 266 21 42 82 96 64 128 256), losses := [] }

theorem u26190 : Upper (D 7) (R 7) [36,264,17,34,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26191 : Route 9 := (fun mask => (mask,id))

def c26191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26191 : Upper (D 7) (R 7) [36,264,17,34,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,17,34,66,128] 13 (by decide) (choices 1) [1,128] r26191 c26191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9345
  · exact u9346

def b26192 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 42 208 33 194 194 450), lower := (rows 37 266 21 42 208 33 64 128 256), losses := [] }

theorem u26192 : Upper (D 7) (R 7) [36,264,17,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26193 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 266 21 42 208 34 193 193 449), lower := (rows 37 266 21 42 208 34 64 128 256), losses := [] }

theorem u26193 : Upper (D 7) (R 7) [36,264,17,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26194 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 42 208 96 195 131 387), lower := (rows 37 266 21 42 208 96 64 128 256), losses := [] }

theorem u26194 : Upper (D 7) (R 7) [36,264,17,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26195 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 73 146 34 224 224 480), lower := (rows 37 266 21 73 146 34 64 128 256), losses := [] }

theorem u26195 : Upper (D 7) (R 7) [36,264,17,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26196 : Route 9 := (fun mask => (mask,id))

def c26196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26196 : Upper (D 7) (R 7) [36,264,17,65,130,64] 13 := by
  apply FastRouting.sound _ _ [36,264,17,65,130,64] 13 (by decide) (choices 1) [2,32,128] r26196 c26196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9347
  · exact u9348
  · exact u9349

def b26197 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 266 21 73 146 160 98 226 354), lower := (rows 37 266 21 73 146 160 64 128 256), losses := [] }

theorem u26197 : Upper (D 7) (R 7) [36,264,17,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26198 : Route 9 := (fun mask => (mask,id))

def c26198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26198 : Upper (D 7) (R 7) [36,264,17,65,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,17,65,192,2] 13 (by decide) (choices 1) [2,32,128] r26198 c26198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9350
  · exact u9351
  · exact u9352

def b26199 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 37 266 21 73 208 160 98 162 290), lower := (rows 37 266 21 73 208 160 64 128 256), losses := [] }

theorem u26199 : Upper (D 7) (R 7) [36,264,17,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26200 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 74 146 33 224 224 480), lower := (rows 37 266 21 74 146 33 64 128 256), losses := [] }

theorem u26200 : Upper (D 7) (R 7) [36,264,17,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26201 : Route 9 := (fun mask => (mask,id))

def c26201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26201 : Upper (D 7) (R 7) [36,264,17,66,130,64] 13 := by
  apply FastRouting.sound _ _ [36,264,17,66,130,64] 13 (by decide) (choices 1) [1,32,128] r26201 c26201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9353
  · exact u9354
  · exact u9355

def b26202 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 266 21 74 146 160 97 225 353), lower := (rows 37 266 21 74 146 160 64 128 256), losses := [] }

theorem u26202 : Upper (D 7) (R 7) [36,264,17,66,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26203 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 74 208 33 226 162 418), lower := (rows 37 266 21 74 208 33 64 128 256), losses := [] }

theorem u26203 : Upper (D 7) (R 7) [36,264,17,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26204 : Route 9 := (fun mask => (mask,id))

def c26204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26204 : Upper (D 7) (R 7) [36,264,17,66,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,17,66,192,2] 13 (by decide) (choices 1) [1,32,128] r26204 c26204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9356
  · exact u9357
  · exact u9358

def b26205 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 266 21 74 208 160 99 163 291), lower := (rows 37 266 21 74 208 160 64 128 256), losses := [] }

theorem u26205 : Upper (D 7) (R 7) [36,264,17,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26206 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 104 82 33 194 130 386), lower := (rows 37 266 21 104 82 33 64 128 256), losses := [] }

theorem u26206 : Upper (D 7) (R 7) [36,264,17,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26207 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 37 266 21 104 82 34 193 129 385), lower := (rows 37 266 21 104 82 34 64 128 256), losses := [] }

theorem u26207 : Upper (D 7) (R 7) [36,264,17,96,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26208 : Route 9 := (fun mask => (mask,id))

def c26208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26208 : Upper (D 7) (R 7) [36,264,17,96,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,17,96,66,128] 13 (by decide) (choices 1) [1,2,128] r26208 c26208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9359
  · exact u9360
  · exact u9361

def b26209 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 104 146 33 194 194 450), lower := (rows 37 266 21 104 146 33 64 128 256), losses := [] }

theorem u26209 : Upper (D 7) (R 7) [36,264,17,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26210 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 104 146 34 193 193 449), lower := (rows 37 266 21 104 146 34 64 128 256), losses := [] }

theorem u26210 : Upper (D 7) (R 7) [36,264,17,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26211 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 37 266 21 104 146 96 195 131 387), lower := (rows 37 266 21 104 146 96 64 128 256), losses := [] }

theorem u26211 : Upper (D 7) (R 7) [36,264,17,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26212 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 266 21 104 146 160 67 195 323), lower := (rows 37 266 21 104 146 160 64 128 256), losses := [] }

theorem u26212 : Upper (D 7) (R 7) [36,264,17,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26213 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 104 208 33 194 130 386), lower := (rows 37 266 21 104 208 33 64 128 256), losses := [] }

theorem u26213 : Upper (D 7) (R 7) [36,264,17,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26214 : Route 9 := (fun mask => (mask,id))

def c26214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26214 : Upper (D 7) (R 7) [36,264,17,96,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,17,96,192,2] 13 (by decide) (choices 1) [1,2,128] r26214 c26214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9362
  · exact u9363
  · exact u9364

def b26215 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 37 266 21 104 208 160 67 131 259), lower := (rows 37 266 21 104 208 160 64 128 256), losses := [] }

theorem u26215 : Upper (D 7) (R 7) [36,264,17,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26216 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 200 82 33 226 162 418), lower := (rows 37 266 21 200 82 33 64 128 256), losses := [] }

theorem u26216 : Upper (D 7) (R 7) [36,264,17,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26217 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 200 82 34 225 161 417), lower := (rows 37 266 21 200 82 34 64 128 256), losses := [] }

theorem u26217 : Upper (D 7) (R 7) [36,264,17,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26218 : Route 9 := (fun mask => (mask,id))

def c26218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26218 : Upper (D 7) (R 7) [36,264,17,192,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,17,192,66,128] 13 (by decide) (choices 1) [1,2,32] r26218 c26218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9365
  · exact u9366
  · exact u9367

def b26219 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 22 11 81 96 224 160 416), lower := (rows 37 266 22 11 81 96 64 128 256), losses := [] }

theorem u26219 : Upper (D 7) (R 7) [36,264,18,3,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26219
end Delivery.IrregularNine14.P07
