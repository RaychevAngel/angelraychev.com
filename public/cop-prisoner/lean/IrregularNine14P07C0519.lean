import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0225
import IrregularNine14P07C0226

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31140 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 261 200 208 51 115 179 307), lower := (rows 7 42 261 200 208 32 64 128 256), losses := [] }

theorem u31140 : Upper (D 7) (R 7) [6,40,257,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31141 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 276 73 19 224 224 224 480), lower := (rows 7 42 276 73 19 32 64 128 256), losses := [] }

theorem u31141 : Upper (D 7) (R 7) [6,40,272,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31142 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(3,5)], upper := (rows 7 42 276 73 49 226 194 194 450), lower := (rows 7 42 276 73 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 276 490 500 32 64 128 256) },{ target := 5, region := (rows 1 2 20 25 16 0 67 131 259), good := (rows 463 458 284 457 477 0 64 128 256) }] }

theorem u31142 : Upper (D 7) (R 7) [6,40,272,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31143 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 276 73 50 225 193 193 449), lower := (rows 7 42 276 73 50 32 64 128 256), losses := [] }

theorem u31143 : Upper (D 7) (R 7) [6,40,272,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31144 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 276 73 81 162 226 162 418), lower := (rows 7 42 276 73 81 32 64 128 256), losses := [] }

theorem u31144 : Upper (D 7) (R 7) [6,40,272,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31145 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 232, targets := 2 },{ cop := 3, region := 162, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 7 42 276 73 82 161 225 161 417), lower := (rows 7 42 276 73 82 32 64 128 256), losses := [] }

theorem u31145 : Upper (D 7) (R 7) [6,40,272,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31146 : Route 9 := (fun mask => (mask,id))

def c31146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31146 : Upper (D 7) (R 7) [6,40,272,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,96] 13 (by decide) (choices 1) [1,2,128] r31146 c31146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13508
  · exact u13509
  · exact u13510

def r31147 : Route 9 := (fun mask => (mask,id))

def c31147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31147 : Upper (D 7) (R 7) [6,40,272,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,129] 13 (by decide) (choices 1) [2,64,128] r31147 c31147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13511
  · exact u13512
  · exact u13513

def r31148 : Route 9 := (fun mask => (mask,id))

def c31148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31148 : Upper (D 7) (R 7) [6,40,272,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,130] 13 (by decide) (choices 1) [1,64,128] r31148 c31148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13514
  · exact u13515
  · exact u13516

def r31149 : Route 9 := (fun mask => (mask,id))

def c31149 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31149 : Upper (D 7) (R 7) [6,40,272,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,160] 13 (by decide) (choices 1) [1,2,64,128] r31149 c31149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13517
  · exact u13518
  · exact u13519
  · exact u13520

def r31150 : Route 9 := (fun mask => (mask,id))

def c31150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31150 : Upper (D 7) (R 7) [6,40,272,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,192] 13 (by decide) (choices 1) [1,2,128] r31150 c31150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13521
  · exact u13522
  · exact u13523

def b31151 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 },{ cop := 4, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,5),(4,1)], upper := (rows 7 42 276 74 49 225 193 193 449), lower := (rows 7 42 276 74 49 32 64 128 256), losses := [] }

theorem u31151 : Upper (D 7) (R 7) [6,40,272,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31152 : Route 9 := (fun mask => (mask,id))

def c31152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31152 : Upper (D 7) (R 7) [6,40,272,66,65] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,65] 13 (by decide) (choices 1) [1,128] r31152 c31152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13524
  · exact u13525

def b31153 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 276 74 112 161 193 129 385), lower := (rows 7 42 276 74 112 32 64 128 256), losses := [] }

theorem u31153 : Upper (D 7) (R 7) [6,40,272,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31154 : Route 9 := (fun mask => (mask,id))

def c31154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31154 : Upper (D 7) (R 7) [6,40,272,66,129] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,129] 13 (by decide) (choices 1) [1,64,128] r31154 c31154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13526
  · exact u13527
  · exact u13528

def r31155 : Route 9 := (fun mask => (mask,id))

def c31155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31155 : Upper (D 7) (R 7) [6,40,272,66,160] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,160] 13 (by decide) (choices 1) [1,64,128] r31155 c31155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13529
  · exact u13530
  · exact u13531

def r31156 : Route 9 := (fun mask => (mask,id))

def c31156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31156 : Upper (D 7) (R 7) [6,40,272,66,192] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,192] 13 (by decide) (choices 1) [1,128] r31156 c31156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13532
  · exact u13533

def b31157 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 276 200 19 225 225 225 481), lower := (rows 7 42 276 200 19 32 64 128 256), losses := [] }

theorem u31157 : Upper (D 7) (R 7) [6,40,272,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31158 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31158 : Upper (D 7) (R 7) [6,40,272,192,33] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,33] 13 (by decide) (choices 1) [1,2,64] r31158 c31158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13534
  · exact u13535
  · exact u13536

def b31159 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 276 200 50 225 193 193 449), lower := (rows 7 42 276 200 50 32 64 128 256), losses := [] }

theorem u31159 : Upper (D 7) (R 7) [6,40,272,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31160 : Route 9 := (fun mask => (mask,id))

def c31160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31160 : Upper (D 7) (R 7) [6,40,272,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,65] 13 (by decide) (choices 1) [1,2,128] r31160 c31160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13537
  · exact u13538
  · exact u13539

def r31161 : Route 9 := (fun mask => (mask,id))

def c31161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31161 : Upper (D 7) (R 7) [6,40,272,192,66] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,66] 13 (by decide) (choices 1) [1,128] r31161 c31161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13540
  · exact u13541

def r31162 : Route 9 := (fun mask => (mask,id))

def c31162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31162 : Upper (D 7) (R 7) [6,40,272,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,96] 13 (by decide) (choices 1) [1,2,128] r31162 c31162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13542
  · exact u13543
  · exact u13544

def b31163 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 276 200 208 35 99 163 291), lower := (rows 7 42 276 200 208 32 64 128 256), losses := [] }

theorem u31163 : Upper (D 7) (R 7) [6,40,272,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31164 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 27, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 42 292 25 19 224 192 192 448), lower := (rows 7 42 292 25 19 32 64 128 256), losses := [] }

theorem u31164 : Upper (D 7) (R 7) [6,40,288,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31165 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 292 25 81 226 194 194 450), lower := (rows 7 42 292 25 81 32 64 128 256), losses := [] }

theorem u31165 : Upper (D 7) (R 7) [6,40,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31166 : Route 9 := (fun mask => (mask,id))

def c31166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31166 : Upper (D 7) (R 7) [6,40,288,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17,66] 13 (by decide) (choices 1) [1,64,128] r31166 c31166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13545
  · exact u13546
  · exact u13547

def r31167 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31167 : Upper (D 7) (R 7) [6,40,288,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17,192] 13 (by decide) (choices 1) [1,2,64] r31167 c31167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13548
  · exact u13549
  · exact u13550

def b31168 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 292 73 19 240 208 208 464), lower := (rows 7 42 292 73 19 32 64 128 256), losses := [] }

theorem u31168 : Upper (D 7) (R 7) [6,40,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31169 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 292 73 81 178 210 146 402), lower := (rows 7 42 292 73 81 32 64 128 256), losses := [] }

theorem u31169 : Upper (D 7) (R 7) [6,40,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31170 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 292 73 82 177 209 145 401), lower := (rows 7 42 292 73 82 32 64 128 256), losses := [] }

theorem u31170 : Upper (D 7) (R 7) [6,40,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31171 : Route 9 := (fun mask => (mask,id))

def c31171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31171 : Upper (D 7) (R 7) [6,40,288,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,129] 13 (by decide) (choices 1) [2,16,64,128] r31171 c31171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13551
  · exact u13552
  · exact u13553
  · exact u13554

def r31172 : Route 9 := (fun mask => (mask,id))

def c31172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31172 : Upper (D 7) (R 7) [6,40,288,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,130] 13 (by decide) (choices 1) [1,16,64,128] r31172 c31172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13555
  · exact u13556
  · exact u13557
  · exact u13558

def r31173 : Route 9 := (fun mask => (mask,id))

def c31173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31173 : Upper (D 7) (R 7) [6,40,288,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,192] 13 (by decide) (choices 1) [1,2,16,128] r31173 c31173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13559
  · exact u13560
  · exact u13561
  · exact u13562

def b31174 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 292 88 19 225 193 193 449), lower := (rows 7 42 292 88 19 32 64 128 256), losses := [] }

theorem u31174 : Upper (D 7) (R 7) [6,40,288,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31175 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 292 88 81 163 195 131 387), lower := (rows 7 42 292 88 81 32 64 128 256), losses := [] }

theorem u31175 : Upper (D 7) (R 7) [6,40,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31176 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 292 88 82 161 193 129 385), lower := (rows 7 42 292 88 82 32 64 128 256), losses := [] }

theorem u31176 : Upper (D 7) (R 7) [6,40,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31177 : Route 9 := (fun mask => (mask,id))

def c31177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31177 : Upper (D 7) (R 7) [6,40,288,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80,129] 13 (by decide) (choices 1) [1,2,64,128] r31177 c31177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13563
  · exact u13564
  · exact u13565
  · exact u13566

def r31178 : Route 9 := (fun mask => (mask,id))

def c31178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31178 : Upper (D 7) (R 7) [6,40,288,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80,130] 13 (by decide) (choices 1) [1,64,128] r31178 c31178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13567
  · exact u13568
  · exact u13569

def b31179 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 292 88 208 163 195 131 387), lower := (rows 7 42 292 88 208 32 64 128 256), losses := [] }

theorem u31179 : Upper (D 7) (R 7) [6,40,288,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31180 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 292 200 19 241 209 209 465), lower := (rows 7 42 292 200 19 32 64 128 256), losses := [] }

theorem u31180 : Upper (D 7) (R 7) [6,40,288,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31181 : Route 9 := (fun mask => (mask,id))

def c31181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31181 : Upper (D 7) (R 7) [6,40,288,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,288,192,65] 13 (by decide) (choices 1) [1,2,16,128] r31181 c31181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13570
  · exact u13571
  · exact u13572
  · exact u13573

def b31182 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 292 200 82 177 209 145 401), lower := (rows 7 42 292 200 82 32 64 128 256), losses := [] }

theorem u31182 : Upper (D 7) (R 7) [6,40,288,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31183 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 292 200 208 51 83 147 275), lower := (rows 7 42 292 200 208 32 64 128 256), losses := [] }

theorem u31183 : Upper (D 7) (R 7) [6,40,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31184 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 42 324 25 19 224 224 224 480), lower := (rows 7 42 324 25 19 32 64 128 256), losses := [] }

theorem u31184 : Upper (D 7) (R 7) [6,40,320,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31185 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 324 25 49 226 194 194 450), lower := (rows 7 42 324 25 49 32 64 128 256), losses := [] }

theorem u31185 : Upper (D 7) (R 7) [6,40,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31186 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 324 25 50 225 193 193 449), lower := (rows 7 42 324 25 50 32 64 128 256), losses := [] }

theorem u31186 : Upper (D 7) (R 7) [6,40,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31187 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 324 25 81 162 226 162 418), lower := (rows 7 42 324 25 81 32 64 128 256), losses := [] }

theorem u31187 : Upper (D 7) (R 7) [6,40,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31188 : Route 9 := (fun mask => (mask,id))

def c31188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31188 : Upper (D 7) (R 7) [6,40,320,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,66] 13 (by decide) (choices 1) [1,128] r31188 c31188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13574
  · exact u13575

def r31189 : Route 9 := (fun mask => (mask,id))

def c31189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31189 : Upper (D 7) (R 7) [6,40,320,17,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,96] 13 (by decide) (choices 1) [1,2,128] r31189 c31189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13576
  · exact u13577
  · exact u13578

def b31190 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 324 25 145 226 226 226 482), lower := (rows 7 42 324 25 145 32 64 128 256), losses := [] }

theorem u31190 : Upper (D 7) (R 7) [6,40,320,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31191 : Route 9 := (fun mask => (mask,id))

def c31191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31191 : Upper (D 7) (R 7) [6,40,320,17,130] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,130] 13 (by decide) (choices 1) [1,64,128] r31191 c31191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13579
  · exact u13580
  · exact u13581

def r31192 : Route 9 := (fun mask => (mask,id))

def c31192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31192 : Upper (D 7) (R 7) [6,40,320,17,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,160] 13 (by decide) (choices 1) [1,2,64,128] r31192 c31192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13582
  · exact u13583
  · exact u13584
  · exact u13585

def r31193 : Route 9 := (fun mask => (mask,id))

def c31193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31193 : Upper (D 7) (R 7) [6,40,320,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,192] 13 (by decide) (choices 1) [1,2,128] r31193 c31193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13586
  · exact u13587
  · exact u13588

def b31194 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 324 26 49 225 193 193 449), lower := (rows 7 42 324 26 49 32 64 128 256), losses := [] }

theorem u31194 : Upper (D 7) (R 7) [6,40,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31195 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 324 26 81 161 225 161 417), lower := (rows 7 42 324 26 81 32 64 128 256), losses := [] }

theorem u31195 : Upper (D 7) (R 7) [6,40,320,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31196 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 324 26 112 161 193 129 385), lower := (rows 7 42 324 26 112 32 64 128 256), losses := [] }

theorem u31196 : Upper (D 7) (R 7) [6,40,320,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31197 : Route 9 := (fun mask => (mask,id))

def c31197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31197 : Upper (D 7) (R 7) [6,40,320,18,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,18,129] 13 (by decide) (choices 1) [1,64,128] r31197 c31197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13589
  · exact u13590
  · exact u13591

def b31198 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 324 26 176 225 193 193 449), lower := (rows 7 42 324 26 176 32 64 128 256), losses := [] }

theorem u31198 : Upper (D 7) (R 7) [6,40,320,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31199 : Route 9 := (fun mask => (mask,id))

def c31199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31199 : Upper (D 7) (R 7) [6,40,320,18,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,18,192] 13 (by decide) (choices 1) [1,128] r31199 c31199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13592
  · exact u13593

#print axioms u31199
end Delivery.IrregularNine14.P07
