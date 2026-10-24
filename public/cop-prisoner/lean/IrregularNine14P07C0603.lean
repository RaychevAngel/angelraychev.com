import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0359
import IrregularNine14P07C0360
import IrregularNine14P07C0361

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36180 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 44 146 241 209 209 465), lower := (rows 35 322 13 44 146 32 64 128 256), losses := [] }

theorem u36180 : Upper (D 7) (R 7) [34,320,9,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36181 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 44 208 179 211 147 403), lower := (rows 35 322 13 44 208 32 64 128 256), losses := [] }

theorem u36181 : Upper (D 7) (R 7) [34,320,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36182 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 56 22 225 193 193 449), lower := (rows 35 322 13 56 22 32 64 128 256), losses := [] }

theorem u36182 : Upper (D 7) (R 7) [34,320,9,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36183 : Route 9 := (fun mask => (mask,id))

def c36183 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36183 : Upper (D 7) (R 7) [34,320,9,48,65] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,65] 13 (by decide) (choices 1) [2,4,128] r36183 c36183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21591
  · exact u21592
  · exact u21593

def b36184 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 13 56 82 165 197 133 389), lower := (rows 35 322 13 56 82 32 64 128 256), losses := [] }

theorem u36184 : Upper (D 7) (R 7) [34,320,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36185 : Route 9 := (fun mask => (mask,id))

def c36185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36185 : Upper (D 7) (R 7) [34,320,9,48,68] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,68] 13 (by decide) (choices 1) [1,2,128] r36185 c36185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21594
  · exact u21595
  · exact u21596

def r36186 : Route 9 := (fun mask => (mask,id))

def c36186 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36186 : Upper (D 7) (R 7) [34,320,9,48,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,129] 13 (by decide) (choices 1) [2,4,64,128] r36186 c36186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21597
  · exact u21598
  · exact u21599
  · exact u21600

def r36187 : Route 9 := (fun mask => (mask,id))

def c36187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36187 : Upper (D 7) (R 7) [34,320,9,48,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,130] 13 (by decide) (choices 1) [1,4,64,128] r36187 c36187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21601
  · exact u21602
  · exact u21603
  · exact u21604

def r36188 : Route 9 := (fun mask => (mask,id))

def c36188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36188 : Upper (D 7) (R 7) [34,320,9,48,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,132] 13 (by decide) (choices 1) [1,2,64,128] r36188 c36188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21605
  · exact u21606
  · exact u21607
  · exact u21608

def r36189 : Route 9 := (fun mask => (mask,id))

def c36189 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36189 : Upper (D 7) (R 7) [34,320,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,192] 13 (by decide) (choices 1) [1,2,4,128] r36189 c36189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21609
  · exact u21610
  · exact u21611
  · exact u21612

def b36190 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 73 22 176 240 176 432), lower := (rows 35 322 13 73 22 32 64 128 256), losses := [] }

theorem u36190 : Upper (D 7) (R 7) [34,320,9,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36191 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 73 52 178 210 146 402), lower := (rows 35 322 13 73 52 32 64 128 256), losses := [] }

theorem u36191 : Upper (D 7) (R 7) [34,320,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36192 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 73 146 180 244 180 436), lower := (rows 35 322 13 73 146 32 64 128 256), losses := [] }

theorem u36192 : Upper (D 7) (R 7) [34,320,9,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36193 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 73 148 178 242 178 434), lower := (rows 35 322 13 73 148 32 64 128 256), losses := [] }

theorem u36193 : Upper (D 7) (R 7) [34,320,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36194 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 73 176 182 214 150 406), lower := (rows 35 322 13 73 176 32 64 128 256), losses := [] }

theorem u36194 : Upper (D 7) (R 7) [34,320,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36195 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 13 74 52 177 209 145 401), lower := (rows 35 322 13 74 52 32 64 128 256), losses := [] }

theorem u36195 : Upper (D 7) (R 7) [34,320,9,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36196 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 13 74 145 180 244 180 436), lower := (rows 35 322 13 74 145 32 64 128 256), losses := [] }

theorem u36196 : Upper (D 7) (R 7) [34,320,9,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36197 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 13 74 148 177 241 177 433), lower := (rows 35 322 13 74 148 32 64 128 256), losses := [] }

theorem u36197 : Upper (D 7) (R 7) [34,320,9,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36198 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 13 74 176 181 213 149 405), lower := (rows 35 322 13 74 176 32 64 128 256), losses := [] }

theorem u36198 : Upper (D 7) (R 7) [34,320,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36199 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 322 13 76 49 178 210 146 402), lower := (rows 35 322 13 76 49 32 64 128 256), losses := [] }

theorem u36199 : Upper (D 7) (R 7) [34,320,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36200 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 322 13 76 50 177 209 145 401), lower := (rows 35 322 13 76 50 32 64 128 256), losses := [] }

theorem u36200 : Upper (D 7) (R 7) [34,320,9,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36201 : Route 9 := (fun mask => (mask,id))

def c36201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36201 : Upper (D 7) (R 7) [34,320,9,68,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,68,129] 13 (by decide) (choices 1) [2,16,128] r36201 c36201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21613
  · exact u21614
  · exact u21615

def r36202 : Route 9 := (fun mask => (mask,id))

def c36202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36202 : Upper (D 7) (R 7) [34,320,9,68,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,68,130] 13 (by decide) (choices 1) [1,16,128] r36202 c36202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21616
  · exact u21617
  · exact u21618

def r36203 : Route 9 := (fun mask => (mask,id))

def c36203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36203 : Upper (D 7) (R 7) [34,320,9,68,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,68,160] 13 (by decide) (choices 1) [1,2,16,128] r36203 c36203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21619
  · exact u21620
  · exact u21621
  · exact u21622

def r36204 : Route 9 := (fun mask => (mask,id))

def c36204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36204 : Upper (D 7) (R 7) [34,320,9,80,6] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,6] 13 (by decide) (choices 1) [1,128] r36204 c36204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21623
  · exact u21624

def b36205 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 13 88 49 166 198 134 390), lower := (rows 35 322 13 88 49 32 64 128 256), losses := [] }

theorem u36205 : Upper (D 7) (R 7) [34,320,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36206 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 13 88 50 165 197 133 389), lower := (rows 35 322 13 88 50 32 64 128 256), losses := [] }

theorem u36206 : Upper (D 7) (R 7) [34,320,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36207 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(4,6)], upper := (rows 35 322 13 88 52 163 195 131 387), lower := (rows 35 322 13 88 52 32 64 128 256), losses := [{ target := 5, region := (rows 1 23 4 24 16 0 69 133 261), good := (rows 451 322 463 90 478 0 64 128 256) },{ target := 6, region := (rows 3 2 4 8 20 35 0 131 259), good := (rows 419 419 445 24 52 32 0 128 256) }] }

theorem u36207 : Upper (D 7) (R 7) [34,320,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36208 : Route 9 := (fun mask => (mask,id))

def c36208 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36208 : Upper (D 7) (R 7) [34,320,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,129] 13 (by decide) (choices 1) [2,4,128] r36208 c36208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21625
  · exact u21626
  · exact u21627

def r36209 : Route 9 := (fun mask => (mask,id))

def c36209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36209 : Upper (D 7) (R 7) [34,320,9,80,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,130] 13 (by decide) (choices 1) [1,4,128] r36209 c36209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21628
  · exact u21629
  · exact u21630

def r36210 : Route 9 := (fun mask => (mask,id))

def c36210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36210 : Upper (D 7) (R 7) [34,320,9,80,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,132] 13 (by decide) (choices 1) [1,2,128] r36210 c36210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21631
  · exact u21632
  · exact u21633

def r36211 : Route 9 := (fun mask => (mask,id))

def c36211 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36211 : Upper (D 7) (R 7) [34,320,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,160] 13 (by decide) (choices 1) [1,2,4,128] r36211 c36211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21634
  · exact u21635
  · exact u21636
  · exact u21637

def r36212 : Route 9 := (fun mask => (mask,id))

def c36212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36212 : Upper (D 7) (R 7) [34,320,9,96,6] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,6] 13 (by decide) (choices 1) [1,16,128] r36212 c36212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21638
  · exact u21639
  · exact u21640

def r36213 : Route 9 := (fun mask => (mask,id))

def c36213 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36213 : Upper (D 7) (R 7) [34,320,9,96,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,129] 13 (by decide) (choices 1) [2,4,16,128] r36213 c36213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21641
  · exact u21642
  · exact u21643
  · exact u21644

def r36214 : Route 9 := (fun mask => (mask,id))

def c36214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36214 : Upper (D 7) (R 7) [34,320,9,96,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,130] 13 (by decide) (choices 1) [1,4,16,128] r36214 c36214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21645
  · exact u21646
  · exact u21647
  · exact u21648

def r36215 : Route 9 := (fun mask => (mask,id))

def c36215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36215 : Upper (D 7) (R 7) [34,320,9,96,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,132] 13 (by decide) (choices 1) [1,2,16,128] r36215 c36215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21649
  · exact u21650
  · exact u21651
  · exact u21652

def b36216 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 22 240 240 240 496), lower := (rows 35 322 13 137 22 32 64 128 256), losses := [] }

theorem u36216 : Upper (D 7) (R 7) [34,320,9,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36217 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 52 242 210 210 466), lower := (rows 35 322 13 137 52 32 64 128 256), losses := [] }

theorem u36217 : Upper (D 7) (R 7) [34,320,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36218 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 84 178 242 178 434), lower := (rows 35 322 13 137 84 32 64 128 256), losses := [] }

theorem u36218 : Upper (D 7) (R 7) [34,320,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36219 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 112 182 214 150 406), lower := (rows 35 322 13 137 112 32 64 128 256), losses := [] }

theorem u36219 : Upper (D 7) (R 7) [34,320,9,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36220 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 146 116 116 244 372), lower := (rows 35 322 13 137 146 32 64 128 256), losses := [] }

theorem u36220 : Upper (D 7) (R 7) [34,320,9,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36221 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 35 322 13 137 148 114 114 242 370), lower := (rows 35 322 13 137 148 32 64 128 256), losses := [] }

theorem u36221 : Upper (D 7) (R 7) [34,320,9,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36222 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 176 118 86 214 342), lower := (rows 35 322 13 137 176 32 64 128 256), losses := [] }

theorem u36222 : Upper (D 7) (R 7) [34,320,9,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36223 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 137 208 54 118 182 310), lower := (rows 35 322 13 137 208 32 64 128 256), losses := [] }

theorem u36223 : Upper (D 7) (R 7) [34,320,9,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36224 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 13 138 49 244 212 212 468), lower := (rows 35 322 13 138 49 32 64 128 256), losses := [] }

theorem u36224 : Upper (D 7) (R 7) [34,320,9,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36225 : Route 9 := (fun mask => (mask,id))

def c36225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36225 : Upper (D 7) (R 7) [34,320,9,130,36] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,36] 13 (by decide) (choices 1) [1,16,64,128] r36225 c36225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21653
  · exact u21654
  · exact u21655
  · exact u21656

def r36226 : Route 9 := (fun mask => (mask,id))

def c36226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36226 : Upper (D 7) (R 7) [34,320,9,130,65] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,65] 13 (by decide) (choices 1) [4,16,128] r36226 c36226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21657
  · exact u21658
  · exact u21659

def r36227 : Route 9 := (fun mask => (mask,id))

def c36227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36227 : Upper (D 7) (R 7) [34,320,9,130,68] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,68] 13 (by decide) (choices 1) [1,16,128] r36227 c36227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21660
  · exact u21661
  · exact u21662

def r36228 : Route 9 := (fun mask => (mask,id))

def c36228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36228 : Upper (D 7) (R 7) [34,320,9,130,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,96] 13 (by decide) (choices 1) [1,4,16,128] r36228 c36228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21663
  · exact u21664
  · exact u21665
  · exact u21666

def r36229 : Route 9 := (fun mask => (mask,id))

def c36229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36229 : Upper (D 7) (R 7) [34,320,9,130,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,129] 13 (by decide) (choices 1) [4,16,64] r36229 c36229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21667
  · exact u21668
  · exact u21669

def r36230 : Route 9 := (fun mask => (mask,id))

def c36230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36230 : Upper (D 7) (R 7) [34,320,9,130,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,132] 13 (by decide) (choices 1) [1,16,64] r36230 c36230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21670
  · exact u21671
  · exact u21672

def r36231 : Route 9 := (fun mask => (mask,id))

def c36231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36231 : Upper (D 7) (R 7) [34,320,9,130,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,160] 13 (by decide) (choices 1) [1,4,16,64] r36231 c36231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21673
  · exact u21674
  · exact u21675
  · exact u21676

def r36232 : Route 9 := (fun mask => (mask,id))

def c36232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36232 : Upper (D 7) (R 7) [34,320,9,130,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,192] 13 (by decide) (choices 1) [1,4,16] r36232 c36232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21677
  · exact u21678
  · exact u21679

def b36233 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 13 140 49 242 210 210 466), lower := (rows 35 322 13 140 49 32 64 128 256), losses := [] }

theorem u36233 : Upper (D 7) (R 7) [34,320,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36234 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 13 140 50 241 209 209 465), lower := (rows 35 322 13 140 50 32 64 128 256), losses := [] }

theorem u36234 : Upper (D 7) (R 7) [34,320,9,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36235 : Route 9 := (fun mask => (mask,id))

def c36235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36235 : Upper (D 7) (R 7) [34,320,9,132,65] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,65] 13 (by decide) (choices 1) [2,16,128] r36235 c36235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21680
  · exact u21681
  · exact u21682

def b36236 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 13 140 82 177 241 177 433), lower := (rows 35 322 13 140 82 32 64 128 256), losses := [] }

theorem u36236 : Upper (D 7) (R 7) [34,320,9,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36237 : Route 9 := (fun mask => (mask,id))

def c36237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36237 : Upper (D 7) (R 7) [34,320,9,132,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,96] 13 (by decide) (choices 1) [1,2,16,128] r36237 c36237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21683
  · exact u21684
  · exact u21685
  · exact u21686

def b36238 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 35 322 13 140 145 114 114 242 370), lower := (rows 35 322 13 140 145 32 64 128 256), losses := [] }

theorem u36238 : Upper (D 7) (R 7) [34,320,9,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36239 : Route 9 := (fun mask => (mask,id))

def c36239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36239 : Upper (D 7) (R 7) [34,320,9,132,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,130] 13 (by decide) (choices 1) [1,16,64] r36239 c36239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21687
  · exact u21688
  · exact u21689

#print axioms u36239
end Delivery.IrregularNine14.P07
