import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0361
import IrregularNine14P07C0362
import IrregularNine14P07C0363

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36240 : Route 9 := (fun mask => (mask,id))

def c36240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36240 : Upper (D 7) (R 7) [34,320,9,132,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,160] 13 (by decide) (choices 1) [1,2,16,64] r36240 c36240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21690
  · exact u21691
  · exact u21692
  · exact u21693

def r36241 : Route 9 := (fun mask => (mask,id))

def c36241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36241 : Upper (D 7) (R 7) [34,320,9,132,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,192] 13 (by decide) (choices 1) [1,2,16] r36241 c36241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21694
  · exact u21695
  · exact u21696

def r36242 : Route 9 := (fun mask => (mask,id))

def c36242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36242 : Upper (D 7) (R 7) [34,320,9,144,6] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,6] 13 (by decide) (choices 1) [1,64,128] r36242 c36242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21697
  · exact u21698
  · exact u21699

def b36243 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 13 152 49 230 198 198 454), lower := (rows 35 322 13 152 49 32 64 128 256), losses := [] }

theorem u36243 : Upper (D 7) (R 7) [34,320,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36244 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 13 152 50 229 197 197 453), lower := (rows 35 322 13 152 50 32 64 128 256), losses := [] }

theorem u36244 : Upper (D 7) (R 7) [34,320,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36245 : Route 9 := (fun mask => (mask,id))

def c36245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36245 : Upper (D 7) (R 7) [34,320,9,144,36] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,36] 13 (by decide) (choices 1) [1,2,64,128] r36245 c36245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21700
  · exact u21701
  · exact u21702
  · exact u21703

def r36246 : Route 9 := (fun mask => (mask,id))

def c36246 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36246 : Upper (D 7) (R 7) [34,320,9,144,65] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,65] 13 (by decide) (choices 1) [2,4,128] r36246 c36246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21704
  · exact u21705
  · exact u21706

def b36247 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 13 152 82 165 229 165 421), lower := (rows 35 322 13 152 82 32 64 128 256), losses := [] }

theorem u36247 : Upper (D 7) (R 7) [34,320,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36248 : Route 9 := (fun mask => (mask,id))

def c36248 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36248 : Upper (D 7) (R 7) [34,320,9,144,68] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,68] 13 (by decide) (choices 1) [1,2,128] r36248 c36248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21707
  · exact u21708
  · exact u21709

def r36249 : Route 9 := (fun mask => (mask,id))

def c36249 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36249 : Upper (D 7) (R 7) [34,320,9,144,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,96] 13 (by decide) (choices 1) [1,2,4,128] r36249 c36249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21710
  · exact u21711
  · exact u21712
  · exact u21713

def b36250 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 35 322 13 152 145 102 102 230 358), lower := (rows 35 322 13 152 145 32 64 128 256), losses := [] }

theorem u36250 : Upper (D 7) (R 7) [34,320,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36251 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 13 152 146 101 101 229 357), lower := (rows 35 322 13 152 146 32 64 128 256), losses := [] }

theorem u36251 : Upper (D 7) (R 7) [34,320,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36252 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 13 152 148 99 99 227 355), lower := (rows 35 322 13 152 148 32 64 128 256), losses := [] }

theorem u36252 : Upper (D 7) (R 7) [34,320,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36253 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 13 152 176 103 71 199 327), lower := (rows 35 322 13 152 176 32 64 128 256), losses := [] }

theorem u36253 : Upper (D 7) (R 7) [34,320,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36254 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 13 152 208 39 103 167 295), lower := (rows 35 322 13 152 208 32 64 128 256), losses := [] }

theorem u36254 : Upper (D 7) (R 7) [34,320,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36255 : Route 9 := (fun mask => (mask,id))

def c36255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36255 : Upper (D 7) (R 7) [34,320,9,160,6] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,6] 13 (by decide) (choices 1) [1,16,64,128] r36255 c36255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21714
  · exact u21715
  · exact u21716
  · exact u21717

def r36256 : Route 9 := (fun mask => (mask,id))

def c36256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36256 : Upper (D 7) (R 7) [34,320,9,160,65] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,65] 13 (by decide) (choices 1) [2,4,16,128] r36256 c36256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21718
  · exact u21719
  · exact u21720
  · exact u21721

def b36257 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 13 168 82 181 213 149 405), lower := (rows 35 322 13 168 82 32 64 128 256), losses := [] }

theorem u36257 : Upper (D 7) (R 7) [34,320,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36258 : Route 9 := (fun mask => (mask,id))

def c36258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36258 : Upper (D 7) (R 7) [34,320,9,160,68] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,68] 13 (by decide) (choices 1) [1,2,16,128] r36258 c36258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21722
  · exact u21723
  · exact u21724
  · exact u21725

def r36259 : Route 9 := (fun mask => (mask,id))

def c36259 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36259 : Upper (D 7) (R 7) [34,320,9,160,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,129] 13 (by decide) (choices 1) [2,4,16,64] r36259 c36259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21726
  · exact u21727
  · exact u21728
  · exact u21729

def r36260 : Route 9 := (fun mask => (mask,id))

def c36260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36260 : Upper (D 7) (R 7) [34,320,9,160,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,130] 13 (by decide) (choices 1) [1,4,16,64] r36260 c36260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21730
  · exact u21731
  · exact u21732
  · exact u21733

def b36261 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 322 13 168 148 115 83 211 339), lower := (rows 35 322 13 168 148 32 64 128 256), losses := [] }

theorem u36261 : Upper (D 7) (R 7) [34,320,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36262 : Route 9 := (fun mask => (mask,id))

def c36262 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36262 : Upper (D 7) (R 7) [34,320,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,192] 13 (by decide) (choices 1) [1,2,4,16] r36262 c36262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21734
  · exact u21735
  · exact u21736
  · exact u21737

def r36263 : Route 9 := (fun mask => (mask,id))

def c36263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36263 : Upper (D 7) (R 7) [34,320,9,192,6] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,6] 13 (by decide) (choices 1) [1,16,128] r36263 c36263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21738
  · exact u21739
  · exact u21740

def b36264 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 13 200 49 182 214 150 406), lower := (rows 35 322 13 200 49 32 64 128 256), losses := [] }

theorem u36264 : Upper (D 7) (R 7) [34,320,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36265 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 13 200 50 181 213 149 405), lower := (rows 35 322 13 200 50 32 64 128 256), losses := [] }

theorem u36265 : Upper (D 7) (R 7) [34,320,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36266 : Route 9 := (fun mask => (mask,id))

def c36266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36266 : Upper (D 7) (R 7) [34,320,9,192,36] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,36] 13 (by decide) (choices 1) [1,2,16,128] r36266 c36266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21741
  · exact u21742
  · exact u21743
  · exact u21744

def r36267 : Route 9 := (fun mask => (mask,id))

def c36267 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36267 : Upper (D 7) (R 7) [34,320,9,192,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,129] 13 (by decide) (choices 1) [2,4,16] r36267 c36267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21745
  · exact u21746
  · exact u21747

def r36268 : Route 9 := (fun mask => (mask,id))

def c36268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36268 : Upper (D 7) (R 7) [34,320,9,192,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,130] 13 (by decide) (choices 1) [1,4,16] r36268 c36268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21748
  · exact u21749
  · exact u21750

def r36269 : Route 9 := (fun mask => (mask,id))

def c36269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36269 : Upper (D 7) (R 7) [34,320,9,192,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,132] 13 (by decide) (choices 1) [1,2,16] r36269 c36269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21751
  · exact u21752
  · exact u21753

def r36270 : Route 9 := (fun mask => (mask,id))

def c36270 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36270 : Upper (D 7) (R 7) [34,320,9,192,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,160] 13 (by decide) (choices 1) [1,2,4,16] r36270 c36270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21754
  · exact u21755
  · exact u21756
  · exact u21757

def b36271 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 28 49 225 193 193 449), lower := (rows 35 322 14 28 49 32 64 128 256), losses := [] }

theorem u36271 : Upper (D 7) (R 7) [34,320,10,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36272 : Route 9 := (fun mask => (mask,id))

def c36272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36272 : Upper (D 7) (R 7) [34,320,10,20,65] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,65] 13 (by decide) (choices 1) [1,128] r36272 c36272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21758
  · exact u21759

def r36273 : Route 9 := (fun mask => (mask,id))

def c36273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36273 : Upper (D 7) (R 7) [34,320,10,20,96] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,96] 13 (by decide) (choices 1) [1,128] r36273 c36273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21760
  · exact u21761

def r36274 : Route 9 := (fun mask => (mask,id))

def c36274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36274 : Upper (D 7) (R 7) [34,320,10,20,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,129] 13 (by decide) (choices 1) [1,64,128] r36274 c36274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21762
  · exact u21763
  · exact u21764

def r36275 : Route 9 := (fun mask => (mask,id))

def c36275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36275 : Upper (D 7) (R 7) [34,320,10,20,160] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,160] 13 (by decide) (choices 1) [1,64,128] r36275 c36275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21765
  · exact u21766
  · exact u21767

def r36276 : Route 9 := (fun mask => (mask,id))

def c36276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36276 : Upper (D 7) (R 7) [34,320,10,20,192] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,192] 13 (by decide) (choices 1) [1,128] r36276 c36276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21768
  · exact u21769

def b36277 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 41 81 180 212 148 404), lower := (rows 35 322 14 41 81 32 64 128 256), losses := [] }

theorem u36277 : Upper (D 7) (R 7) [34,320,10,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36278 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 41 84 177 209 145 401), lower := (rows 35 322 14 41 84 32 64 128 256), losses := [] }

theorem u36278 : Upper (D 7) (R 7) [34,320,10,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36279 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 41 145 244 212 212 468), lower := (rows 35 322 14 41 145 32 64 128 256), losses := [] }

theorem u36279 : Upper (D 7) (R 7) [34,320,10,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36280 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 41 148 241 209 209 465), lower := (rows 35 322 14 41 148 32 64 128 256), losses := [] }

theorem u36280 : Upper (D 7) (R 7) [34,320,10,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36281 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 41 208 181 213 149 405), lower := (rows 35 322 14 41 208 32 64 128 256), losses := [] }

theorem u36281 : Upper (D 7) (R 7) [34,320,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36282 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 44 81 177 209 145 401), lower := (rows 35 322 14 44 81 32 64 128 256), losses := [] }

theorem u36282 : Upper (D 7) (R 7) [34,320,10,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36283 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 44 145 241 209 209 465), lower := (rows 35 322 14 44 145 32 64 128 256), losses := [] }

theorem u36283 : Upper (D 7) (R 7) [34,320,10,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36284 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 14 44 208 177 209 145 401), lower := (rows 35 322 14 44 208 32 64 128 256), losses := [] }

theorem u36284 : Upper (D 7) (R 7) [34,320,10,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36285 : Route 9 := (fun mask => (mask,id))

def c36285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36285 : Upper (D 7) (R 7) [34,320,10,48,65] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,65] 13 (by decide) (choices 1) [1,4,128] r36285 c36285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21770
  · exact u21771
  · exact u21772

def r36286 : Route 9 := (fun mask => (mask,id))

def c36286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36286 : Upper (D 7) (R 7) [34,320,10,48,68] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,68] 13 (by decide) (choices 1) [1,128] r36286 c36286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21773
  · exact u21774

def r36287 : Route 9 := (fun mask => (mask,id))

def c36287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36287 : Upper (D 7) (R 7) [34,320,10,48,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,129] 13 (by decide) (choices 1) [1,4,64,128] r36287 c36287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21775
  · exact u21776
  · exact u21777
  · exact u21778

def r36288 : Route 9 := (fun mask => (mask,id))

def c36288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36288 : Upper (D 7) (R 7) [34,320,10,48,132] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,132] 13 (by decide) (choices 1) [1,64,128] r36288 c36288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21779
  · exact u21780
  · exact u21781

def r36289 : Route 9 := (fun mask => (mask,id))

def c36289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36289 : Upper (D 7) (R 7) [34,320,10,48,192] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,192] 13 (by decide) (choices 1) [1,4,128] r36289 c36289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21782
  · exact u21783
  · exact u21784

def b36290 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 14 73 49 180 212 148 404), lower := (rows 35 322 14 73 49 32 64 128 256), losses := [] }

theorem u36290 : Upper (D 7) (R 7) [34,320,10,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36291 : Route 9 := (fun mask => (mask,id))

def c36291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36291 : Upper (D 7) (R 7) [34,320,10,65,36] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,36] 13 (by decide) (choices 1) [1,16,128] r36291 c36291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21785
  · exact u21786
  · exact u21787

def r36292 : Route 9 := (fun mask => (mask,id))

def c36292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36292 : Upper (D 7) (R 7) [34,320,10,65,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,129] 13 (by decide) (choices 1) [4,16,128] r36292 c36292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21788
  · exact u21789
  · exact u21790

def r36293 : Route 9 := (fun mask => (mask,id))

def c36293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36293 : Upper (D 7) (R 7) [34,320,10,65,132] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,132] 13 (by decide) (choices 1) [1,16,128] r36293 c36293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21791
  · exact u21792
  · exact u21793

def r36294 : Route 9 := (fun mask => (mask,id))

def c36294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36294 : Upper (D 7) (R 7) [34,320,10,65,160] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,160] 13 (by decide) (choices 1) [1,4,16,128] r36294 c36294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21794
  · exact u21795
  · exact u21796
  · exact u21797

def b36295 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 322 14 76 145 177 241 177 433), lower := (rows 35 322 14 76 145 32 64 128 256), losses := [] }

theorem u36295 : Upper (D 7) (R 7) [34,320,10,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36296 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 322 14 76 176 177 209 145 401), lower := (rows 35 322 14 76 176 32 64 128 256), losses := [] }

theorem u36296 : Upper (D 7) (R 7) [34,320,10,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36297 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 14 88 49 165 197 133 389), lower := (rows 35 322 14 88 49 32 64 128 256), losses := [] }

theorem u36297 : Upper (D 7) (R 7) [34,320,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36298 : Route 9 := (fun mask => (mask,id))

def c36298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36298 : Upper (D 7) (R 7) [34,320,10,80,36] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,36] 13 (by decide) (choices 1) [1,128] r36298 c36298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21798
  · exact u21799

def r36299 : Route 9 := (fun mask => (mask,id))

def c36299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36299 : Upper (D 7) (R 7) [34,320,10,80,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,129] 13 (by decide) (choices 1) [1,4,128] r36299 c36299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21800
  · exact u21801
  · exact u21802

#print axioms u36299
end Delivery.IrregularNine14.P07
